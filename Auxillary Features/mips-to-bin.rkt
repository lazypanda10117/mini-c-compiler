#lang racket

; REQUIREMENTS
(require "Provided/scanning.rkt")


; GLOBAL CONSTANTS (and constant helper)
(define (max-base-2-number len) (sub1 (expt 2 len)))

(define WORD_BYTE_SIZE 4)
(define BYTE_SIZE 8)
(define WORD_LEN 32)

(define BASE_RADIX 2)

(define REGISTER_NUM 32)

(define REGISTER_LEN 5)
(define REGISTER_MIN 0)
(define REGISTER_MAX 31)

(define IMMEDIATE_LEN 16)
(define IMMEDIATE_SIGNED_MIN (- 0 (expt 2 15)))
(define IMMEDIATE_SIGNED_MAX (max-base-2-number 15))
(define UNSIGNED_IMMEDIATE_MIN 0)
(define UNSIGNED_IMMEDIATE_MAX (max-base-2-number 16))

(define UNSIGNED_MIN_INT 0)
(define UNSIGNED_MAX_INT (max-base-2-number 32))
(define MIN_SIGNED_INT (- 0 (expt 2 31)))
(define MAX_SIGNED_INT (max-base-2-number 31))


; CUSTOM STRUCTURES
(define-struct ntoken (type param))
(define-struct spair (label addr))


; GLOBAL MUTABLE VARIABLES
; Symbol table storing all the labels and their respective addresses
(define symbol-table (make-hash))
; Program index, which line is the assembler on
(define p-idx 0)
; The actual prettified program data we want without labels
(define token-super-list empty)


; Some utility functions
(define (in-list element lst)
  (ormap (lambda (e) (equal? e element)) lst))

(define (num-type-converter str)
  (match str
    [(regexp "^0x[0-9|a-f]+$") (string-append "#x" (substring str 2))] ; Assumption is that input will be of form 0x folowed by hex representation of number
    [(regexp "^(-)?[0-9]+$") str]
    [_ (begin (println str)
              (print-end "ERROR - Cannot convert number string to its corresponding type" (current-error-port)))]
    ))

; Symbol Table Functions
; Set ref in symbol table or throw error
(define (label-to-table label address)
  (if (hash-has-key? symbol-table label)
      (print-end "ERROR - Same label name already exists" (current-error-port))
      (hash-set! symbol-table label address)))

; Get ref from symbol table or throw error
(define (get-label-throw label)
  (if (hash-has-key? symbol-table label)
      (spair label (hash-ref symbol-table label))
      (print-end "ERROR - Label does not exist" (current-error-port))
      ))

; Output the whole symbol table to stderr
(define (throw-symbol-table)
  (for ([(label address) (in-hash symbol-table)])
    (fprintf (current-error-port) "~a ~a\n" label address)))


; Printing functions
; Print and exit function
(define (print-end str port)
  (begin (print str port) (exit)))
  ;(error 'ERROR str))


; Padding functions
; Generalized string padding function
(define (string-padder str len chr)
  ;(printf "string-padder: ~a  ~a" str chr)
  (define diff-len (- len (string-length str)))
  (define pad-str (make-string diff-len chr))    
  (if (> diff-len 0)
      (string-append pad-str str)
      str))

; Binary string (specific) padding function
(define (bin-padder neg num len)
  ;(printf "bin-padder: num ~a  neg ~a \n" num neg)
  (if (false? neg)
      (string-padder (number->string num BASE_RADIX) len #\1)
      (string-padder (number->string num BASE_RADIX) len #\0)
      ))


; nToken Functions
; token to nToken conversion
(define (decomposer tok)
  (match tok
    [(token type lex) (ntoken type lex)]
    [_ (print-end "ERROR - Failed to decompose token." (current-error-port))]
    ))

; nToken string to int conversion
(define (parse-to-int ntok)
  (match ntok
    [(ntoken 'HEXINT lex) (bin-verify (string-to-number (num-type-converter lex) 10) UNSIGNED_MIN_INT UNSIGNED_MAX_INT WORD_LEN)]
    [(ntoken 'INT lex) (bin-verify (string-to-number (num-type-converter lex) 10) MIN_SIGNED_INT UNSIGNED_MAX_INT WORD_LEN)]
    [_ (print-end "ERROR - Failed to parse integer." (current-error-port))]
  ))


; Binary String Functions
(define (string-to-number str radix)
  (define num (string->number str radix))
  (if (not (equal? num #f))
      num
      (print-end "ERROR - Failed to convert string to number" (current-error-port))))

(define (range-check num low high)
    (if (and (>= num low) (<= num high))
        num
        (print-end "ERROR - Number exceeds constraint." (current-error-port))
    ))

; Number to binary string conversion
(define (bin-verify num low high len)
  ;(printf "bin-verify: ~a  ~a  ~a  ~a" num low high len)
  (define (flip-neg num)
    (if (< num 0)
        (add1 (+ (max-base-2-number len) num))
        num))
  (begin
    ;(print (bin-padder (>= num 0) (flip-neg num) len))
    (bin-padder (>= num 0) (flip-neg (range-check num low high)) len)
    )
  )

; Building a binary string from a list of components
(define (build-bin-str lst)
  (foldr (lambda (a b) (string-append a b)) "" lst))

; Convert a binary string to actual binary code
(define (compile-command bstr)
  ;(println bstr)
  (define (compile-command-helper bin-str char-lst len)
    ; Conver a binary word (4 bits) to actual char
    (define (build-char str)
      (string-to-number (string-append "#b" str) 16))
    
    (if (< len WORD_LEN)
        (compile-command-helper (substring bin-str BYTE_SIZE)
                         (cons (build-char (substring bin-str 0 BYTE_SIZE)) char-lst)
                         (+ len BYTE_SIZE))
            (for-each (lambda (b) (write-byte b)) (reverse char-lst))))
  (compile-command-helper bstr empty 0))  



; First Pass (label builder)
; First pass token normalizer - Remove all labels and blank lines, then put the remaining tokens to super list
(define (normalize-token-list lst)  
  (define (normalize tokenList result [init #t])
    (if (empty? tokenList)
        result
        (match (car tokenList)
          [(token 'LABEL lex) (if init
                                  (normalize (cdr tokenList) result init)
                                  (print-end "ERROR - Label should not be in this index of the token list" (current-error-port)))]
          [(token 'WORD lex)
           (begin
             (parse-word-dfa (ntoken 'WORD (cdr tokenList)))
             (normalize (cdr tokenList) (cons (car tokenList) result) #f)
             )]                 
          [(token _ lex) (normalize (cdr tokenList) (cons (car tokenList) result) #f)]))
    )
  (define token-remains (reverse (normalize lst empty)))
  (if (empty? token-remains)
      (void)
      (set! token-super-list (cons token-remains token-super-list))))

; First pass symbol table builder
(define (label-builder tokenList)
  (define (trim-label label)
    (substring label 0 (sub1 (string-length label))))
  (if (not (empty? tokenList))
      (match (car tokenList)
        [(token 'LABEL lex)
         (begin
           (label-to-table (trim-label lex) p-idx)
           (label-builder (cdr tokenList))
           )]
        [(token _ lex) (set! p-idx (+ WORD_BYTE_SIZE p-idx))]
        )
      (void)))


; Second Pass (function/code builder and recursive matcher)
; Second Pass Individual Parsers
; Word parser
(define (parse-word-dfa ptok)
  (define tok-param-list
    (normalize-param-list (ntoken-param ptok) (list 'INT 'HEXINT 'ID)))

  (define (parse-word-dfa-2 lst result exp-lst)
    (if (empty? lst)
        (if (in-list 'END exp-lst)
            result
            (print-end "ERROR - Invalid termination state in WORD DFA" (current-error-port)))
        (if (in-list (ntoken-type (decomposer (car lst))) exp-lst)
            (match (car lst)
              [(token 'INT lex)
               (parse-word-dfa-2
                (cdr lst)
                (cons (decomposer (car lst)) result)
                (list' END))
               ]
              [(token 'HEXINT lex)
               (parse-word-dfa-2
                (cdr lst)
                (cons (decomposer (car lst)) result)
                (list' END))
               ]
              [(token 'ID lex)
               (parse-word-dfa-2
                (cdr lst)
                (cons (decomposer (car lst)) result)
                (list' END))
               ]
              [_ (print-end "ERROR - Failed to parse word subsequent token."
                            (current-error-port))])
              (print-end "ERROR - Invalid word structure in Word DFA" (current-error-port))
              )))
  (car (reverse
        (parse-word-dfa-2 tok-param-list empty (list 'INT 'HEXINT 'ID)))))

(define (parse-word ptok)
  ; This works because in the first pass, we already check for validity of word structure using Base structure DFA and Word DFA.
  ; Now, we are just converting those token with the ID tag into an INT ntoken with the corresponding address for the label
  (define (convert-label-to-addr tok)
    (if (equal? (ntoken-type tok) 'ID)
        (ntoken 'INT (number->string (spair-addr (get-label-throw (ntoken-param tok)))))
        tok))
  (compile-command (parse-to-int (convert-label-to-addr (parse-word-dfa ptok)))))


; Normalize parameter list
(define (normalize-param-list lst [init-state (list 'REG)])
  (define (normalize-param paramList result inparen exp-lst)
    (define (paren-fail e-lst)
      (if inparen
          (print-end "ERROR - Wrong parameter list structure" (current-error-port))
          (normalize-param (cdr paramList) (cons (car paramList) result) #f e-lst)
          ))
    (if (empty? paramList)
        (if (in-list 'END exp-lst)
            result
            (print-end "ERROR - Invalid termination state in Base Structure DFA" (current-error-port)))
        (if (not (in-list (ntoken-type (decomposer (car paramList))) exp-lst))
            (print-end "ERROR - Invalid parmeter list structure in Base Structure DFA" (current-error-port))
            (match (car paramList)
              ; not matching all edge cases i think, but 0v0 who cares ?
              [(token 'REG lex)
               (if inparen
                   (normalize-param (cdr paramList) (cons (car paramList) result) #f (list 'RPAREN))
                   (normalize-param (cdr paramList) (cons (car paramList) result) #f (list 'COMMA 'END))
                   )]
              [(token 'INT lex) (paren-fail (list 'LPAREN 'END))]
              [(token 'HEXINT lex) (paren-fail (list 'LPAREN 'END))]
              [(token 'ID lex) (paren-fail (list 'END))]
              [(token 'LPAREN lex) (normalize-param (cdr paramList) result #t (list 'REG))]
              [(token 'RPAREN lex) (normalize-param (cdr paramList) result #f (list 'END))]
              [(token 'COMMA lex) (normalize-param (cdr paramList) result #f (list 'REG 'INT 'HEXINT 'ID))]
              [_ (print-end "ERROR - Failed to normalize tokens in parameter list" (current-error-port))]))))
  (reverse (normalize-param lst empty #f init-state)))

; Transform a parameter list into a normalized list of essential nTokens of type ('REG or 'IMM)
(define (param-ntok-transform paramList)
  ; Transform token list into nToken list
  (define (pn-helper plst result)
    (if (empty? plst)
        result
        (match (car plst)
          [(token 'REG lex)
           (pn-helper (cdr plst)
                      (cons (ntoken 'REG (string-to-number (num-type-converter (substring lex 1)) 10)) result))]
          [(token 'INT lex)
           (pn-helper (cdr plst)
                      (cons (ntoken 'IMM (range-check 
                                           (string-to-number (num-type-converter lex) 10)
                                           IMMEDIATE_SIGNED_MIN 
                                           IMMEDIATE_SIGNED_MAX)) result))]
          [(token 'HEXINT lex)
           (pn-helper (cdr plst)
                      (cons (ntoken 'IMM (range-check 
                                           (string-to-number (num-type-converter lex) 10) 
                                            UNSIGNED_IMMEDIATE_MIN 
                                            UNSIGNED_IMMEDIATE_MAX)) result))]
          [(token 'ID lex)
           ; this is a particular case for label
           (pn-helper (cdr plst)
                      (cons (ntoken 'IMM
                                    (range-check 
                                        (/ (- (- (spair-addr (get-label-throw lex)) p-idx) 4) 4) 
                                        IMMEDIATE_SIGNED_MIN 
                                        IMMEDIATE_SIGNED_MAX)) result))]
          [_ (print-end "ERROR - Failed to transform parameter token into nToken" (current-error-port))])))
  
  (reverse (pn-helper (normalize-param-list paramList) empty)))

; Function parser (i.e. add, sub, lw, ...)
(define (parse-func ptok)
  ; Verify that parameters staisfy constraints (the formatting constraints) and implicitly check for boundary constraint in (bin-verify)
  (define (verifier par con)
    (define (verifier-helper param constraint result)
      ; param: nToken
      ; constraint: (list Type('REG or 'IMM) ...)
      (define (general-match ntok celement range-func)
        (if (equal? (ntoken-type  ntok) celement)
            (verifier-helper (cdr param) (cdr constraint)
                (cons (ntoken (ntoken-type ntok) (range-func (ntoken-param ntok))) result))
            (print-end "ERROR - Constraint types do not match." (current-error-port))))
    
      (if (empty? param)
          (if (empty? constraint)
              result
              (print-end "ERROR - Constraint count greater than parameter count."
                         (current-error-port)))
          (if (empty? constraint)
              (print-end "ERROR - Parameter count greater than constraint count."
                         (current-error-port))
              (match (car param)
                [(ntoken 'REG lex)
                 (general-match (car param) (car constraint)
                  (lambda (val) (bin-verify val REGISTER_MIN REGISTER_MAX REGISTER_LEN)))]
                [(ntoken 'IMM lex)
                 (begin
                   ;(printf "IMM ~a" lex)
                   (general-match (car param) (car constraint)
                                  (lambda (val) (bin-verify val IMMEDIATE_SIGNED_MIN UNSIGNED_IMMEDIATE_MAX IMMEDIATE_LEN))))]
                [_ (print-end "ERROR - Invalid nToken type on verification of parameters' constraints."
                         (current-error-port))]))))
    (reverse (verifier-helper par con empty)))

  ; Building the binary string according to format (like printf)
  (define (build-fun-bin format parameters)
    ; In the format list, "#" denotes a parameter
    (define (build-fun-bin-helper f result)
      (if (empty? f)
          (begin
            ;(print (string-join (reverse result) ""))
            (compile-command (string-join (reverse result) ""))
          )
          (if (equal? (string-ref (car f) 0) #\#)
              (build-fun-bin-helper
               (cdr f)
               (cons
                (ntoken-param (list-ref parameters (sub1 (string-to-number (substring (car f) 1) 10))))
                result))
              (build-fun-bin-helper
               (cdr f)
               (cons (car f) result)))))
    (build-fun-bin-helper format empty))
  
  (match ptok
    [(ntoken 'JR param)    
     (build-fun-bin (list "000000" "#1" "000000000000000001000") (verifier (param-ntok-transform param) (list 'REG)))
     ]   
    [(ntoken 'JALR param)
     (build-fun-bin (list "000000" "#1" "000000000000000001001") (verifier (param-ntok-transform param) (list 'REG)))
     ]
    [(ntoken 'ADD param)
     (build-fun-bin (list "000000" "#2" "#3" "#1" "00000100000") (verifier (param-ntok-transform param) (list 'REG 'REG 'REG)))
     ]
    [(ntoken 'SUB param)
     (build-fun-bin (list "000000" "#2" "#3" "#1" "00000100010") (verifier (param-ntok-transform param) (list 'REG 'REG 'REG)))
     ]
    [(ntoken 'SLT param)
     (build-fun-bin (list "000000" "#2" "#3" "#1" "00000101010") (verifier (param-ntok-transform param) (list 'REG 'REG 'REG)))
     ]
    [(ntoken 'SLTU param)
     (build-fun-bin (list "000000" "#2" "#3" "#1" "00000101011") (verifier (param-ntok-transform param) (list 'REG 'REG 'REG)))
     ]
    [(ntoken 'BEQ param)
     (build-fun-bin (list "000100" "#1" "#2" "#3") (verifier (param-ntok-transform param) (list 'REG 'REG 'IMM)))
     ]
    [(ntoken 'BNE param)
     (build-fun-bin (list "000101" "#1" "#2" "#3") (verifier (param-ntok-transform param) (list 'REG 'REG 'IMM)))
     ]
    [(ntoken 'LIS param)
     (build-fun-bin (list "0000000000000000" "#1" "00000010100") (verifier (param-ntok-transform param) (list 'REG)))
     ]
    [(ntoken 'MFLO param)
     (build-fun-bin (list "0000000000000000" "#1" "00000010010") (verifier (param-ntok-transform param) (list 'REG)))
     ]
    [(ntoken 'MFHI param)
     (build-fun-bin (list "0000000000000000" "#1" "00000010000") (verifier (param-ntok-transform param) (list 'REG)))
     ]
    [(ntoken 'MULT param)
     (build-fun-bin (list "000000" "#1" "#2" "0000000000011000") (verifier (param-ntok-transform param) (list 'REG 'REG)))
     ]
    [(ntoken 'MULTU param)
     (build-fun-bin (list "000000" "#1" "#2" "0000000000011001") (verifier (param-ntok-transform param) (list 'REG 'REG)))
     ]
    [(ntoken 'DIV param)
     (build-fun-bin (list "000000" "#1" "#2" "0000000000011010") (verifier (param-ntok-transform param) (list 'REG 'REG)))
     ]
    [(ntoken 'DIVU param)
     (build-fun-bin (list "000000" "#1" "#2" "0000000000011011") (verifier (param-ntok-transform param) (list 'REG 'REG)))
     ]
    [(ntoken 'SW param)
     (build-fun-bin (list "101011" "#3" "#1" "#2") (verifier (param-ntok-transform param) (list 'REG 'IMM 'REG)))
     ]
    [(ntoken 'LW param)
     (build-fun-bin (list "100011" "#3" "#1" "#2") (verifier (param-ntok-transform param) (list 'REG 'IMM 'REG)))
     ]
    [_ (print-end "ERROR - Failed to parse function subsequent token."
                  (current-error-port))]
    ))


; Second pass matcher
(define (matcher tokenList)
  ; Second pass function builder
  (define (fun-builder ntok)
    (match ntok
      [(ntoken (list 'WORD) param) (parse-word ntok)]
      [(ntoken _ param) (parse-func ntok)]
      [_ (print-end "ERROR - Failed to comprehend function building nToken." (current-error-port))]
      ))

  ; Function nToken builder from input
  (define (fun-ntok-builder type-str lst)
    (match type-str
      [(regexp "^jr$") (ntoken 'JR lst)]
      [(regexp "^jalr$") (ntoken 'JALR lst)]
      [(regexp "^add$") (ntoken 'ADD lst)]
      [(regexp "^sub$") (ntoken 'SUB lst)]
      [(regexp "^slt$") (ntoken 'SLT lst)]
      [(regexp "^sltu$") (ntoken 'SLTU lst)]
      [(regexp "^beq$") (ntoken 'BEQ lst)]
      [(regexp "^bne$") (ntoken 'BNE lst)]
      [(regexp "^lis$") (ntoken 'LIS lst)]
      [(regexp "^mflo$") (ntoken 'MFLO lst)]
      [(regexp "^mfhi$") (ntoken 'MFHI lst)]
      [(regexp "^mult$") (ntoken 'MULT lst)]
      [(regexp "^multu$") (ntoken 'MULTU lst)]
      [(regexp "^div$") (ntoken 'DIV lst)]
      [(regexp "^divu$") (ntoken 'DIVU lst)]
      [(regexp "^sw$") (ntoken 'SW lst)]
      [(regexp "^lw$") (ntoken 'LW lst)]
      [_ (print-end "ERROR - Failed to build function nToken due to invalid instruction type." (current-error-port))]
      ))
  
  (if (not (empty? tokenList))
      (match (car tokenList)
        [(token 'WORD lex) (fun-builder (ntoken (list 'WORD) (cdr tokenList)))]
        [(token 'ID lex) (fun-builder (fun-ntok-builder lex (cdr tokenList)))]
        [_ (print-end "ERROR - Failed to comprehend initial token." (current-error-port))])
      (void)
  ))


; THE MAIN ASSEMBLER FUNCTION
(define (assemble)
  (define (first-pass)
    (for [(line (in-lines))]
      (define tokenList (scan line))
      (label-builder tokenList)
      (normalize-token-list tokenList)
      )
    ; Reversing the list as it is put in reverse order during normalize function
    (set! token-super-list (reverse token-super-list))
    (set! p-idx 0))
  (define (second-pass token-lst)
    (if (empty? token-lst)
        (void)
        (begin
          (matcher (car token-lst))
          (set! p-idx (+ WORD_BYTE_SIZE p-idx))
          (second-pass (cdr token-lst)))))
  (first-pass)
  (second-pass token-super-list)
  (throw-symbol-table))


; Executing the assembler function
(assemble)
