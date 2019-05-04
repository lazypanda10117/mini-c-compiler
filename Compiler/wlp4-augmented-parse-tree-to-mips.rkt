#lang racket

(define terminal-symbols
  (list
   "BOF" "BECOMES" "COMMA" "ELSE" "EOF" "EQ" "GE" "GT"
   "ID" "IF" "INT" "LBRACE" "LE" "LPAREN" "LT" "MINUS"
   "NE" "NUM" "PCT" "PLUS" "PRINTLN" "RBRACE" "RETURN" "RPAREN"
   "SEMI" "SLASH" "STAR" "WAIN" "WHILE" "AMP" "LBRACK" "RBRACK"
   "NEW" "DELETE" "NULL"))

; Parse Tree Global Vars
(define-struct v-obj (val type) #:transparent)
(define-struct node (vobj lst) #:transparent)
(define parse-tree empty)

; Input Queue
(define input-queue empty)

; Hash Table for Declarations
(define func-sym-table (make-hash))
(define fast-func-sym-table (make-hash))

(define-struct dcl-type (type pointer) #:transparent)
(define-struct dcl-obj (type symbol) #:transparent)
(define-struct dcl-box (type offset) #:transparent)
(define-struct func-sign (name rtype params) #:transparent)
(define current-scope "")
(define derailed #f)

; Code Generation Variables
(define WORD_BYTE_SIZE 4)


; Some general utility functions
(define (in-list element lst)
  (ormap (lambda (e) (equal? e element)) lst))

(define (print-end str)
  (begin (displayln str (current-error-port)) (exit)))

(define (list-to-str lst)
  (define (lp-helper n l str)
    (if (empty? l)
        str
        (begin
          (if n
              (lp-helper #f (cdr l) (string-append str (car l)))
              (lp-helper #f (cdr l) (string-append str (string-append " "(car l))))))))
  (lp-helper #t lst ""))

(define (error-hash-ref table key)
  (if (hash-has-key? table key)
      (hash-ref table key)
      (begin
        (fprintf (current-error-port) "ERROR: Cannot reference key: ~a in hash table: ~a" key table)
        (exit))))

(define (error-hash-exist table key)
  (if (hash-has-key? table key)
          (begin
            (fprintf (current-error-port) "ERROR: Already has reference key: ~a in hash table: ~a" key table)
            (exit))
          #t))

(define (in-hash table key)
  (hash-has-key? table key))

(define (print-preorder tree)
  (displayln (v-obj-val (node-vobj tree)))
  (for [(subtree-node (node-lst tree))]
    (print-preorder subtree-node)))

(define (linear-merge source target [to-reverse #f])
  ; Linear Merge list Utility
  (define (merge-helper src tgt)
    (if (empty? src)
      tgt
      (merge-helper (cdr src) (cons (car src) tgt))))
  (merge-helper (if to-reverse (reverse source) source) target))


; Context-Sensitive Parser Specific Utilties Function
(define (get-value-str str)
  (cadr (string-split str)))

(define (get-root-str str)
  (car (string-split str)))

(define (skip-tree-node lst node-key)
  (if (empty? lst)
      lst
      (if (string=? (get-root-str (v-obj-val (node-vobj (car lst)))) node-key)
          (cdr lst)
          (skip-tree-node (cdr lst) node-key))))

(define (error-hash-has-dcl table dcl)
  (define normal-dcl dcl)
  (define normal-neg-ptr-dcl
    (dcl-obj
     (dcl-type
      (dcl-type-type (dcl-obj-type dcl))
      (not (dcl-type-pointer (dcl-obj-type dcl))))
     (dcl-obj-symbol dcl)))
  (begin
    (error-hash-exist table normal-dcl)
    (error-hash-exist table normal-neg-ptr-dcl)))

(define (error-hash-has-no-dcl table id)
  (define has-dcl (hash-has-key? table id))
  (if has-dcl
      #t
      (fprintf (current-error-port) "ERROR: Declaration: ~a has not been defined in table: ~a" id table)))

(define (dcl-type-conversion d-type)
  (cond
    [(dcl-type-pointer d-type) (string-append (dcl-type-type d-type) "*")]
    [else (dcl-type-type d-type)]))


; Context-Sensitive Parser Helper Functions
(define (generate-input-queue)
  (for [(line (in-lines))]
    (set! input-queue (cons line input-queue)))
  (set! input-queue (reverse input-queue)))

(define (generate-parse-tree)
  (define (reverse-parse-tree)
    (define line (car input-queue))
    (define element-list (string-split line))
    (define derivation-root (car element-list))
    (define useful-elements (cdr element-list))
    (set! input-queue (cdr input-queue))
    (define (build-elements elements lst)
      (if (empty? elements)
          (reverse lst)
          (build-elements (cdr elements) (cons (reverse-parse-tree) lst))
          ))
    (cond
      [(in-list derivation-root terminal-symbols) (node (v-obj line 'NULL) empty)]
      [else (node (v-obj line 'NULL) (build-elements useful-elements empty))]
      ))
  (define non-typed-parse-tree (reverse-parse-tree))
  (set! parse-tree non-typed-parse-tree))

(define (build-typed-parse-tree)
  (define (generate-typed-parse-tree tree)
    (define (build-typed-list tree-lst result)
      (if (empty? tree-lst)
          (reverse result)
          (build-typed-list
           (cdr tree-lst)
           (cons (generate-typed-parse-tree (car tree-lst)) result))))
    (node
     (v-obj (v-obj-val (node-vobj tree)) (get-node-type tree))
     (build-typed-list (node-lst tree) empty)))
  (set! parse-tree (generate-typed-parse-tree parse-tree)))

(define type-scope "")

(define (get-node-type tree)
  (define nlst (node-lst tree))
  (define line-tokens (string-split (v-obj-val (node-vobj tree))))
  ;(println (node-vobj tree))
  (match line-tokens
    [(list "ID" _)
     (define id-dcl-box (hash-ref
                         (hash-ref fast-func-sym-table type-scope)
                         (list-ref line-tokens 1)
                         (dcl-box "Random Filler Value" "Type undefined for function ID")))
     (match (dcl-box-type id-dcl-box)
       [(dcl-type "int" #t) 'INTPTR]
       [(dcl-type "int" #f) 'INT]
       [_ 'UNKNOWN]
       )
     ]
    [(list "NULL" "NULL") 'INTPTR]
    [(list "NUM" _) 'INT]
    [(list "factor" "ID") (get-node-type (list-ref nlst 0))]
    [(list "factor" "NUM") (get-node-type (list-ref nlst 0))]
    [(list "factor" "NULL") (get-node-type (list-ref nlst 0))]
    [(list "LPAREN" "expr" "RPAREN") (get-node-type (list-ref nlst 1))]
    [(list "expr" "term") (get-node-type (list-ref nlst 0))]
    [(list "term" "factor") (get-node-type (list-ref nlst 0))]
    [(list "lvalue" "ID") (get-node-type (list-ref nlst 0))]
    [(list "factor" "STAR" "factor")
     (if (equal? (get-node-type (list-ref nlst 1)) 'INTPTR)
         'INT
         (print-end "ERROR: Type Checking in factor STAR factor"))]
    [(list "factor" "AMP" "lvalue")
     (if (equal? (get-node-type (list-ref nlst 1)) 'INT)
         'INTPTR
         (print-end "ERROR: Type Checking in factor AMP lvalue"))]
    [(list "lvalue" "LPAREN" "lvalue" "RPAREN") (get-node-type (list-ref nlst 1))]
    [(list "lvalue" "STAR" "factor")
     (if (equal? (get-node-type (list-ref nlst 1)) 'INTPTR)
         'INT
         (print-end "ERROR: Type Checking in lvalue STAR factor"))]
    [(list "factor" "NEW" "INT" "LBRACK" "expr" "RBRACK")
     (if (equal? (get-node-type (list-ref nlst 3)) 'INT)
         'INTPTR
         (print-end "ERROR: Type Checking in factor NEW INT LBRACK expr RBRACK
"))]
    [(list "expr" "expr" "PLUS" "term")
     (define p-list (list
                     (get-node-type (list-ref nlst 0))
                     (get-node-type (list-ref nlst 2))))
     (match p-list
       [(list 'INT 'INT) 'INT]
       [(list 'INT 'INTPTR) 'INTPTR]
       [(list 'INTPTR 'INT) 'INTPTR]
       [_ (print-end "ERROR: Type Checking in expr expr PLUS term")])
     ]
    [(list "expr" "expr" "MINUS" "term")
     (define p-list (list
                     (get-node-type (list-ref nlst 0))
                     (get-node-type (list-ref nlst 2))))
     (match p-list
       [(list 'INT 'INT) 'INT]
       [(list 'INTPTR 'INT) 'INTPTR]
       [(list 'INTPTR 'INTPTR) 'INT]
       [_ (print-end "ERROR: Type Checking in expr expr MINUS term")])
     ]
    [(list "term" "term" "STAR" "factor")
     (define p-list (list
                     (get-node-type (list-ref nlst 0))
                     (get-node-type (list-ref nlst 2))))
     (match p-list
       [(list 'INT 'INT) 'INT]
       [_ (print-end "ERROR: Type Checking in term term STAR factor")])
     ]
    [(list "term" "term" "SLASH" "factor")
     (define p-list (list
                     (get-node-type (list-ref nlst 0))
                     (get-node-type (list-ref nlst 2))))
     (match p-list
       [(list 'INT 'INT) 'INT]
       [_ (print-end "ERROR: Type Checking in term term SLASH factor")])
     ]
    [(list "term" "term" "PCT" "factor")     
     (define p-list (list
                     (get-node-type (list-ref nlst 0))
                     (get-node-type (list-ref nlst 2))))
     (match p-list
       [(list 'INT 'INT) 'INT]
       [_ (print-end "ERROR: Type Checking in term term PCT factor")])
     ]
    [(list "factor" "LPAREN" "expr" "RPAREN")
     (get-node-type (list-ref nlst 1))]
    [(list "factor" "ID" "LPAREN" "RPAREN") 'INT]
    [(list "factor" "ID" "LPAREN" "arglist" "RPAREN")
     (get-node-type (list-ref nlst 2))]
    [(list "arglist" "expr") 'INT]
    [(list "arglist" "expr" "COMMA" "arglist") 'INT]
    [(list "procedure" "INT" "ID" "LPAREN" "params" "RPAREN"
     "LBRACE" "dcls" "statements" "RETURN" "expr" "SEMI" "RBRACE")
     (set! type-scope (get-value-str (v-obj-val (node-vobj (list-ref nlst 1)))))
     'NULL
     ]
    [(list "main" "INT" "WAIN" "LPAREN" "dcl" "COMMA" "dcl" "RPAREN"
           "LBRACE" "dcls" "statements" "RETURN" "expr" "SEMI" "RBRACE")
     (set! type-scope (get-value-str (v-obj-val (node-vobj (list-ref nlst 1)))))
     'NULL
     ]
    [_ 'NULL]
    ))

(define (output-sym-table)
  (define print-first #f)
  (for [((func d-table) func-sym-table)]
    (if print-first
        (displayln "" (current-error-port))
        (set! print-first #t))
    (define function-param-types 
         (map
          (lambda (d-type) (dcl-type-conversion d-type))
          (func-sign-params func)))
    (define function-signature
      (list-to-str (cons (func-sign-name func) function-param-types)))
    (displayln function-signature (current-error-port))
    (for [((d-obj val) d-table)]
      (define output-str 
        (string-append
         (dcl-obj-symbol d-obj)
         (string-append " " (dcl-type-conversion (dcl-obj-type d-obj)))))
      (displayln output-str (current-error-port)))))


; DCL list parser
(define (parse-dcl-list dcl-list result)
  (define (dcl-parse dcl-tree)
    (define tree-lst (node-lst dcl-tree))
    (define d-type (car tree-lst))
    (define d-id (cadr tree-lst))
    (define type (dcl-type
                  (get-value-str (v-obj-val (node-vobj (car (node-lst d-type)))))
                  ((lambda (pointer)
                     (cond
                       [(empty? pointer) #f]
                       [(equal? (get-root-str (v-obj-val (node-vobj (car pointer)))) "STAR") #t]
                       [else
                        (print-end "ERROR: Should not have anything else in DCL other than empty or *")
                        ]))
                  (cdr (node-lst d-type)))))
    (define value (get-value-str (v-obj-val (node-vobj d-id))))
    (dcl-obj type value))
  
  (if (empty? dcl-list)
      result
      (parse-dcl-list
       (cdr dcl-list)
       (cons (dcl-parse (car dcl-list)) result))))

; Function Param Parser
(define (parse-param tree-lst type)
  (define (parse-param-procedure tlst)
    (define params-tree (car (skip-tree-node tlst "LPAREN")))
    (define dcl-list (extract-dcl-from-tree params-tree))
    (parse-dcl-list dcl-list empty))
  (define (parse-param-main tlst)
    (define dcl1 (car (skip-tree-node tlst "LPAREN")))
    (define dcl2 (car (skip-tree-node tlst "COMMA")))
    (define dcl-list (reverse (list dcl1 dcl2)))
    (parse-dcl-list dcl-list empty))
  (cond
    [(equal? type "main") (parse-param-main tree-lst)]
    [(equal? type "procedure") (parse-param-procedure tree-lst)]
    [else (print-end "ERROR: Should not be in parse parameter function")]
  ))

; Extract DCL objects as list from a tree node
(define (extract-dcl-from-tree t)
  (define dcl-list empty)
  (define (extract-helper tree)
      (cond
        [(equal? (get-root-str (v-obj-val (node-vobj tree))) "dcl")
         (set! dcl-list (cons tree dcl-list))]
        [else (void)])
      (for [(subtree-node (node-lst tree))]
        (extract-helper subtree-node)))
  (begin
    (extract-helper t)
    dcl-list))

; Function-Code DCL Parser
(define (parse-code-dcl tree-lst)
  (define (extract-dcls tlst)
    (define dcl-list empty)
    (begin
      (for [(element-tree tlst)]
        (set! dcl-list (append dcl-list (extract-dcl-from-tree element-tree))))
      dcl-list))
  (begin
    (parse-dcl-list (extract-dcls tree-lst) empty)))

; Checking Validity of Procedures (i.e. use before declaration)
; Returns nothing, if there is error, the program dies
(define (validity-list-check pro-tree-lst)
  (define (match-id-tree tree-lst)
    (define (id-type str)
      (match (string-split str)
        [(list "ID" _) #t]
        [_ #f]))
    (cond
      [(id-type (v-obj-val (node-vobj (car tree-lst)))) (get-value-str (v-obj-val (node-vobj (car tree-lst))))] ;ID
      [else ""]))
    
  ; Check For (factor ID) and (lvalue ID)
  (define (validity-check pro-tree)
    (set! derailed #f)
    (define p-line (v-obj-val (node-vobj pro-tree)))
    (define d-root (get-root-str p-line))
    (cond
      [(equal? d-root "factor")
       (define match-id (match-id-tree (node-lst pro-tree)))
       (cond
         [(equal? p-line "factor ID LPAREN arglist RPAREN")
          (error-hash-ref fast-func-sym-table match-id)]
         [(equal? p-line "factor ID")
          (error-hash-has-no-dcl (hash-ref fast-func-sym-table (func-sign-name current-scope)) match-id)]
         [else (void)])]
      [(equal? p-line "lvalue ID")
       (define match-id (match-id-tree (node-lst pro-tree)))
       (error-hash-has-no-dcl (hash-ref fast-func-sym-table (func-sign-name current-scope)) match-id)
       ]
      [else (void)])
    (if (not derailed)
        (for [(subtree-node (node-lst pro-tree))]
          (validity-check subtree-node))
        (void)))
  
   (for [(pro-tree pro-tree-lst)]
     (validity-check pro-tree)))

; Setting Up DCL Related Objects (i.e Hash Table)
(define (procedure-dcl-setup function-signature parameters tree-lst)
  (define dcl-offset-counter 0)
  ; Setting up function symbol hash table
  (hash-set! func-sym-table function-signature (make-hash))
  (hash-set! fast-func-sym-table
             (func-sign-name function-signature)
             (make-hash))

  (for [(d-obj parameters)]
    (begin
      (error-hash-has-dcl (hash-ref func-sym-table function-signature) d-obj)
      (hash-set! (hash-ref func-sym-table function-signature) d-obj dcl-offset-counter)
      (hash-set! (hash-ref
                  fast-func-sym-table
                  (func-sign-name function-signature))
                 (dcl-obj-symbol d-obj) (dcl-box (dcl-obj-type d-obj) dcl-offset-counter)) ;The KVP is (dcl-obj value)
      (set! dcl-offset-counter (- dcl-offset-counter WORD_BYTE_SIZE))))

  ; Finding declarations in code block
  (define incode-dcl-objects (parse-code-dcl tree-lst))
  (for [(d-obj incode-dcl-objects)]
    (begin
      (error-hash-has-dcl (hash-ref func-sym-table function-signature) d-obj)
      (hash-set! (hash-ref func-sym-table function-signature) d-obj empty)
      (hash-set! (hash-ref
                  fast-func-sym-table
                  (func-sign-name function-signature))
                 (dcl-obj-symbol d-obj) (dcl-box (dcl-obj-type d-obj) dcl-offset-counter))
      (set! dcl-offset-counter (- dcl-offset-counter WORD_BYTE_SIZE)))))

(define (generate-func-sign type procedure-tree-lst)
  ; Retrieving info of return type and function name
  (define return-type (get-value-str (v-obj-val (node-vobj (car procedure-tree-lst)))))
  (define function-name (get-value-str (v-obj-val (node-vobj (cadr procedure-tree-lst)))))
  
  ; Parsing pamaters and generating function signature
  (define param-objects (parse-param procedure-tree-lst type))
  (define param-signature (map (lambda (d-obj) (dcl-obj-type d-obj)) param-objects))
  (define function-signature (func-sign function-name return-type param-signature))
  (list function-signature param-objects)
  )

; Procedure Block Parser (DCL -> Validity Check)
(define (procedure-parse tree type)
  (define tree-lst (node-lst tree))
  
  ; Parsing pamaters and generating function signature
  (define func-sign-tuple (generate-func-sign type tree-lst))
  (define function-signature (car func-sign-tuple))
  (define param-objects (cadr func-sign-tuple))
  (set! tree-lst (skip-tree-node tree-lst "LBRACE"))
  ; Checking if function signature already exists
  (error-hash-exist func-sym-table function-signature)
  ; Since in WLP$, same name function is not allowed in the grammar
  (error-hash-exist fast-func-sym-table (func-sign-name function-signature))
  (set! current-scope function-signature)

  ; This procedure here only works for wlp4 bot general c++ since variable declarations
  ; can only be defined on the top of the function
  (begin
    (procedure-dcl-setup function-signature param-objects tree-lst)
    (validity-list-check tree-lst)))

; Whole Program Parser
(define (parse-elements tree)
  (set! derailed #f)
  (define p-line (v-obj-val (node-vobj tree)))
  (define d-root (get-root-str p-line))
  (cond
    [(equal? d-root "main")
     (procedure-parse tree d-root)
     (set! current-scope "")
     (set! derailed #t)
     ]
    [(equal? d-root "procedure")
     (procedure-parse tree d-root)
     (set! current-scope "")
     (set! derailed #t)
     ]
    [else (void)])
  (if (not derailed)
      (for [(subtree-node (node-lst tree))]
        (parse-elements subtree-node))
      (void)))

; Wrapper for all the context sensitive analysis functions
(define (context-sensitive-analysis)
  (begin
    (generate-input-queue)
    (generate-parse-tree)
    (parse-elements parse-tree)
    (build-typed-parse-tree)
    ;(output-sym-table)
    ))


(define (dump-code code)
  (for [(line code)]
    (displayln line)))

; Code Generation Main Function
(define (code-generator)
  (define unique-counter -1)
  (define local-cl empty) ; Local Code List
  (define code-gen-scope "")

  (define (main-logue)
    (push-codes
     (list
      ".import init"
      ".import new"
      ".import delete"
      ".import print"
      "lis $4"
      ".word 4"
      "lis $9"
      ".word init"      
      "lis $10"
      ".word print"
      "lis $11"
      ".word 1"
      "lis $12"
      ".word new"
      "lis $13"
      ".word delete"
      ))
    (push "$31")
    (push-codes
     (list
      "sub $29, $30, $4"
      "lis $3"
      ".word Fwain"
      "jalr $3"
      "add $30, $29, $4"
      ))
    (pop "$31")
    (push-codes (list "jr $31")))

  (define (build-label label)
    (define (increment-unique-counter)
      (set! unique-counter (add1 unique-counter)))
    (increment-unique-counter)
    (string-append label (number->string unique-counter)))

  (define (build-function-name fname)
    (string-append "F" fname))
  
  (define (label-init label)
    (string-append label ":"))
  
  (define (push-codes lines)
    (set! local-cl (linear-merge lines local-cl)))

  (define (store-offset id)
    (push-codes
     (list (string-append
            (string-append "sw $3, " (number->string id)) "($29)"))))
  
  (define (load-offset id)
    (push-codes
     (list (string-append
            (string-append "lw $3, " (number->string id)) "($29)"))))

  (define (push register)
    (push-codes
     (list
      (string-append
       (string-append "sw " register) ", -4($30)")
      "sub $30, $30, $4")))
  
  (define (pop register)
    (push-codes
     (list
      "add $30, $30, $4"
      (string-append
       (string-append "lw " register) ", -4($30)"))))

  (define (get-dcl-type dcl-tree)
    (define ID (get-value-str (v-obj-val (node-vobj (list-ref (node-lst dcl-tree) 1)))))
    (define d-box (error-hash-ref (hash-ref fast-func-sym-table code-gen-scope) ID))
    (dcl-box-type d-box))

  (define (get-type node)
    (v-obj-type (node-vobj node)))
  
  (define (code expr [load-id #f])
    (define nlst (node-lst expr))
    ;(println (v-obj-val (node-vobj expr)))
    (match (v-obj-val (node-vobj expr))
      [(pregexp "^ID [\\w]+$")
       (if load-id
           (load-offset (dcl-box-offset
                         (error-hash-ref
                          (hash-ref fast-func-sym-table code-gen-scope)
                          (get-value-str (v-obj-val (node-vobj expr))))))
           (void))
       (dcl-box-offset
        (error-hash-ref
         (hash-ref fast-func-sym-table code-gen-scope)
         (get-value-str (v-obj-val (node-vobj expr)))))
       ]
      [(pregexp "^NUM [\\d]+$")
       (push-codes
        (list
         "lis $3"
         (string-append ".word " (get-value-str (v-obj-val (node-vobj expr))))))]
      ["start BOF procedures EOF"
       (code (list-ref nlst 0) load-id)
       (code (list-ref nlst 1) load-id)
       (code (list-ref nlst 2) load-id)]
      ["procedures main" (code (list-ref nlst 0) load-id)]
      ["main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"
       (set! code-gen-scope (get-value-str (v-obj-val (node-vobj (list-ref nlst 1)))))
       (define function-name (build-function-name "wain"))
       (define function-label (string-append function-name ":"))
       (push-codes (list function-label))
       (match (get-dcl-type (list-ref nlst 3))
         [(dcl-type "int" #t)
          (push "$31")
          (push-codes (list "jalr $9"))
          (pop "$31")
           ]
         [(dcl-type "int" #f)
          (push-codes
           (list
            "add $14, $0, $2"
            "add $2, $0, $0")
           )
          (push "$31")
          (push-codes (list "jalr $9"))
          (pop "$31")
          (push-codes (list "add $2, $14, $0"))
         ])

       (push "$1")
       (push "$2")
       (code (list-ref nlst 8) load-id) ; For dcls
       (code (list-ref nlst 9) load-id) ; For statements
       (code (list-ref nlst 11)) ; For expr
       (push-codes (list
                    ;"add $30, $29, $4"
                    "jr $31"))
       ]
      ["type INT" (code (list-ref nlst 0) load-id)]
      ["expr term" (code (list-ref nlst 0) load-id)]
      ["term factor" (code (list-ref nlst 0) load-id)]
      ["factor ID" (code (list-ref nlst 0) #t)]
      ["factor LPAREN expr RPAREN"
       (code (list-ref nlst 0) load-id)
       (code (list-ref nlst 1) load-id)
       (code (list-ref nlst 2) load-id)]
      ["expr expr PLUS term"
       (define type1 (get-type (list-ref nlst 0)))
       (define type2 (get-type (list-ref nlst 2)))
       (define signature (list type1 type2))
       (match signature
         [(list 'INTPTR 'INT)
          (code (list-ref nlst 0) load-id)
          (push "$3")
          (code (list-ref nlst 2) load-id)
          (push-codes
           (list
            "mult $3, $4"
            "mflo $3"))
          (pop "$5")
          (push-codes (list "add $3, $5, $3"))
          ]
         [(list 'INT 'INTPTR)
          (code (list-ref nlst 0) load-id)
          (push-codes
           (list
            "mult $3, $4"
            "mflo $3"))
          (push "$3")
          (code (list-ref nlst 2) load-id)
          (pop "$5")
          (push-codes (list "add $3, $5, $3"))
          ]
         [(list 'INT 'INT)
          (code (list-ref nlst 0) load-id)
          (push "$3")
          (code (list-ref nlst 2) load-id)
          (pop "$5")
          (push-codes (list "add $3, $5, $3"))]
         )]
      ["expr expr MINUS term"
       (define type1 (get-type (list-ref nlst 0)))
       (define type2 (get-type (list-ref nlst 2)))
       (define signature (list type1 type2))
       (match signature
         [(list 'INTPTR 'INT)
          (code (list-ref nlst 0) load-id)
          (push "$3")
          (code (list-ref nlst 2) load-id)
          (push-codes
           (list
            "mult $3, $4"
            "mflo $3"))
          (pop "$5")
          (push-codes (list "sub $3, $5, $3"))
          ]
         [(list 'INTPTR 'INTPTR)
          (code (list-ref nlst 0) load-id)
          (push "$3")
          (code (list-ref nlst 2) load-id)
          (pop "$5")
          (push-codes
           (list
            "sub $3, $5, $3"
            "div $3, $4"
            "mflo $3"))
          ]
         [(list 'INT 'INT)
          (code (list-ref nlst 0) load-id)
          (push "$3")
          (code (list-ref nlst 2) load-id)
          (pop "$5")
          (push-codes (list "sub $3, $5, $3"))]
         )]
      ["term term STAR factor"
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (push-codes (list "mult $5, $3"))
       (push-codes (list "mflo $3"))]
      ["term term SLASH factor"
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (push-codes (list "div $5, $3"))
       (push-codes (list "mflo $3"))]
      ["term term PCT factor"
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (push-codes (list "div $5, $3"))
       (push-codes (list "mfhi $3"))]
      ["factor NUM"
       (code (list-ref nlst 0) load-id)]
      ["statements statements statement"
       (code (list-ref nlst 0) load-id)
       (code (list-ref nlst 1) load-id)
       ]
      ["statement PRINTLN LPAREN expr RPAREN SEMI"
       (push "$1")
       (code (list-ref nlst 2) load-id)
       (push-codes (list "add $1, $3, $0"))
       (push "$31")
       (push-codes (list "jalr $10"))
       (pop "$31")
       (pop "$1")
       ]
      ["dcls dcls dcl BECOMES NUM SEMI"
       (code (list-ref nlst 0) load-id)
       (code (list-ref nlst 1) load-id)
       (code (list-ref nlst 3) load-id)
       (push "$3")
       ]
      ["statement lvalue BECOMES expr SEMI"
       (match (v-obj-val (node-vobj (list-ref nlst 0)))
         ["lvalue STAR factor"
          (code (list-ref nlst 2) load-id)
          (push "$3")
          (code (list-ref (node-lst (list-ref nlst 0)) 1))
          (pop "$5")
          (push-codes (list "sw $5, 0($3)"))
          ]
         [_
          (define offset-id (code (list-ref nlst 0) load-id))
          (code (list-ref nlst 2) load-id)
          (store-offset offset-id)
          ])]
      ["lvalue ID"
       (code (list-ref nlst 0) load-id)
       ]
      ["lvalue LPAREN lvalue RPAREN"
       (code (list-ref nlst 1) load-id)
       ]
      ["statement WHILE LPAREN test RPAREN LBRACE statements RBRACE"
       (define start-label (build-label "startLoop"))
       (define end-label (build-label "endLoop"))
       (push-codes (list (label-init start-label)))
       (code (list-ref nlst 2) load-id)
       (push-codes
        (list (string-append "beq $3, $0, " end-label)))
       (code (list-ref nlst 5) load-id)
       (push-codes
        (list
         (string-append "beq $0, $0, " start-label)
         (label-init end-label)
         ))
       ]
      ["test expr LT expr"
       (define test-type (get-type (list-ref nlst 0)))
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (if (equal? test-type 'INTPTR)
           (push-codes (list "sltu $3, $5, $3"))
           (push-codes (list "slt $3, $5, $3")))
       ]
      ["test expr GT expr"
       (define test-type (get-type (list-ref nlst 0)))
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (if (equal? test-type 'INTPTR)
           (push-codes (list "sltu $3, $3, $5"))
           (push-codes (list "slt $3, $3, $5")))
       ]
      ["test expr EQ expr"
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (push-codes
        (list
         "beq $3, $5, 2"
         "add $3, $0, $0"
         "beq $0, $0, 1"
         "add $3, $0, $11"))
       ]
      ["test expr NE expr"
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (push-codes
        (list
         "beq $3, $5, 2"
         "add $3, $0, $11"
         "beq $0, $0, 1"
         "add $3, $0, $0"
         ))
       ]
      ["test expr LE expr"
       (define test-type (get-type (list-ref nlst 0)))
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (if (equal? test-type 'INTPTR)
           (push-codes
            (list
             "bne $3, $5, 2"
             "add $3, $0, $11"
             "beq $0, $0, 1"
             "sltu $3, $5, $3"))
           (push-codes
            (list
             "bne $3, $5, 2"
             "add $3, $0, $11"
             "beq $0, $0, 1"
             "slt $3, $5, $3")))
       ]
      ["test expr GE expr"
       (define test-type (get-type (list-ref nlst 0)))
       (code (list-ref nlst 0) load-id)
       (push "$3")
       (code (list-ref nlst 2) load-id)
       (pop "$5")
       (if (equal? test-type 'INTPTR)
           (push-codes
            (list
             "bne $3, $5, 2"
             "add $3, $0, $11"
             "beq $0, $0, 1"
             "sltu $3, $3, $5"))
           (push-codes
            (list
             "bne $3, $5, 2"
             "add $3, $0, $11"
             "beq $0, $0, 1"
             "slt $3, $3, $5")))
       ]
      ["statement IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE"
       (define else-label (build-label "elseIf"))
       (define end-label (build-label "endIf"))
       (code (list-ref nlst 2) load-id)
       (push-codes
        (list (string-append "beq $3, $0, " else-label)))
       (code (list-ref nlst 5) load-id)
       (push-codes
        (list (string-append "beq $0, $0, " end-label)))
       (push-codes (list (label-init else-label)))
       (code (list-ref nlst 9) load-id)
       (push-codes (list (label-init end-label)))
       ]
      ["dcls dcls dcl BECOMES NULL SEMI"
       (code (list-ref nlst 0) load-id)
       (code (list-ref nlst 1) load-id) ; Does Nothing
       (push "$11")
       ]
      ["factor NULL"
       (push-codes (list "add $3, $0, $11"))]
      ["factor AMP lvalue"
       (match (v-obj-val (node-vobj (list-ref nlst 1)))
         ["lvalue STAR factor"
          (code (list-ref (node-lst (list-ref nlst 1)) 1))
          ]
         [_ (push-codes
             (list
              "lis $3"
              (string-append ".word " (number->string (code (list-ref nlst 1) load-id)))
              (string-append "add $3, $3, $29")))
            ]
         )]
      ["factor STAR factor"
       (code (list-ref nlst 1) load-id)
       (push-codes (list "lw $3, 0($3)"))
       ]
      ["factor NEW INT LBRACK expr RBRACK"
       (code (list-ref nlst 3) load-id)
       (push-codes (list "add $1, $3, $0"))
       (push "$31")
       (push-codes (list "jalr $12"))
       (pop "$31")
       (push-codes
        (list
         "bne $3, $0, 1"
         "add $3, $11, $0")
        )
       ]
      ["statement DELETE LBRACK RBRACK expr SEMI"
       (define delete-label (build-label "skipDelete"))
       (code (list-ref nlst 3) load-id)
       (push-codes
        (list
         (string-append "beq $3, $11, " delete-label)
         "add $1, $3, $0")
        )
       (push "$31")
       (push-codes (list "jalr $13"))
       (pop "$31")
       (push-codes (list (label-init delete-label)))
       ]
      ["factor ID LPAREN RPAREN"
       (define function-name
         (build-function-name
          (get-value-str (v-obj-val (node-vobj (list-ref nlst 0))))))
       (push "$29")
       (push "$31")
       (push-codes (list "sub $29, $30, $4")) ; Saving the expected $29 location
       (push-codes
        (list
         "lis $5"
         (string-append ".word " function-name)
         "jalr $5"
         ))
       (push-codes (list "add $30, $29, $4"))
       (pop "$31")
       (pop "$29")
       ]
      ["procedures procedure procedures"
       (code (list-ref nlst 0) load-id)
       (code (list-ref nlst 1) load-id)
       ]
      ["procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"       
       (define original-func-name (get-value-str (v-obj-val (node-vobj (list-ref nlst 1)))))
       (set! code-gen-scope original-func-name)
       (define function-name (build-function-name original-func-name))
       (define function-label (string-append function-name ":"))
       (push-codes (list function-label))
       (code (list-ref nlst 3) load-id) ; For params
       (code (list-ref nlst 6) load-id) ; For dcls
       (code (list-ref nlst 7) load-id) ; For statements
       (code (list-ref nlst 9) load-id) ; For expr
       (push-codes (list "jr $31"))
       ]
      ["factor ID LPAREN arglist RPAREN"
       (define function-name
         (build-function-name
          (get-value-str (v-obj-val (node-vobj (list-ref nlst 0))))))
       (push "$29")
       (push "$31")
       (push-codes (list "sub $15, $30, $4")) ; Saving the expected $29 location
       (code (list-ref nlst 2) load-id)
       (push-codes (list "add $29, $15, $0"))
       (push-codes (list
                    "lis $5"
                    (string-append ".word " function-name)
                    "jalr $5"))
       (push-codes (list "add $30, $29, $4"))
       (pop "$31")
       (pop "$29")
       ]
      ["arglist expr"
       (code (list-ref nlst 0) #t)
       (push "$3")
       ]
      ["arglist expr COMMA arglist"
       (code (list-ref nlst 0) #t)
       (push "$3")
       (code (list-ref nlst 2) #t)
       ]
      [_ (void)]
      )
    )
  (main-logue)
  (code parse-tree)
  (reverse local-cl))

(define (wlp4-compiler)
  (begin
    (context-sensitive-analysis)
    (dump-code (code-generator))
    ))

(wlp4-compiler)