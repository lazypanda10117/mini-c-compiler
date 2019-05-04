#lang racket
;;;
;;; Racket starter code for CS241 A3
;;;
;;; This file contains helpers for asm.rkt. You should read it up until the
;;; comment saying otherwise.

(provide scan token)
(require racket/match)

;; A token structure has two parts. Its kind describes
;; what category the token falls into, such as ID or INT.
;; Its lexeme describes exactly what the user typed in,
;; such as "a" or "1234".
(define-struct token (kind lexeme) #:transparent)

;; Gets the integer value of an INT, HEXINT, or REG.
;; Should not be called on other types.
(define (token-int-value tok)
  (match tok
    [(token 'INT    lexeme)
     (string->number lexeme)]
    [(token 'HEXINT lexeme)
     (string->number (substring lexeme 2) 16)]
    [(token 'REG    lexeme)
     (string->number (substring lexeme 1))]
    [_ (error "Cannot get int value of token")]))

;; A list of acceptable token kinds. Listed in more detail below.
(define asm-kinds
  (set 'ID 'LABEL 'WORD 'COMMA 'LPAREN 'RPAREN 'INT 'HEXINT 'REG 'ZERO 'DOTID))

;; Scans a single line of input and produces a list of tokens.
;;
;; Scan returns tokens with the following kinds:
;; ID: identifiers and keywords.
;; LABEL: labels (identifiers ending in a colon).
;; WORD: the special ".word" keyword.
;; COMMA: a comma.
;; LPAREN: a left parenthesis.
;; RPAREN: a right parenthesis.
;; INT: a signed or unsigned 32-bit integer written in decimal.
;; HEXINT: an unsigned 32-bit integer written in hexadecimal.
;; REG: a register between $0 and $31.
(define (scan input)
  ; The rest of this file contains techniques beyond the scope of A3.
  ; You may want to come back and read it when working on future assignments,
  ; but do not need to understand it for now.
  (define (token-postprocess tok)
    (match tok
      [(token 'DOTID ".word") (make-token 'WORD ".word")]
      [(token 'DOTID _)       (error 'ERROR "Unrecognized DOTID token lexeme.")]
      [(token 'ZERO  lex)     (make-token 'INT lex)]
      [_                       tok]))

  (let* [(tokens (simplified-maximal-munch asm-dfa (string->list input)))
         (fixed-tokens
           (filter (lambda (x) (set-member? asm-kinds (token-kind x)))
                   (map token-postprocess tokens)))]

    fixed-tokens))

;; Represents a DFA. The states and alphabet are not stored here.
;; * start should be a state (any type you want).
;; * accepting should be a set of states.
;; * transition should be a function t : state * letter -> (either state #f)
;;   where #f represents failure to transition.
(define-struct DFA (start accepting transition))

(define (char-hexdigit? ch)
  (string-contains? "abcdefABCDEF0123456789" (string ch)))

(define asm-dfa
  (make-DFA
    'START
    (set-union (set 'WHITESPACE 'COMMENT) (set-remove asm-kinds 'WORD))
    (lambda (state letter)
      (match (cons state letter)
        [(not (cons _ (? char?)))                                #f]
        [(cons 'START (? char-alphabetic?))                     'ID]
        [(cons 'START #\.)                                      'DOT]
        [(cons 'START #\0)                                      'ZERO]
        [(cons 'START (? char-numeric?))                        'INT]
        [(cons 'START #\-)                                      'MINUS]
        [(cons 'START #\;)                                      'COMMENT]
        [(cons 'START (? char-whitespace?))                     'WHITESPACE]
        [(cons 'START #\$)                                      'DOLLARS]
        [(cons 'START #\,)                                      'COMMA]
        [(cons 'START #\()                                      'LPAREN]
        [(cons 'START #\))                                      'RPAREN]
        [(cons 'ID (or (? char-alphabetic?)
                        (? char-numeric?)))                     'ID]
        [(cons 'ID #\:)                                         'LABEL]
        [(cons (or 'DOT 'DOTID) (? char-alphabetic?))           'DOTID]
        [(cons 'ZERO #\x)                                       'ZEROX]
        [(cons (or 'ZEROX 'HEXINT) (? char-hexdigit?))          'HEXINT]
        [(cons (or 'ZERO 'MINUS 'INT) (? char-numeric?))        'INT]
        [(cons 'COMMENT (? (lambda (c) (not (eq? c #\newline))))) 'COMMENT]
        [(cons 'WHITESPACE (? char-whitespace?))                'WHITESPACE]
        [(cons (or 'DOLLARS 'REG) (? char-numeric?))            'REG]
        [_                                                       #f]))))

;; Takes a DFA and a list of letters and performs the simplified maximal
;; munch algorithm, which you will see in class around assignment 5 or 6.
(define (simplified-maximal-munch dfa input)
  ; Munch the longest possible token and return a pair containing it
  ; and the remaining (unconsumed) input
  (define (scan-one input state consumed-input)
    (let [(transition ((DFA-transition dfa)
                       state
                       (if (empty? input) null (car input))))]
      (cond [(and (not transition) (set-member? (DFA-accepting dfa) state))
             (cons input (make-token state
                                     (list->string (reverse consumed-input))))]
            [(not transition)
             (error 'ERROR
                    (string-append
                      "Simplified maximal munch failed on input: "
                      (string-append (list->string (reverse consumed-input))
                                     (list->string input))))]
            [else (scan-one (cdr input) transition
                            (cons (car input) consumed-input))])))

  ; Repeatedly call scan-one to tokenize the entire input
  (define (scan-all input accumulator)
    (if (empty? input)
      (reverse accumulator)
      (let [(result (scan-one input (DFA-start dfa) null))]
        (scan-all (car result) (cons (cdr result) accumulator)))))

  (scan-all input null))
