#lang racket
(define-struct node (val lst))

(define cfg-term-sym empty)
(define cfg-nonterm-sym empty)
(define cfg-start-sym empty)
(define cfg-rule empty)
(define cfg-rule-string empty)

(define start-state 0)
(define states empty)
(define state-action (make-hash))
(define shift-table (make-hash))
(define reduction-table (make-hash))

(define local-memory-stack empty)
(define state-stack empty)
(define symbol-stack empty)
(define process-queue empty)
(define output-queue empty)
(define output-tree-stack empty)
(define symbol-counter 0)

(define wlp4-definition-input (open-input-file "wlp4-cfg.in"))

; Some utility functions
(define (in-list element lst)
  (ormap (lambda (e) (equal? e element)) lst))

(define (print-end str)
  (begin (displayln str (current-error-port)) (exit)))

(define (state-checker state)
  ;(println state)
  (if (in-list state states)
      state
      (print-end "ERROR: Transition State Not Found")))

(define (alphabet-checker alphabet)
  ;(println alphabet)
  (if (or (in-list alphabet cfg-term-sym) (in-list alphabet cfg-nonterm-sym))
      alphabet
      (print-end "ERROR: Transition Alphabet Not Found")))

(define (get-transition-state table state alphabet)
  (if (hash-has-key? table state)
      (if (hash-has-key? (hash-ref table state) alphabet)
          (hash-ref (hash-ref table state) alphabet)
          (print-end "ERROR: Something is going crazy here .___."))
      (print-end "ERROR: Something is going crazy here too o___o")))

(define (pop-stack stack n)
  (if (> n 0)
      (pop-stack (cdr stack) (sub1 n))
      stack))

(define (error-line)
  (define error-text (string-append "ERROR at " (number->string symbol-counter)))
  (print-end error-text))

(define (error-hash-ref table key)
  (if (hash-has-key? table key)
      (hash-ref table key)
      (error-line)))

(define (print-derivation output-queue)
  (if (empty? output-queue)
      (void)
      (begin
        (displayln (car output-queue))
        (print-derivation (cdr output-queue)))))

(define (get-end-state all-states)
  (define state (car all-states))
  (if (not (empty? all-states))
    (if (or (hash-has-key? shift-table state) (hash-has-key? reduction-table state))
       (get-end-state (cdr all-states))
       state
    )
    (print-end "ERROR: Something funny is going on in get-end-state.")))

(define (get-start-rule)
  (define (get-start-rule-helper idx)
    ;(println idx)
    (if (>= idx 0)
      (if (equal? (car (vector-ref cfg-rule idx)) cfg-start-sym)
          idx
          (get-start-rule-helper (sub1 idx)))
      (print-end "ERROR: Something funny is going on in get-start-rule.")))
  (get-start-rule-helper (sub1 (vector-length cfg-rule))))

(define (input-tuple? in-tup)
  (pair? in-tup))

(define (resolve-input-tuple in-tup)
  (if (input-tuple? in-tup) (car in-tup) in-tup))

(define (parse-tree-gen stop)
  ;(println output-tree-stack)
  (define oq-line (car output-tree-stack))
  ; Since we store in reverse derivation and we dont want the first element to be recursed on
  (define oq-elements (reverse (cdr (string-split oq-line))))
  (set! output-tree-stack (cdr output-tree-stack))
  (define (build-elements elements lst)
    (if (empty? elements)
        lst
        (build-elements (cdr elements) (cons (parse-tree-gen (in-list (car elements) cfg-term-sym)) lst))
    ))
  (cond
      [stop (node oq-line empty)]
      [else  (node oq-line (build-elements oq-elements empty))]))

(define (pre-order-flatten tree)
  (displayln (node-val tree))
  (for [(subtree-node (node-lst tree))]
    (pre-order-flatten subtree-node)))

(define (representation-builder)
  (define (cfg-pass)
    ; Terminal Symbol Pass
    (set! cfg-term-sym (cons 'EMPTY cfg-term-sym))
    (let ([numLine (read-line wlp4-definition-input)])
      (for [(num (build-list (string->number numLine) values))]
        (define term-sym (read-line wlp4-definition-input))
        (set! cfg-term-sym (cons term-sym cfg-term-sym))
        ))
    
    ; Non-Terminal Symbol Pass
    (let ([numLine (read-line wlp4-definition-input)])
      (for [(num (build-list (string->number numLine) values))]
        (define nonterm-sym (read-line wlp4-definition-input))
        (set! cfg-nonterm-sym (cons nonterm-sym cfg-nonterm-sym))
        ))
    
    ; Start Symbol Pass
    (define start-sym (read-line wlp4-definition-input))
    (set! cfg-start-sym start-sym)
    
    ; State Number Pass
    (define cfg-rule-num (string->number (read-line wlp4-definition-input)))
    (define cfg-rule-vector (make-vector cfg-rule-num))
    (define cfg-rule-string-vector (make-vector cfg-rule-num))

    ; Rule Pass
    (let ([numLine cfg-rule-num])
      (for [(num (build-list numLine values))]
        (define rule-string (read-line wlp4-definition-input))
        (define rule (string-split rule-string))
        (vector-set! cfg-rule-string-vector num rule-string)
        (vector-set! cfg-rule-vector num (list (car rule) (cdr rule)))
        ))
    (set! cfg-rule-string cfg-rule-string-vector)
    (set! cfg-rule cfg-rule-vector))
  
  (define (lr1-transducer-pass)
    (define (build-transducer)
      (define (build-single-shift-transition input transition output)
        (if (hash-has-key? shift-table input)
            (void)
            (hash-set! shift-table input (make-hash)))
        (if (hash-has-key? (hash-ref shift-table input) (alphabet-checker transition))
            (print-end "ERROR: Term Shift Duplication in Transition Table")
            (begin
              (hash-set! (hash-ref shift-table input) transition output)
              (hash-set! shift-table input (hash-ref shift-table input)))))
      
      (define (build-single-reduction-transition input transition output)
        (if (hash-has-key? reduction-table input)
          (void)
          (hash-set! reduction-table input (make-hash)))
        (if (hash-has-key? (hash-ref reduction-table input) (alphabet-checker transition))
            (print-end "ERROR: Term Reduction Duplication in Transition Table")
            (begin
              (hash-set! (hash-ref reduction-table input) transition output)
              (hash-set! reduction-table input (hash-ref reduction-table input)))))
      (begin
        (define state-num (string->number (read-line wlp4-definition-input)))
        (set! states (build-list state-num values)) ; This is how the states of the LR(1) transducer are defined
        (let ([numLine (read-line wlp4-definition-input)])
          (for [(num (build-list (string->number numLine) values))]
            (define rule (string-split (read-line wlp4-definition-input)))
            ; Build State Action Table, Transition Table
            (define input-state (state-checker (string->number (car rule)))) ; Since all states are numbered
            (define transition-sym (cadr rule))
            (define transition-type
              ((lambda (type)
                (if (string=? "shift" type)
                    'SHIFT
                    (if (string=? "reduce" type)
                        'REDUCE
                        (print-end "ERROR: Transition Type Not Reduce or Shift"))))
              (caddr rule)))
            (define output (state-checker (string->number (car (cdddr rule))))) ; Since all outputs (states/rules) are numbered
            (begin
              (hash-set! state-action (cons input-state transition-sym) transition-type)
              (if (equal? transition-type 'SHIFT)
                  (build-single-shift-transition input-state transition-sym output)
                  (build-single-reduction-transition input-state transition-sym output)))
            ))
        (define terminating-state (get-end-state states))
        (build-single-reduction-transition terminating-state 'EMPTY (get-start-rule))
        (hash-set! state-action (cons terminating-state 'EMPTY) 'REDUCE)))
      (build-transducer))

  (begin
    (cfg-pass)
    (lr1-transducer-pass)))

(define (match-representation)
  (define (match-init-augmented)
    (begin
      (set! process-queue (cons (cons "BOF" (cons "BOF" empty)) process-queue))
      (for [(line (in-lines))]
        (define token (string-split line))
        (set! process-queue (cons token process-queue)))
      (set! process-queue (cons (cons "EOF" (cons "EOF" empty)) process-queue)))
      (set! process-queue (reverse process-queue)) ; We were inserting it as a stack before
      (set! state-stack (cons start-state state-stack)))
    
  (define (process-shift current-state next-input-tuple)
    (define next-input (resolve-input-tuple next-input-tuple))
    (define next-state (get-transition-state shift-table current-state next-input))
    (set! process-queue (cdr process-queue)) ; Pop next-input from process queue
    (set! state-stack (cons next-state state-stack)) ; Push next-state to state stack
    (set! symbol-stack (cons next-input symbol-stack))
    (set! symbol-counter (add1 symbol-counter))
    (if (input-tuple? next-input-tuple)
        (set! local-memory-stack (cons next-input-tuple local-memory-stack))
        (void)))
  
  (define (process-reduce current-state next-input-tuple)
    (define next-input (resolve-input-tuple next-input-tuple))
    (define reduction-rule-num (get-transition-state reduction-table current-state next-input))
    (define reduction-rule (vector-ref cfg-rule reduction-rule-num))
    (define reduction-symbol (car reduction-rule))
    (define reduction-prereq (cadr reduction-rule))
    (define backtrack-length (length reduction-prereq))
    (define reduction-rule-output (vector-ref cfg-rule-string reduction-rule-num))

    (define local-output-stack
      (map
       (lambda (tuple) (string-append (car tuple) (string-append " " (cadr tuple))))
       local-memory-stack))
    (set! local-memory-stack empty)
    
    (set! local-output-stack (cons reduction-rule-output local-output-stack))
    (set! state-stack (pop-stack state-stack backtrack-length))
    (set! symbol-stack (pop-stack symbol-stack backtrack-length))
    (set! output-queue (append local-output-stack output-queue)) ; TODO: Optimize    
    
    (if (equal? next-input 'EMPTY)
        (begin
          (set! symbol-stack (cons reduction-symbol symbol-stack))
          (set! process-queue (cdr process-queue)))
        (begin
          (set! process-queue (cons reduction-symbol process-queue))
          (set! symbol-counter (sub1 symbol-counter)) ; Only need for non last iteration, since the last iteration is an edge case
          )))
  
  (define (next-step)
    (define current-state (car state-stack))
    (define next-input-tuple (car process-queue))
    (define next-input (resolve-input-tuple next-input-tuple))
    ;This takes care of error when you cannot shift/reduce
    (define next-action (error-hash-ref state-action (cons current-state next-input)))
    (if (equal? next-action 'SHIFT)
        (process-shift current-state next-input-tuple)
        (process-reduce current-state next-input-tuple)))
  
  (define (end-verification)
    (set! output-tree-stack output-queue)
    (if (= (length symbol-stack) 1)
          (if (string=? cfg-start-sym (car symbol-stack))
              (pre-order-flatten (parse-tree-gen #f))
            (error-line))
          (error-line)
        ))

  (define last-iter-flag #f)
  
  (define (grammar-matcher)
    ;(println process-queue)
    ;(println state-stack)
    ;(println symbol-stack)
    (if (not (empty? process-queue))
        (begin
          (next-step)
          (grammar-matcher))
        (if last-iter-flag
            (end-verification)
            (begin
              (set! process-queue (cons (cons 'EMPTY (cons 'EMPTY empty)) process-queue))
              (set! last-iter-flag #t)
              (grammar-matcher)))))
  
  (begin
    (match-init-augmented)
    (grammar-matcher)
    ))

; Executing the LR(1) function
(define (LR1-Parser)
  (begin
    (representation-builder)
    (match-representation)))

(LR1-Parser)