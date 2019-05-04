#lang racket

(define alphabets (make-hash))
(define transition-table (make-hash))
(define rule-table (make-hash))
(define reduce-table (make-hash))
(define states empty)
(define start-state empty)



; Some utility functions
(define (in-list element lst)
  (ormap (lambda (e) (equal? e element)) lst))

(define (print-end str)
  (begin (print str (current-error-port)) (exit)))

(define (state-checker state)
  (if (in-list state states)
      state
      (print-end "ERROR: Transition State Not Found")))

(define (alphabet-checker alphabet)
  (if (in-list alphabet alphabets)
      alphabet
      (print-end "ERROR: Alphabet Not Found")))

(define (get-transition-state state alphabet)
  (if (hash-has-key? transition-table state)
    (if (hash-has-key? (hash-ref transition-table state) alphabet)
        (hash-ref (hash-ref transition-table state) alphabet)
        #f)
    #f))

; THE MAIN ASSEMBLER FUNCTION
(define (dfa-organizer)
  (define (alphabet-pass)
    (let ([numLine (read-line)])
    (for [(num (build-list (string->number numLine) values))]
      (define alphabet (read-line))
      (set! alphabets (cons alphabet alphabets))
    )))
  (define (state-pass)
    (let ([numLine (read-line)])
    (for [(num (build-list (string->number numLine) values))]
      (define state (read-line))
      (set! states (cons state states))
    )))
  (define (init-pass)
    (let ([state (read-line)])
      (set! start-states (cons state start-states))
    ))
  (define (end-pass)
    (let ([numLine (read-line)])
    (for [(num (build-list (string->number numLine) values))]
      (define end-state (read-line))
      (set! end-states (cons end-state end-states))
    )))
  (define (transition-pass)
    (let ([numLine (read-line)])
    (for [(num (build-list (string->number numLine) values))]
      (define transition (string-split (read-line)))
      (begin 
        (if (hash-has-key? transition-table (state-checker (car transition)))
          (void)
          (hash-set! transition-table (car transition) (make-hash)))
        (if (hash-has-key? (hash-ref transition-table (car transition)) (alphabet-checker (cadr transition)))
              (print-end "ERROR: Alphabet in Transition Duplication")
              (begin
                (hash-set! (hash-ref transition-table (car transition)) (cadr transition) (state-checker (caddr transition)))
                (hash-set! transition-table (car transition) (hash-ref transition-table (car transition))))))
      )))
  (define (parse)
    (define (start-check state)
      (begin
        ;(println start-states)
        ;(println state)
        (in-list state start-states)))
    (define (end-check state)
      (begin
        ;(println end-states)
        ;(println state)
        (in-list state end-states)))
    (define (parse-helper lst state validity)
      (if validity
        (if (empty? lst)
          validity
          (if (empty? (cdr lst))
              (parse-helper (cdr lst) empty (end-check (get-transition-state state (car lst))))
              (parse-helper (cdr lst) (get-transition-state state (car lst)) (get-transition-state state (car lst)))))
        validity))
    (for [(line (in-lines))]
        (define state-check (string-split line))
        (if (empty? state-check)
          (truth-print (end-check (car start-states)))
          (truth-print (parse-helper state-check (car start-states) (start-check (car start-states)))))))
  (begin
    (alphabet-pass)
    (state-pass)
    (init-pass)
    (end-pass)
    (transition-pass)
    (parse)
  ))


; Executing the assembler function
(dfa-organizer)
