#lang rosette/safe
(require rosette/lib/synthax)   ; grammars
(require rosette/lib/destruct)  ; pattern matching

; Interpreter for the target language
(define (eval e)
  (destruct e
    [(plus x y) (+ (eval x) (eval y))]
    [(mult x y) (* (eval x) (eval y))]
    [(minus x y) (- (eval x) (eval y))]
    [_ e]))

; "Tokens" for the target language
(define-struct plus (x y) #:transparent)
(define-struct minus (x y) #:transparent)
(define-struct mult (x y) #:transparent)

; Grammar for the target language
(define-grammar (arith x)
  [op (choose + - *)]
  [expr
    (choose (?? integer?)
            x
            ((op) (expr) (expr))
            ((op) (expr) (expr))
            ((op) (expr) (expr)))])

; Some example behavioral specifications for f
(define (spec-square x)
  (assert (equal? (f 0) 0))
  (assert (equal? (f 1) 1))
  (assert (equal? (f 2) 4))
  (assert (equal? (f 3) 9)))

(define (spec-square-formula x)
  (assert (equal? (f x) (* x x))))

(define (spec-id x)
  (assert (equal? (f 2) 2))
  (assert (equal? (f 3) 3)))

(define (spec-id-formula x)
  (assert (equal? (f x) x)))

; The function we want to synthesize, and what subset of the grammar it can use
(define (f x) (arith x))

; Behavioral specification
;(define spec spec-square)

; Input space
(define-symbolic x integer?)

; Synthesize
(define solution
  (synthesize
    #:forall (list x)
    #:guarantee (spec-id x)
    ))

; Results
(if (sat? solution)
  (begin (print-forms solution)
         (equal? (f 2) 9))
  (display "UNSAT\n"))

; Synthesize 2
(define solution2
  (synthesize
    #:forall (list x)
    #:guarantee (spec-square x)
    ))

; Results
(if (sat? solution2)
  (begin (print-forms solution2)
         (equal? (f 2) 9))
  (display "UNSAT\n"))

(evaluate f solution)
