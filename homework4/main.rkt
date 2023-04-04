#lang rosette/safe

(require rosette/lib/synthax)
(require rosette/lib/destruct)

(define-struct plus (x y) #:transparent)
(define-struct minus (x y) #:transparent)
(define-struct mult (x y) #:transparent)

(define (eval e)
  (destruct e
    [(plus x y) (+ (eval x) (eval y))]
    [(mult x y) (* (eval x) (eval y))]
    [(minus x y) (- (eval x) (eval y))]
    [_ e]))

(define-grammar (arith x)
  [expr
    (choose (?? integer?)
            x
            (* (expr) (expr))
            (- (expr) (expr))
            (+ (expr) (expr)))])

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
(define spec spec-square-formula)

; Input space
(define-symbolic x integer?)

; Synthesize
(define solution
  (synthesize
    #:forall (list x)
    #:guarantee (spec x)
    ))

; Results
(if (sat? solution)
  (begin (print-forms solution)
         (equal? (f 2) 9))
  (display "UNSAT\n"))
