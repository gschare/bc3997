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
   ;[op (choose + - *)]
   [expr
     (choose (?? integer?)
             x
             (+ (expr) (expr))
             (- (expr) (expr))
             (* (expr) (expr)))])

;(define-synthax ops ([(ops) (choose + - *)]))

;(define-synthax (arith x depth)
;  #:base (choose x (?? integer?))
;  #:else (choose
;           x
;           (?? integer?)
;           (
;           (choose + - *) (arith x (- depth 1)) (arith x (- depth 1))))
;  )

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
(define (f x)
  ;((choose + * -) (arith x) (arith x))
  (choose (arith x) ((choose + * -) (arith x) (arith x)))
  )

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
  (print-forms solution)
  (display "UNSAT\n"))

; Synthesize 2
(define solution2
  (synthesize
    #:forall (list x)
    #:guarantee (spec-square x)
    ))

; Results
(if (sat? solution2)
  (print-forms solution2)
  (display "UNSAT\n"))
