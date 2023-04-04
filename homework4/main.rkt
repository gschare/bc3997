#lang rosette/safe
(require rosette/lib/synthax)   ; grammars
(require rosette/lib/destruct)  ; pattern matching

; Grammar for the target language
(define-grammar (arith x)
  [expr
    (choose (?? integer?)
            x
            (+ (expr) (expr))
            (- (expr) (expr))
            (* (expr) (expr)))])

; Some example behavioral specifications
(define (spec-square impl x)
  (assert (equal? (impl 0) 0))
  (assert (equal? (impl 1) 1))
  (assert (equal? (impl 2) 4))
  (assert (equal? (impl 3) 9)))

(define (spec-square-formula impl x)
  (assert (equal? (impl x) (* x x))))

(define (spec-id impl x)
  (assert (equal? (impl 2) 2))
  (assert (equal? (impl 3) 3)))

(define (spec-id-formula impl x)
  (assert (equal? (impl x) x)))

(define (spec-random impl x)
  ; x |-> x * 3 - 2
  (assert (equal? (impl 2) 4))
  (assert (equal? (impl 3) 7))
  (assert (equal? (impl 5) 13))
  )

; "Tokens" for the target language
(define-struct plus (x y) #:transparent)
(define-struct minus (x y) #:transparent)
(define-struct mult (x y) #:transparent)

; Simple interpreter in group Z/n
; This essentially enables alternate semantics
(define (eval-mod e n)
  (destruct e
    [(plus x y) (modulo
                  (+ (eval-mod x n) (eval-mod y n))
                  n)]
    [(mult x y) (modulo
                  (* (eval-mod x n) (eval-mod y n))
                  n)]
    [(minus x y) (modulo
                   (- (eval-mod x n) (eval-mod y n))
                   n)]
    [_ (modulo e n)]))

; Grammar for the target language
(define-grammar (mod-arith x)
  [expr
    (choose (?? integer?)
            x
            (plus (expr) (expr))
            (mult (expr) (expr))
            (minus (expr) (expr)))])

(define (spec-double-mod impl x n)
  (assume (<= 0 x))
  (assume (< x n))
  (assert (equal? (eval-mod (impl x) n)
                  (modulo (+ x x) n))))

; The functions we want to synthesize, and what subset of the grammar to use
(define (f x)
  (arith x))

(define (g x)
  (arith x #:depth 1))

(define (h x)
  (mod-arith x #:depth 1))

(define (j x)
  (arith x #:depth 2))

; Input space
(define-symbolic x integer?)

; Synthesize
(define solution
  (synthesize
    #:forall (list x)
    #:guarantee (and (spec-id f x)
                     (spec-id-formula f x)
                     (spec-square g x)
                     (spec-square-formula g x)
                     (spec-double-mod h x 12)
                     (spec-random j x)
                     )
    ))

; Results
(if (sat? solution)
  (print-forms solution)
  (display "UNSAT\n"))
