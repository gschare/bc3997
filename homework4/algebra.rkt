#lang rosette/safe
(require rosette/lib/synthax)   ; grammars
(require rosette/lib/destruct)  ; pattern matching
(require racket/match)

; "Tokens" for the target language
(define-struct plus  (x y) #:transparent)
(define-struct minus (x y) #:transparent)
(define-struct mult  (x y) #:transparent)
(define-struct div   (x y) #:transparent)
(define-struct equal (x y) #:transparent)

; Simple interpreter
(define (interpret e)
  (destruct e
    [(plus a b)  (+ (interpret a) (interpret b))]
    [(minus a b) (- (interpret a) (interpret b))]
    [(mult a b)  (* (interpret a) (interpret b))]
    [(div a b)   (/ (interpret a) (interpret b))]
    [(equal a b) (= (interpret a) (interpret b))]
    [_ e]))

; Grammar for the target language
(define-grammar (algebra x)
  [expr
    (choose (?? integer?)
            x
            (plus (expr) (expr))
            (minus (expr) (expr))
            (mult (expr) (expr))
            (div (expr) (expr))
            (equal (expr) (expr))
            )])

(define (parse s)
  (match s
    [`(+ ,e1 ,e2) (plus  (parse e1) (parse e2))]
    [`(- ,e1 ,e2) (minus (parse e1) (parse e2))]
    [`(* ,e1 ,e2) (mult  (parse e1) (parse e2))]
    [`(/ ,e1 ,e2) (div   (parse e1) (parse e2))]
    [`(= ,e1 ,e2) (equal (parse e1) (parse e2))]
    [e e]))


; Input space
(define-symbolic x y z integer?)

; Expression to solve
; limited to integers
(define (check)
  (assert
    (interpret (parse
      ; `(3 * x = 45)
      `(= (* 3 ,x) 45)
      )
      ))
  (assert
    (interpret (parse
      ; `(10 * x + 12 = 2)
      `(= (+ (* 10 ,y) 12) 2)
      )
      ))
  (assert
    (interpret (parse
      ; `(z = y*x)
      `(= ,z (* ,x ,y))
      )
     ))
  (list x y z)
  )

; Synthesize
(define solution (solve (check)))

; Results
(if (sat? solution)
  (begin (print-forms solution)
         (evaluate (check) solution)
    )
  (display "UNSAT\n"))

