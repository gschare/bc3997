#lang rosette

; Example from Emina Torlak's page about Rosette
; https://emina.github.io/rosette/
(define (interpret formula)
  (match formula
    [`(^, expr ...)  (apply && (map interpret expr))]
    [`(v, expr ...) (apply || (map interpret expr))]
    [`(!, expr)     (! (interpret expr))]
    [lit            (constant lit boolean?)]))

; This implements a SAT solver.
(define (SAT formula)
  (solve (assert (interpret formula))))

(SAT `(^ r o (v s e (! t)) t (! e)))
