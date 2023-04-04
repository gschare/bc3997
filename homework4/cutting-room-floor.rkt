; Graveyard of Discontents

; Early attempt at synthesizing lambda calculus
(define-grammar (lc x)
  [expr
    (choose (?? boolean?)
            x
            ('lam (x) (expr))
            ('app (expr) (expr)))])

; I had really no idea what I was doing at this point. This is an early spec.
(define (check-if impl p)
  (define r (impl p 'c 'a))
  (assert (equal? r (if p 'c 'a))))

; I 
(define sol
  (synthesize
    #:forall (list x)
    #:guarantee (begin
                  (assume x)
                  (check-if (lc x)))))

; At first I wanted to restrict my language to Booleans, but more interesting
; applications are in the integer domain.
(define-symbolic x boolean?)

; I recall that at this point in the process, I had given up on copy-pasting
; from the documentation, and I began to experimentally take away pieces of my
; program bit by bit until I found the smallest nugget of a synthesizer that
; still worked. This particular attempt was, unsurprisingly, rather
; unsuccessful.
(synthesize #t)

; Here I am more on the right track, but I later abstracted this to be part of
; the grammar. I struggled to get the syntax for the grammar right, so here I
; was testing if I could put it in the function itself. It turns out you can,
; but it's nicer to do it in the grammar.
(define (f x) (choose ((+) (??) (??))
                      ((*) (??) (??))
                      x
                      (?? integer?)))

; I tried including this in my grammar definition because I saw another
; tutorial doing it, but it ended up being unnecessary.
[op (choose + - *)]

; Another syntax for defining the grammar involves what I believe to be an
; older syntax, `define-synthax`, but I was unable to get it to work. It
; complained with a syntax error despite me taking the idea almost verbatim
; from the documentation.
(define-synthax ops ([(ops) (choose + - *)]))

(define-synthax (arith x depth)
  #:base (choose x (?? integer?))
  #:else (choose
           x
           (?? integer?)
           (
           (choose + - *) (arith x (- depth 1)) (arith x (- depth 1))))
  )

; At first my function holes looked like this:
  (choose (arith x)
          ((choose + * -) (arith x) (arith x))))
; but I didn't know why this worked and nothing else did.
