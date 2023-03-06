; Variable declarations
; I thought it would be more fun to use names of famous programming language designers
(declare-fun church  () Int) ; englishman
(declare-fun hopper  () Int) ; japanese
(declare-fun liskov  () Int) ; norwegian
(declare-fun ritchie () Int) ; spaniard
(declare-fun wadler  () Int) ; ukrainian

(declare-fun blue   () Int)
(declare-fun green  () Int)
(declare-fun ivory  () Int)
(declare-fun red    () Int)
(declare-fun yellow () Int)

(declare-fun coffee () Int)
(declare-fun juice  () Int)
(declare-fun milk   () Int)
(declare-fun tea    () Int)
(declare-fun water  () Int)

(declare-fun dog    () Int)
(declare-fun fox    () Int)
(declare-fun horse  () Int)
(declare-fun snails () Int)
(declare-fun zebra  () Int)

; I don't like smoking, so I went with functional programming languages instead
(declare-fun erlang  () Int) ; chesterfields
(declare-fun haskell () Int) ; kools
(declare-fun ml      () Int) ; lucky strike
(declare-fun ocaml   () Int) ; old gold
(declare-fun racket  () Int) ; parliaments

; Constraints
(assert (distinct church hopper liskov ritchie wadler))
(assert (distinct blue green ivory red yellow))
(assert (distinct coffee juice milk tea water))
(assert (distinct dog fox horse snails zebra))
(assert (distinct erlang haskell ml ocaml racket))

(assert (and (< 0 church) (<= church 5)))
(assert (and (< 0 hopper) (<= hopper 5)))
(assert (and (< 0 liskov) (<= liskov 5)))
(assert (and (< 0 ritchie) (<= ritchie 5)))
(assert (and (< 0 wadler) (<= wadler 5)))

(assert (and (< 0 blue) (<= blue 5)))
(assert (and (< 0 green) (<= green 5)))
(assert (and (< 0 ivory) (<= ivory 5)))
(assert (and (< 0 red) (<= red 5)))
(assert (and (< 0 yellow) (<= yellow 5)))

(assert (and (< 0 coffee) (<= coffee 5)))
(assert (and (< 0 juice) (<= juice 5)))
(assert (and (< 0 milk) (<= milk 5)))
(assert (and (< 0 tea) (<= tea 5)))
(assert (and (< 0 water) (<= water 5)))

(assert (and (< 0 dog) (<= dog 5)))
(assert (and (< 0 fox) (<= fox 5)))
(assert (and (< 0 horse) (<= horse 5)))
(assert (and (< 0 snails) (<= snails 5)))
(assert (and (< 0 zebra) (<= zebra 5)))

(assert (and (< 0 erlang) (<= erlang 5)))
(assert (and (< 0 haskell) (<= haskell 5)))
(assert (and (< 0 ml) (<= ml 5)))
(assert (and (< 0 ocaml) (<= ocaml 5)))
(assert (and (< 0 racket) (<= racket 5)))

; puzzle hints
(assert (= church red)) ; Alonzo Church lives in the red house
(assert (= ritchie dog)) ; Dennis Ritchie owns the dog
(assert (= coffee green)) ; coffee is drunk in the green house
(assert (= wadler tea)) ; Philip Wadler drinks tea
(assert (= green (+ ivory 1))) ; the green house is immediately to the right of the ivory house
(assert (= ocaml snails)) ; the OCaml programmer owns snails
(assert (= haskell yellow)) ; Haskell is programmed in the yellow house
(assert (= milk 3)) ; milk is drunk in the middle house
(assert (= liskov 1)) ; Barbara Liskov lives in the first house
(assert (or (= erlang (+ fox 1)) (= erlang (- fox 1)))) ; The computer scientist who programs in Erlang lives next to the computer scientist with the fox
(assert (or (= haskell (+ horse 1)) (= haskell (- horse 1)))) ; Haskell is programmed in the house next to the house where the horse is kept
(assert (= ml juice)) ; The ML programmer drinks orange juice
(assert (= hopper racket)) ; Grace Hopper programs in Racket
(assert (or (= liskov (+ blue 1)) (= liskov (- blue 1)))) ; Barbara Liskov lives next to the blue house

; Solve
(check-sat)
(get-model)
