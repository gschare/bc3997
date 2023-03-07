; Variable declarations
; I thought it would be more fun to use names of famous programming language designers
(declare-fun person-church  () Int) ; englishman
(declare-fun person-hopper  () Int) ; japanese
(declare-fun person-liskov  () Int) ; norwegian
(declare-fun person-ritchie () Int) ; spaniard
(declare-fun person-wadler  () Int) ; ukrainian

(declare-fun color-blue   () Int)
(declare-fun color-green  () Int)
(declare-fun color-ivory  () Int)
(declare-fun color-red    () Int)
(declare-fun color-yellow () Int)

(declare-fun drink-coffee () Int)
(declare-fun drink-juice  () Int)
(declare-fun drink-milk   () Int)
(declare-fun drink-tea    () Int)
(declare-fun drink-water  () Int)

(declare-fun pet-dog    () Int)
(declare-fun pet-fox    () Int)
(declare-fun pet-horse  () Int)
(declare-fun pet-snails () Int)
(declare-fun pet-zebra  () Int)

; I don't like smoking, so I went with functional programming languages instead
(declare-fun lang-erlang  () Int) ; chesterfields
(declare-fun lang-haskell () Int) ; kools
(declare-fun lang-ml      () Int) ; lucky strike
(declare-fun lang-ocaml   () Int) ; old gold
(declare-fun lang-racket  () Int) ; parliaments

; Constraints
(assert (distinct person-church person-hopper person-liskov person-ritchie person-wadler))
(assert (distinct color-blue color-green color-ivory color-red color-yellow))
(assert (distinct drink-coffee drink-juice drink-milk drink-tea drink-water))
(assert (distinct pet-dog pet-fox pet-horse pet-snails pet-zebra))
(assert (distinct lang-erlang lang-haskell lang-ml lang-ocaml lang-racket))

(assert (and (< 0 person-church) (<= person-church 5)))
(assert (and (< 0 person-hopper) (<= person-hopper 5)))
(assert (and (< 0 person-liskov) (<= person-liskov 5)))
(assert (and (< 0 person-ritchie) (<= person-ritchie 5)))
(assert (and (< 0 person-wadler) (<= person-wadler 5)))

(assert (and (< 0 color-blue) (<= color-blue 5)))
(assert (and (< 0 color-green) (<= color-green 5)))
(assert (and (< 0 color-ivory) (<= color-ivory 5)))
(assert (and (< 0 color-red) (<= color-red 5)))
(assert (and (< 0 color-yellow) (<= color-yellow 5)))

(assert (and (< 0 drink-coffee) (<= drink-coffee 5)))
(assert (and (< 0 drink-juice) (<= drink-juice 5)))
(assert (and (< 0 drink-milk) (<= drink-milk 5)))
(assert (and (< 0 drink-tea) (<= drink-tea 5)))
(assert (and (< 0 drink-water) (<= drink-water 5)))

(assert (and (< 0 pet-dog) (<= pet-dog 5)))
(assert (and (< 0 pet-fox) (<= pet-fox 5)))
(assert (and (< 0 pet-horse) (<= pet-horse 5)))
(assert (and (< 0 pet-snails) (<= pet-snails 5)))
(assert (and (< 0 pet-zebra) (<= pet-zebra 5)))

(assert (and (< 0 lang-erlang) (<= lang-erlang 5)))
(assert (and (< 0 lang-haskell) (<= lang-haskell 5)))
(assert (and (< 0 lang-ml) (<= lang-ml 5)))
(assert (and (< 0 lang-ocaml) (<= lang-ocaml 5)))
(assert (and (< 0 lang-racket) (<= lang-racket 5)))

; puzzle hints
(assert (= person-church color-red)) ; Alonzo Church lives in the red house
(assert (= person-ritchie pet-dog)) ; Dennis Ritchie owns the dog
(assert (= drink-coffee color-green)) ; coffee is drunk in the green house
(assert (= person-wadler drink-tea)) ; Philip Wadler drinks tea
(assert (= color-green (+ color-ivory 1))) ; the green house is immediately to the right of the ivory house
(assert (= lang-ocaml pet-snails)) ; the OCaml programmer owns snails
(assert (= lang-haskell color-yellow)) ; Haskell is programmed in the yellow house
(assert (= drink-milk 3)) ; milk is drunk in the middle house
(assert (= person-liskov 1)) ; Barbara Liskov lives in the first house
(assert (or (= lang-erlang (+ pet-fox 1)) (= lang-erlang (- pet-fox 1)))) ; The computer scientist who programs in Erlang lives next to the computer scientist with the fox
(assert (or (= lang-haskell (+ pet-horse 1)) (= lang-haskell (- pet-horse 1)))) ; Haskell is programmed in the house next to the house where the horse is kept
(assert (= lang-ml drink-juice)) ; The ML programmer drinks orange juice
(assert (= person-hopper lang-racket)) ; Grace Hopper programs in Racket
(assert (or (= person-liskov (+ color-blue 1)) (= person-liskov (- color-blue 1)))) ; Barbara Liskov lives next to the blue house

; Solve
(check-sat)
(get-model)
