# Homework 3
## Overview
I used SMT to solve the [Zebra Problem](https://en.wikipedia.org/wiki/Zebra_Puzzle),
aka Einstein's Riddle, using the theory of integers.

## Usage
To see the results more easily, solve the problem locally using z3 and pipe the
output into my handy-dandy-hacky Python script like so:

```
z3 -smt2 einstein.lisp | python tabulate.py
```

This is prayer-based parsing, so please check the actual SMT output first.

Alternatively you can run this in any SMT solver that accepts SMT-LIBv2, but
the results may be difficult to see due to the output format.

## Puzzle
The puzzle imagines there are five people, each of which lives next to each
other in a row of houses, each house a different color, and each person has a
preferred drink, pet, and programming language.

The problem is to figure out the correct assignment of each unique thing based
on a few given relationships. For example, we may be given that Barbara Liskov
lives in the first house and that she lives next to the house that is painted
blue. This allows us to fill in some part of our table like so:

| house # | color | resident | animal | beverage | language |
| ------- | ----- | -------- | ------ | -------- | -------- |
|    1    |       | Liskov   |        |          |          |
|    2    | Blue  |          |        |          |          |
|    3    |       |          |        |          |          |
|    4    |       |          |        |          |          |
|    5    |       |          |        |          |          |

To solve the puzzle, we must fill out the whole table by making inferences. It
ends up feeling quite a lot like sudoku.

In the famous version of the problem, the five people are identified by
nationality and they use different brands of cigarettes in lieu of different
programming languages. I detest smoking, so I went with the more thematic
choice and I named each of the people after a famous programming language
designer. Note that each designer's own language is not necessarily their
favorite...

Here is the list of variables in alphabetical order:

| color | resident | animal | beverage | language |
| ----- | -------- | ------ | -------- | -------- |
| Blue  | Church   | Dog    | Coffee   | Erlang   |
| Green | Hopper   | Fox    | Juice    | Haskell  |
| Ivory | Liskov   | Horse  | Milk     | ML       |
| Red   | Ritchie  | Snails | Tea      | OCaml    |
| Yellow | Wadler  | Zebra  | Water    | Racket   |

## Solution
If you'd like to solve the puzzle yourself, go to the Wikipedia page and make
an attempt! Otherwise, the solution is as follows:

| house # | color | resident | animal | beverage | language |
| ------- | ----- | -------- | ------ | -------- | -------- |
|    1    | Yellow | Liskov  | Fox    | Water    | Haskell  |
|    2    | Blue  | Wadler   | Horse  | Tea      | Erlang   |
|    3    | Red   | Church   | Snails | Milk     | OCaml    |
|    4    | Ivory | Ritchie  | Dog    | Juice    | ML       |
|    5    | Green | Hopper   | Zebra  | Coffee   | Racket   |

So there you have it. Liskov prefers Wadler's work to her own; Alonzo Church
believes that OCaml, not Haskell, is the realization of the lambda calculus;
and Dennis Ritchie loves nothing more than relaxing with his dog in his white
house and sipping on orange juice.
The only unsurprising thing here is that Grace Hopper loves Racket, the
teaching language!

## SMT Problem
I have encoded the SMT problem by creating an integer variable for each of the
25 variables above. The integer represents the ordinal number of the house they
belong to. So, if Church lives in House #1, the variable `person-church` would have
value assignment `1`. The theory of integers will allow us to make use of
comparison and arithmetic operators.

I assert that each of the five variables in each category are distinct by using
the `distinct` function:
```lisp
(assert (distinct lang-erlang lang-haskell lang-ml lang-ocaml lang-racket))
```
This
ensures that two people cannot live in the same house, and one person cannot
have two favorite languages, etc. As we all know, every computer scientist has
a favorite language--even if they refuse to tell you what it is.

We must also assert that every variable is between 1 and 5, inclusive. This
ensures that each variable belongs to one of the five houses.
These assertions look like
```lisp
(assert (and (< 0 color-red) (<= color-red 5)))
```

Then, we can begin adding in the "actual" constraints--the hints given by the
puzzle that make it solveable for a human. These are things like "The green
house is immediately to the right of the ivory house," which gets encoded as
```lisp
(assert (= color-green (+ color-ivory 1)))
```
This is where the theory of integers becomes
truly helpful for this problem.

## Results
Once all of the constraints are in, the problem has a unique solution.

The result of `(get-model)` is:

```lisp
sat
(
  (define-fun lang-erlang () Int
    2)
  (define-fun lang-racket () Int
    5)
  (define-fun color-ivory () Int
    4)
  (define-fun drink-water () Int
    2)
  (define-fun pet-horse () Int
    2)
  (define-fun pet-snails () Int
    4)
  (define-fun pet-fox () Int
    1)
  (define-fun drink-juice () Int
    1)
  (define-fun drink-tea () Int
    4)
  (define-fun color-blue () Int
    2)
  (define-fun color-yellow () Int
    3)
  (define-fun color-red () Int
    1)
  (define-fun pet-zebra () Int
    5)
  (define-fun pet-dog () Int
    3)
  (define-fun person-hopper () Int
    5)
  (define-fun lang-ml () Int
    1)
  (define-fun person-liskov () Int
    1)
  (define-fun drink-milk () Int
    3)
  (define-fun lang-haskell () Int
    3)
  (define-fun lang-ocaml () Int
    4)
  (define-fun person-wadler () Int
    4)
  (define-fun drink-coffee () Int
    5)
  (define-fun color-green () Int
    5)
  (define-fun person-ritchie () Int
    3)
  (define-fun person-church () Int
    1)
)
```

Thought it is difficult to tell from just looking, this corresponds to the
correct solution above. The Python script I wrote helps by converting this to a
readable table format. This is what it outputs for me:

```txt
# color      resident   pet        drink      language
- ---------- ---------- ---------- ---------- ----------
1 yellow     liskov     fox        water      haskell
2 blue       wadler     horse      tea        erlang
3 red        church     snails     milk       ocaml
4 ivory      ritchie    dog        juice      ml
5 green      hopper     zebra      coffee     racket
```
