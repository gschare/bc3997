# Synthesis of Arithmetic Expressions with Rosette
This was a doozy to complete.

I found the Rosette documentation difficult to understand, and other tutorials
were sparse. Moreover, lots of the documentation and tutorials were out of
date. The result was that I completed the assignment by a large amount of trial
and error.

## TL;DR
* [`main.rkt`](./main.rkt): demonstrates synthesis of arithmetic functions
* [`algebra.rkt`](./algebra.rkt): demonstrates solving algebraic equations
* [`cutting-room-floor.rkt`](./cutting-room-floor.rkt): all my failed attempts
* [`sat.rkt`](./sat.rkt): *not my work!* - Emina Torlak's example

## Overview
Rosette allows you to synthesize programs in a number of ways. Much of the
documentation focuses on verification, sketching, and _angelic execution_. Angelic
execution is a form of synthesis in which one leverages an SMT solver as an
oracle to fill in holes in a sketch of a program.

While the sketching approach is neat, I really wanted my synthesizer to fit the
traditional model:

* Grammar of the target language
* Behavioral specification given as input/ouput examples
* A function to synthesize over a subset of the grammar
* SMT-based synthesis engine producing either a program matching the spec or
  "unsat"

This is how my synthesizer works. I delineated each part of this schematic in
the code comments in my script, [`main.rkt`](./main.rkt).

The function to synthesize is `f`, and its body is just a hole that refers to
the grammar defined earlier in the file.

I also wrote a file demonstrating the use of Rosette for solving algebraic
equations: [`algebra.rkt`](./algebra.rkt). It leverages the `solve` procedure
rather than the `synthesize` procedure, as it is concerned with figuring out
the concrete values of symbolic values rather than filling holes in a sketch.

## Approach ("How did we get here?")
I began by trying out various examples from the documentation, to varying
success. Once I felt I had a grasp of the basics, I looked into defining my own
grammar. I was met with UNSAT after UNSAT, but by looking at the Rosette repo
source code, I eventually pieced together how it is supposed to work. One of
the example I used was Emina Torlak's equivalent of "hello world" in Rosette,
which I have in the repo in the file [`sat.rkt`](./sat.rkt).

For fun, I provided a file,
[`cutting-room-floor.rkt`](./cutting-room-floor.rkt), containing some of my
failed attempts in the form of decontextualized code snippets. I provided
comments that narrate my journey.

The holes feature confused me at first, but some reading and experimentation
clarified that in Rosette, the synthesizer merely attempts to fill in all the
holes of your program. You do not pass the function to synthesize into the
synthesize procedure; it fills all holes at once. This means you can synthesize
multiple functions at once! This did not occur to me until very late in the
process, so I actually had several instances of the solve procedure running in
sequence before I put two and two together and simply passed the implementation
as an argument to the specifications.

I currently target Racket itself for convenience, but I provide a simple
example of how one could target another language and then interpret it to check
against the specification. The alternate language I provide is just modular
arithmetic where the operators have been replaced with words instead of
symbols. This amounts to little more than writing a quick `eval` function and
making sure you interpret the results before comparing them against the spec.
It is easy to extend this, thanks to Rosette's and Racket's flexibility.

At first,
each of the synthesized functions `f`, `g`, `h`, and `j` would produce `UNSAT` if I
did not give them a choice between the starting rule of the grammar and a
binary operation with each operand being a grammar rule. I have no idea why
this was the case. It's probably a mistake in my grammar. In any case, I
checked the documentation and found that you could add a `#:depth` argument to
a hole, and this seems to have fixed the issue. You can see the cutting room
floor file for the earlier versions.

The synthesizer occasionally comes up with somewhat hilarious solutions to the
problems, for example producing the function `h(x) = -22x` for doubling the
argument modulo 12. Since `-22` is indeed `2` modulo 12, this actually works.

## Takeaways
I appreciate the flexibility of Rosette. I ended up only using the safe subset
out of fear of making debugging even more difficult in the full featured
version, but I can see how access to the full power of Racket makes this a very
competent language for making SDSLs.

In the future I would like to explore the use of Rosette for angelic execution
and verification. I would like to look at more of Emina Torlak's work, as well
as that of her students.
