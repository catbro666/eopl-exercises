#lang eopl
; Exercise 3.24 [**] Use the tricks of the program above to write the pair of
; mutually recursive procedures, odd and even, as in exercise 3.32.

; Note for simplicity, we don't use currying any more as we've already supported multi-arg procedures.

(run "let odd = proc (self other x)
            if (zero? x)
            then false
            else (other other self (- x 1))
    even = proc (self other x)
             if (zero? x)
             then true
             else (other other self (- x 1))
in (cons (odd odd even 1) (even even odd 1))")
