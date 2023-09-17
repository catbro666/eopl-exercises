#lang eopl
; Exercise 3.23 [**]  Use Currying to write a procedure for factorial in PROC
; Note our procedure is based on the PROC Language in Exercise 3.22
; Currying: takes a procedure and returns another procedure that takes more arguments 

(run "let times = proc (maker)
                    proc (x)
                      proc (y)
                        if (zero? x)
                        then 0
                        else (+ (((maker maker) (- x 1)) y) y)
      in let makefact = proc (maker)
                          proc (x)
                            if (zero? x)
                            then 1
                            else (((times times) x) ((maker maker) (- x 1)))
         in ((makefact makefact) 4)")
