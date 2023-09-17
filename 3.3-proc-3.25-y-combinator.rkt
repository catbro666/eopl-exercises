#lang eopl
; Exercise 3.25 [*] UThe tricks of the previous exercises can be generalized to show that
; we can define any recursive procedure in PROC.
; This is actually the famous Y-combinator.

; below is the code in the book
(run "let makerec = proc (f)
                      let d = proc (x)
                               proc (z) ((f (x x)) z)
                      in proc (n) ((f (d d)) n)
      in let maketimes4 = proc (f)
                            proc (x)
                              if (zero? x)
                              then 0
                              else (+ (f (- x 1)) 4)
         in let times4 = (makerec maketimes4)
            in (times4 3)")
;12

; actually we can simplify it
; let's look at the `makerec`. `f` is any recusive procedure that must takes a parameter
; in order to implement recursion, so its form is like
; proc (f)
;   proc (x) ... (f (- x 1))...

; the code above actually has a repeating pattern.
; the value of `(d d)` is `proc (z) ((f (d d)) z)`
; which is exactly the same as `proc (n) ((f (d d)) n)`
; and `proc (n) ((f (d d)) n)` is the same as `(f (d d))`.
; We don't need to calcuate `(d d)` in every recusion step.
; Actually the parameter of `f` the key procedure to implement recursion
; which should always behave as `((f ?) x)` when being called, i.e.
; `(? x)` should be equal to `((f ?) x)`
; 1. we start to modify `makerec`
; let makerec = proc (f)
;                 let g = proc (x) ((f g) x)
;                 in (f g)
; 2. again, a repeating pattern `(f g)` appears, and `g` can't reference `g` itself
;    we can implement recursion by passing itself as an arugment
;    `proc (h) (h h)`
; let makerec = proc (f)
;                 let g = proc (x) ((h h) x)
;                 in (f g)
; 3. so what `h` should be? `(h h)` should be equal to `(f g)` 
; `proc (h) (f g)` -->  proc (h) (f proc (x) ((h h) x))
;
; let makerec = proc (f)
;                 let h = proc (h) (f proc (x) ((h h) x))
;                 in (h h)
; or, we can remove the local variable
; let makerec = proc (f)
;                 (proc (h) (h h)
;                  proc (h) (f proc (x) ((h h) x)))

(run "let makerec = proc (f)
                      (proc (h) (h h)
                       proc (h) (f proc (x) ((h h) x)))
      in let maketimes4 = proc (f)
                            proc (x)
                              if (zero? x)
                              then 0
                              else (+ (f (- x 1)) 4)
         in let times4 = (makerec maketimes4)
            in (times4 3)
      ")

; essentially it's still recursion by passing the procedure itself through the arguments,
; except that the procedure becomes a higher order procedure and the parameter-passing is 
; done in the Y-combinator so users don't have to pass explicitly when calling the procedure.
