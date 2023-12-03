; CPS-OUT Interpreter
;Exercise 6.19 [**] Write a Scheme procedure tail-form? that takes the syntax tree of
;a program in CPS-IN, expressed in the grammar of figure 6.3, and determines whether
;the same string would be in tail form according to the grammar of figure 6.5.
;
(define (tail-form? pgm)
  (cases program pgm
         (a-program (exp1)
                    (tail-form-exp? exp1))))

(define (tail-form-exp? exp)
  (cases expression exp
         (if-exp (exp1 exp2 exp3)
                 (and (simple-exp? exp1)
                      (tail-form-exp? exp2)
                      (tail-form-exp? exp3)))
         (let-exp (vars rhss body)
                  (and (andmap simple-exp? rhss)
                       (tail-form-exp? body)))
         (letrec-exp (p-names b-varss p-bodies letrec-body)
                     (and (andmap tail-form-exp? p-bodies)
                          (tail-form-exp? letrec-body)))
         (call-exp (rator rands)
                   (and (simple-exp? rator)
                        (andmap simple-exp? rands)))
         (else (simple-exp? exp))))

(define (simple-exp? exp)
  (cases expression exp
         (const-exp (num) #t)
         (var-exp (var) #t)
         (diff-exp (exp1 exp2)
                   (and (simple-exp? exp1)
                        (simple-exp? exp2)))
         (zero?-exp (exp1) (simple-exp? exp1))
         (proc-exp (vars body) (tail-form-exp? body))
         (else #f)))

