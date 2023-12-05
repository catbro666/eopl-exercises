#lang eopl
; 6.3 CPS transformer (CPS-IN -> CPS-OUT)
; Exercise 6.29 [**] Consider this variant of cps-of-exps.
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ((exps exps) (acc ’()))
      cps-of-rest : Listof(InpExp) × Listof(SimpleExp) → TfExp
      (cond
        ((null? exps) (builder (reverse acc)))
        ((inp-exp-simple? (car exps))
         (cps-of-rest (cdr exps)
                      (cons
                       (cps-of-simple-exp (car exps))
                       acc)))
        (else
         (let ((var (fresh-identifier ’var)))
           (cps-of-exp (car exps)
                       (cps-proc-exp (list var)
                                     (cps-of-rest (cdr exps)
                                                  (cons
                                                   (cps-of-simple-exp (var-exp var))
                                                   acc))))))))))

;Why is this variant of cps-of-exp more efficient than the one in figure 6.8?

; 1. No need to test `inp-exp-simple?` repeatedly, O(n^2) -> O(n)
; 2. Change recursion to iteration.