#lang eopl
; Exercise 6.4 [**] Rewrite each of the following procedures in continuation-passing
;style. For each procedure, do this first using a data-structure representation of continuations,
;then with a procedural representation, and then with the inlined procedural
;representation. Last, write the registerized version

; 1. data structure representation
(define (any x) #t)

;; use `any` just because I'm lazy
;(define-datatype continuation continuation?
;  (end-cont)
;  (remove-first-cont (a any) (saved-cont continuation?))
;  (list-sum-cont (a integer?) (saved-cont continuation?))
;  (occurs-free-cont (var symbol?) (param any) (saved-cont continuation?))
;  (subst-cont (new symbol?) (old symbol?) (slist list?) (saved-cont continuation?))
;  (subst-cont2 (saved-car any) (saved-cont continuation?)))
;
;;remove-first : Sym × Listof(Sym) → Listof(Sym)
;(define (remove-first s los)
;  (remove-first/k s los (end-cont)))
;
;(define (remove-first/k s los cont)
;  (if (null? los)
;      (apply-cont cont '())
;      (if (eqv? (car los) s)
;          (apply-cont cont (cdr los))
;          (remove-first/k s (cdr los) (remove-first-cont (car los) cont)))))
;
;;list-sum : Listof(Int) → Int
;(define (list-sum loi)
;  (list-sum/k loi (end-cont)))
;
;(define (list-sum/k loi cont)
;  (if (null? loi)
;      (apply-cont cont 0)
;      (list-sum/k (cdr loi) (list-sum-cont (car loi) cont))))
;
;;occurs-free? : Sym × LcExp → Bool
;;usage: returns #t if the symbol var occurs free in exp, otherwise returns #f.
;(define (occurs-free? var exp)
;  (occurs-free?/k var exp (end-cont)))
;
;(define (occurs-free?/k var exp cont)
;  (cond
;    ((symbol? exp) (apply-cont cont (eqv? var exp))) ; var
;    ((eqv? (car exp) 'lambda) ; one param lambda
;     (if (eqv? var (car (cadr exp)))
;         (apply-cont cont #f)
;         (occurs-free?/k var (caddr exp) cont)))
;    (else (occurs-free?/k var (car exp) (occurs-free-cont var (cadr exp) cont))))) ; call
;
;;subst : Sym × Sym × S-list → S-list
;(define (subst new old slist)
;  (subst/k new old slist (end-cont)))
;
;(define (subst/k new old slist cont)
;  (if (null? slist)
;      (apply-cont cont '())
;      (subst-in-s-exp/k new old (car slist) (subst-cont new old (cdr slist) cont))))
;
;;subst-in-s-exp : Sym × Sym × S-exp → S-exp
;(define (subst-in-s-exp/k new old sexp cont)
;  (if (symbol? sexp)
;      (apply-cont cont (if (eqv? sexp old) new sexp))
;      (subst/k new old sexp cont)))
;
;(define (apply-cont cont val)
;  (cases continuation cont
;    (end-cont () (eopl:printf "End of computation.~%")
;              (eopl:printf "This sentence should appear only once.~%")
;              val)
;    (remove-first-cont (a saved-cont) (apply-cont saved-cont (cons a val)))
;    (list-sum-cont (a saved-cont) (apply-cont saved-cont (+ a val)))
;    (occurs-free-cont (var param saved-cont) (if val
;                                                 (apply-cont saved-cont val)
;                                                 (occurs-free?/k var param saved-cont)))
;    (subst-cont (new old slist saved-cont)
;                (subst/k new old slist (subst-cont2 val saved-cont)))
;    (subst-cont2 (saved-car saved-cont) (apply-cont saved-cont (cons saved-car val)))))

;; 2. procedural representation
;(define (apply-cont cont val)
;  (cont val))
;
;(define (end-cont)
;  (lambda (val)
;    (eopl:printf "End of computation.~%")
;    (eopl:printf "This sentence should appear only once.~%")
;    val))
;
;(define (remove-first-cont a saved-cont)
;  (lambda (val) (apply-cont saved-cont (cons a val))))
;
;(define (list-sum-cont a saved-cont)
;  (lambda (val) (apply-cont saved-cont (+ a val))))
;
;(define (occurs-free-cont var param saved-cont)
;  (lambda (val)
;    (if val
;        (apply-cont saved-cont val)
;        (occurs-free?/k var param saved-cont))))
;
;(define (subst-cont new old slist saved-cont)
;  (lambda (val) (subst/k new old slist (subst-cont2 val saved-cont))))
;
;(define (subst-cont2 saved-car saved-cont)
;  (lambda (val) (apply-cont saved-cont (cons saved-car val))))
;
;;remove-first : Sym × Listof(Sym) → Listof(Sym)
;(define (remove-first s los)
;  (remove-first/k s los (end-cont)))
;
;(define (remove-first/k s los cont)
;  (if (null? los)
;      (apply-cont cont '())
;      (if (eqv? (car los) s)
;          (apply-cont cont (cdr los))
;          (remove-first/k s (cdr los) (remove-first-cont (car los) cont)))))
;
;;list-sum : Listof(Int) → Int
;(define (list-sum loi)
;  (list-sum/k loi (end-cont)))
;
;(define (list-sum/k loi cont)
;  (if (null? loi)
;      (apply-cont cont 0)
;      (list-sum/k (cdr loi) (list-sum-cont (car loi) cont))))
;
;;occurs-free? : Sym × LcExp → Bool
;;usage: returns #t if the symbol var occurs free in exp, otherwise returns #f.
;(define (occurs-free? var exp)
;  (occurs-free?/k var exp (end-cont)))
;
;(define (occurs-free?/k var exp cont)
;  (cond
;    ((symbol? exp) (apply-cont cont (eqv? var exp))) ; var
;    ((eqv? (car exp) 'lambda) ; one param lambda
;     (if (eqv? var (car (cadr exp)))
;         (apply-cont cont #f)
;         (occurs-free?/k var (caddr exp) cont)))
;    (else (occurs-free?/k var (car exp) (occurs-free-cont var (cadr exp) cont))))) ; call
;
;;subst : Sym × Sym × S-list → S-list
;(define (subst new old slist)
;  (subst/k new old slist (end-cont)))
;
;(define (subst/k new old slist cont)
;  (if (null? slist)
;      (apply-cont cont '())
;      (subst-in-s-exp/k new old (car slist) (subst-cont new old (cdr slist) cont))))
;
;;subst-in-s-exp : Sym × Sym × S-exp → S-exp
;(define (subst-in-s-exp/k new old sexp cont)
;  (if (symbol? sexp)
;      (apply-cont cont (if (eqv? sexp old) new sexp))
;      (subst/k new old sexp cont)))

; 3. inlined procedural representation
(define (end-cont)
  (lambda (val)
    (eopl:printf "End of computation.~%")
    (eopl:printf "This sentence should appear only once.~%")
    val))

;remove-first : Sym × Listof(Sym) → Listof(Sym)
(define (remove-first s los)
  (remove-first/k s los (end-cont)))

(define (remove-first/k s los cont)
  (if (null? los)
      (cont '())
      (if (eqv? (car los) s)
          (cont (cdr los))
          (remove-first/k s (cdr los) (lambda (val) (cont (cons (car los) val)))))))

;list-sum : Listof(Int) → Int
(define (list-sum loi)
  (list-sum/k loi (end-cont)))

(define (list-sum/k loi cont)
  (if (null? loi)
      (cont 0)
      (list-sum/k (cdr loi) (lambda (val) (cont (+ (car loi) val))))))

;occurs-free? : Sym × LcExp → Bool
;usage: returns #t if the symbol var occurs free in exp, otherwise returns #f.
(define (occurs-free? var exp)
  (occurs-free?/k var exp (end-cont)))

(define (occurs-free?/k var exp cont)
  (cond
    ((symbol? exp) (cont (eqv? var exp))) ; var
    ((eqv? (car exp) 'lambda) ; one param lambda
     (if (eqv? var (car (cadr exp)))
         (cont #f)
         (occurs-free?/k var (caddr exp) cont)))
    (else (occurs-free?/k var (car exp)
                          (lambda (val)
                            (if val
                                (cont val)
                                (occurs-free?/k var (cadr exp) cont))))))) ; call

;subst : Sym × Sym × S-list → S-list
(define (subst new old slist)
  (subst/k new old slist (end-cont)))

(define (subst/k new old slist cont)
  (if (null? slist)
      (cont '())
      (subst-in-s-exp/k new old (car slist)
                        (lambda (val)
                          (subst/k new old (cdr slist)
                                   (lambda (val2)
                                     (cont (cons val val2))))))))

;subst-in-s-exp : Sym × Sym × S-exp → S-exp
(define (subst-in-s-exp/k new old sexp cont)
  (if (symbol? sexp)
      (cont (if (eqv? sexp old) new sexp))
      (subst/k new old sexp cont)))

; 4. registerized
; skip

;test
(remove-first 2 '(1 2 3))
;(1 3)
(list-sum '(1 2 3))
;6
(occurs-free? 'x 'x) ; #t
(occurs-free? 'x 'y) ; #f
(occurs-free? 'x '(lambda (x) (x y))) ; #f
(occurs-free? 'x '(lambda (y) (x y))) ; #t
(occurs-free? 'x '((lambda (x) x) (x y))) ; #t
(occurs-free? 'x '(lambda (y) (lambda (z) (x (y z))))) ; #t

(subst 'a 'b '((b c) (b () d))) ; ((a c) (a () d))
