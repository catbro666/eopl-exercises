#lang eopl
; Exercise B.4 [**] Extend language to include variables
; - add an `arith-state` non-termination in the `grammar` definition
;   which includes a variant for setting variable value.
; - add a variant `var-factor` in `arith-factor` to get the variable value.
; - use `,` as the separator of statements, so we can set multiple variable at once.
; - add a `!` as the first token to avoid LL(1) parsing conflict
; - example: !x=2,!y=3,x+y;   ---> 5

(define scanner-spec-1
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (additive-op ((or "+" "-")) symbol)
    (multiplicative-op ((or "*" "/")) symbol)))

(define grammar-1
  '((arith-program
     ((arbno arith-state ",") arith-expr ";")
     program)
    (arith-state
     ("!" identifier "=" arith-expr) ; add a `!` as the first token to avoid LL(1) parsing conflict
     state)
    (arith-expr
     (arith-term (arbno additive-op arith-term))
     expr)
    (arith-term
     (arith-factor (arbno multiplicative-op arith-factor))
     term)
    (arith-factor
     (number)
     num-factor)
    (arith-factor
     ("(" arith-expr ")")
     expr-factor)
    (arith-factor
     (identifier)
     var-factor)))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-1 grammar-1)))
(define just-scan
  (sllgen:make-string-scanner scanner-spec-1 grammar-1))
(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))

; env data structure representation, from Exercise 2.21
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment: ~s" env)))

(define-datatype env-type env?
  (empty-env)
  (extend-env (var symbol?)
              (val (lambda (val) #t))
              (env env?)))
(define (apply-env env search-var)
  (cases env-type env
    (empty-env () (report-no-binding-found search-var))
    (extend-env (var val env) (if (eqv? var search-var)
                                  val
                                  (apply-env env search-var)))))
(define (has-binding? env search-var)
  (cases env-type env
    (empty-env () #f)
    (extend-env (var val env)
                (or (eqv? var search-var)
                    (has-binding? env search-var)))))

(define init-env (empty-env))

; evaluation
(define (value-of-program a-program)
  (cases arith-program a-program
    (program (states expr)
             (value-of-expr expr (value-of-states states init-env)))))

(define (value-of-states states env)
  (fold/l (lambda (env state)
            (value-of-state state env))
          env states))

(define (value-of-state a-state env)
  (cases arith-state a-state
    (state (var expr)
          (extend-env var (value-of-expr expr env) env))))

(define (value-of-expr a-expr env)
  (cases arith-expr a-expr
    (expr (term ops terms)
          (value-of-comb value-of-term term ops terms env))))

(define (value-of-term a-term env)
  (cases arith-term a-term
    (term (factor ops factors)
          (value-of-comb value-of-factor factor ops factors env))))

(define (value-of-factor a-factor env)
  (cases arith-factor a-factor
    (num-factor (num) num)
    (expr-factor (expr) (value-of-expr expr env))
    (var-factor (var) (apply-env env var))))

(define (value-of-comb value-of term ops terms env)
  (fold/l (lambda (res op term)
            ((symbol->proc op) res (value-of term env)))
          (value-of term env) ops terms))

(define (symbol->proc s)
  (case s
    ((+) +)
    ((-) -)
    ((*) *)
    ((/) /)))

; fold/l accumulator on the left
(define (fold/l op init lst1 . lsts)
  (if (null? lst1)
      init
      (apply fold/l op (apply op init (car lst1) (map car lsts)) (cdr lst1) (map cdr lsts))))

; fold/r accumulator on the right
(define (fold/r op init lst1 . lsts)
  (if (null? lst1)
      init
      (apply op (car lst1) (fold/r (lambda (lst args)
                                     (cons (car lst) args))
                                   (list (apply fold/r op init (cdr lst1) (map cdr lsts)))
                                   lsts))))

(define repl
  (sllgen:make-rep-loop "--> " value-of-program
                        (sllgen:make-stream-parser scanner-spec-1 grammar-1)))

; test
;> (repl)
;--> 3;
;3
;--> !x=2, x;
;2
;--> !x=2,!y=3,x+y;
;5
;--> !x=2,!y=1+x,x+y;
