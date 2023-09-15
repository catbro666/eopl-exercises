#lang eopl
; Exercise 3.16 [**] Extend the language so that a `let` declaration can declare an arbitrary number of variables,
; using the grammar `Expression ::= let {Identifier = Expression}∗ in Expression`

; Nothing special, just add extend-env+

;syntax
;Program    ::= Expression
;               a-program (exp1)
;Expression ::= Number
;               const-exp (num)
;Expression ::= Operation ( {Expression}*, )
;               op-exp (op exp1 exp2)
;Expression ::= if Expression then Expression else Expression
;               if-exp (exp1 exp2 exp3)
;Expression ::= Identifier
;               var-exp (var)
;Expression ::= let {Identifier = Expression}* in Expression
;               let-exp (vars exps body)
;Expression ::= cond {Expression ==> Expression}∗ end
;Operation  ::= +|-|*|/|equal?|greater?|less?|minus|cons|car|cdr|null?|list|print

; NOTE: we change `op` from symbol to string, otherwise some `op`s such as `cons` will be treated as `identifier`s 
(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (op ((or "+" "-" "*" "/" "equal?" "greater?" "less?" "minus" "zero?"
             "cons" "car" "cdr" "null?" "list" "print")) string)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (op "(" (separated-list expression ",") ")") op-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("emptylist") null-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    ))

(sllgen:make-define-datatypes scanner-spec grammar)
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec grammar)))
(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar))
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

;; Expressed values for the LET
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (null-val)
  (pair-val (car expval?) (cdr expval?)))

;expval->num : ExpVal → Int
(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))))

;expval->bool : ExpVal → Bool
(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))))

(define true (bool-val #t))
(define false (bool-val #f))

(define (report-expval-extractor-error expect val)
  (eopl:error 'expval->extractor "Bad expval: expected a ~s, got ~s" expect val))

; env data structure representation, from Exercise 2.21
(define (report-no-binding-found search-var)
  (eopl:error 'apply-env "No binding for ~s" search-var))
(define (report-invalid-env env)
  (eopl:error 'apply-env "Bad environment: ~s" env))

; list-of: takes a predicate and generates a new predicate
; Pred -> Pred
(define (list-of pred)
  (define (new-pred l)
    (if (null? l)
        #t
        (and (pred (car l)) (new-pred (cdr l)))))
  new-pred)

; any: predicate that always returns true
(define (any val) #t)

(define-datatype env-type env?
  (empty-env)
  (extend-env (var symbol?)
              (val any)
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
(define (extend-env+ vars vals env)
  (cond
    ((null? vars) (if (null? vals)
                      env
                      (eopl:error 'extend-env+ "to many arguments")))
    ((null? vals) (eopl:error 'extend-env+ "too few arguments"))
    (else (extend-env+ (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env)))))

;init-env : () → Env
;usage: (init-env) = [i=1,v=5,x=10]
(define (init-env)
  (extend-env
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10)
     (empty-env)))))

; evaluation
;run : String → ExpVal
(define (run string)
  (value-of-program (scan&parse string)))

;value-of-program : Program → ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-env)))))

;value-of : Exp × Env → ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (op-exp (op args)
              (let ((proc (symbol->proc op)))
                (apply proc (value-of-explist args env))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (vars exps body)
               (value-of body
                         (extend-env* vars (value-of-explist exps env) env)))
      (null-exp () (null-val))
      (cond-exp (preds actions)
                (value-of-cond preds actions env)))))

; ListOf(Exp) × Env → ListOf(ExpVal)
(define (value-of-explist exps env)
  (map (lambda (exp) (value-of exp env)) exps))

(define (value-of-cond preds actions env)
  (define (iter preds actions)
    (cond
      ((null? preds) (eopl:error 'value-of-cond "none of the cond predicates succeed"))
      ((equal? true (value-of (car preds) env)) (value-of (car actions) env))
      (else (iter (cdr preds) (cdr actions)))))
  (iter preds actions))

; primitives
; arithmetic operations
; ExpVal(Int) × ExpVal(Int) → ExpVal(Int)
(define (prim-arith+ val1 val2)
  (arith-bin + val1 val2))

(define (prim-arith- val1 val2)
  (arith-bin - val1 val2))

(define (prim-arith* val1 val2)
  (arith-bin * val1 val2))

(define (prim-arith/ val1 val2)
  (arith-bin quotient val1 val2))

(define (arith-bin proc val1 val2)
  (let ((num1 (expval->num val1))
        (num2 (expval->num val2)))
    (num-val (proc num1 num2))))

(define (prim-minus val1)
  (num-val (- (expval->num val1))))

; comparison operations
; ExpVal(Int) × ExpVal(Int) → ExpVal(Bool)
(define (prim-compare=? val1 val2)
  (compare-ex = val1 val2))

(define (prim-compare>? val1 val2)
  (compare-ex > val1 val2))

(define (prim-compare<? val1 val2)
  (compare-ex < val1 val2))

(define (compare-ex proc val1 val2)
  (let ((num1 (expval->num val1))
        (num2 (expval->num val2)))
    (bool-val (proc num1 num2))))

; ExpVal(Int) → ExpVal(Bool)
(define (prim-zero? val1)
  (if (zero? (expval->num val1))
      true
      false))

; list operations
; ExpVal(Any) × ExpVal(Any) → ExpVal(Pair)
(define (prim-cons val1 val2)
  (pair-val val1 val2))

; ExpVal(Pair) → ExpVal(Any)
(define (prim-car val)
  (cases expval val
    (pair-val (a d) a)
    (else (report-expval-extractor-error 'pair val))))

(define (prim-cdr val)
  (cases expval val
    (pair-val (a d) d)
    (else (report-expval-extractor-error 'pair val))))

; ExpVal(Any) → ExpVal(Bool)
(define (prim-null? val)
  (cases expval val
    (null-val () true)
    (else false)))

; () → ExpVal(Null)
; { ExpVal(Any) }+ → ExpVal(Pair)
(define (prim-list . lov)
  (define (iter l)
    (if (null? l)
        (null-val)
        (pair-val (car l) (iter (cdr l)))))
  (iter lov))

; ExpVal(Any) → print and returns 1
(define (prim-print val)
  (let ((sexp (expval->sexp val)))
    (display sexp)
    (newline)
    (num-val 1)))

(define (expval->sexp val)
  (cases expval val
    (num-val (num) num)
    (bool-val (bool) bool)
    (null-val () '())
    (pair-val (a d) (cons (expval->sexp a) (expval->sexp d)))))

; symbol -> procedure map
(define (symbol->proc s)
  (case s
    (("+") prim-arith+)
    (("-") prim-arith-)
    (("*") prim-arith*)
    (("/") prim-arith/)
    (("minus") prim-minus)
    (("equal?") prim-compare=?)
    (("greater?") prim-compare>?)
    (("less?") prim-compare<?)
    (("zero?") prim-zero?)
    (("cons") prim-cons)
    (("car") prim-car)
    (("cdr") prim-cdr)
    (("null?") prim-null?)
    (("list") prim-list)
    (("print") prim-print)))

; utils
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
                        (sllgen:make-stream-parser scanner-spec grammar)))

; test
;> (run "let x=1 in +(x, 2)")
;#(struct:num-val 3)
;> (run "let x=1 y=2 in +(x, y)")
;#(struct:num-val 3)
;> (run "let in +(1, 2)")
;#(struct:num-val 3)
