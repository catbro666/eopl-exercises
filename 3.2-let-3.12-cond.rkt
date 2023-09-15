#lang eopl
; Exercise 3.12 [**] Add to the defined language a facility that adds a cond expression.
; Use the grammar `Expression ::= cond {Expression ==> Expression}∗ end`

; nothing special

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
;Expression ::= let Identifier = Expression in Expression
;               let-exp (var exp1 body)
;Expression ::= cond {Expression ==> Expression}∗ end
;Operation  ::= +|-|*|/|equal?|greater?|less?|minus|cons|car|cdr|null?|list

; NOTE: we change `op` from symbol to string, otherwise some `op`s such as `cons` will be treated as `identifier`s 
(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (op ((or "+" "-" "*" "/" "equal?" "greater?" "less?" "minus" "zero?"
             "cons" "car" "cdr" "null?" "list")) string)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (op "(" (separated-list expression ",") ")") op-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
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
                (apply proc (map (lambda (arg) (value-of arg env)) args))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (null-exp () (null-val))
      (cond-exp (preds actions)
                (value-of-cond preds actions env)))))

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
    (("list") prim-list)))

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
;> (run "cond zero?(0) ==> i greater?(2, 1) ==> 3 end")
;#(struct:num-val 1)
;> (run "cond zero?(1) ==> 2 greater?(2, 1) ==> v end")
;#(struct:num-val 5)
;> (run "cond zero?(1) ==> 2 greater?(2, 3) ==> v end")
;value-of-cond: none of the cond predicates succeed