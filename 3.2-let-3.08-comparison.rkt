#lang eopl
; Exercise 3.8 [*] Add a numeric equality predicate `equal?` and numeric order predicates `greater?` and `less?`
; These operations also take 2 arguments, but their return values are Bool, so we need to address differently
; Also we no longer distinguish binary op and unary op at the grammer level.

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
;Operation  ::= +|-|*|/|equal?|greater?|less?|minus|zero?

; NOTE: put `op` before `identifier`, otherwise an operation like `minus` will be treated as a `identifier`
(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (op ((or "+" "-" "*" "/" "equal?" "greater?" "less?" "minus" "zero?")) symbol)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (op "(" (separated-list expression ",") ")") op-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
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
  (num-val
   (num number?))
  (bool-val
   (bool boolean?)))

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
      (op-exp (op exps)
              (let ((proc (symbol->proc op)))
                (apply proc (map (lambda (exp) (value-of exp env)) exps))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env)))))))

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
      (bool-val #t)
      (bool-val #f)))

; symbol -> procedure map
(define (symbol->proc s)
  (case s
    ((+) prim-arith+)
    ((-) prim-arith-)
    ((*) prim-arith*)
    ((/) prim-arith/)
    ((minus) prim-minus)
    ((equal?) prim-compare=?)
    ((greater?) prim-compare>?)
    ((less?) prim-compare<?)
    ((zero?) prim-zero?)))

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
;> (run "+(3,2)")
;#(struct:num-val 5)
;> (run "-(3,2)")
;#(struct:num-val 1)
;> (run "*(3,2)")
;#(struct:num-val 6)
;> (run "/(3,2)")
;#(struct:num-val 1)
;> (run "equal?(3,2)")
;#(struct:bool-val #f)
;> (run "greater?(3,2)")
;#(struct:bool-val #t)
;> (run "less?(3,2)")
;#(struct:bool-val #f)
;> (run "minus(3)")
;>  (run "minus(-(minus(5),9))")
;#(struct:num-val 14)
;> (run "zero?(3)")
;#(struct:bool-val #f)
;> (run "zero?(0)")
;#(struct:bool-val #t)
