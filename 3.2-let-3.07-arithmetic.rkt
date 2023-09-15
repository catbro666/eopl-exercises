#lang eopl
; Exercise 3.7 [*] Add operators for addition, multiplication, and integer quotient.
; Add a new token type `BinaryOp` which includes +-*/

;syntax
;Program    ::= Expression
;               a-program (exp1)
;Expression ::= Number
;               const-exp (num)
;Expression ::= BinaryOp (Expression , Expression)
;               binop-exp (op exp1 exp2)
;Expression ::= zero? (Expression)
;               zero?-exp (exp1)
;Expression ::= if Expression then Expression else Expression
;               if-exp (exp1 exp2 exp3)
;Expression ::= Identifier
;               var-exp (var)
;Expression ::= let Identifier = Expression in Expression
;               let-exp (var exp1 body)
;Expression ::= minus (Expression)
;               minus-exp (exp1)
;BinaryOp   ::= +|-|*|/

(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (binop ((or "+" "-" "*" "/")) symbol)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (binop "(" expression "," expression ")") binop-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("minus" "(" expression ")") minus-exp)
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
      (binop-exp (op exp1 exp2)
                (let ((proc (symbol->proc op))
                      (val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val
                     (proc num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (if (zero? num1)
                         (bool-val #t)
                         (bool-val #f)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (var exp1 body)
               (let ((val1 (value-of exp1 env)))
                 (value-of body
                           (extend-env var val1 env))))
      (minus-exp (exp1)
                 (let* ((val1 (value-of exp1 env))
                        (num1 (expval->num val1)))
                   (num-val (- num1)))))))

(define (symbol->proc s)
  (case s
   ((+) +)
   ((-) -)
   ((*) *)
   ((/) quotient)))

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
;> (run "-(3,2)")
;#(struct:num-val 1)
;> (run "+(3,2)")
;#(struct:num-val 5)
;> (run "*(3,2)")
;#(struct:num-val 6)
;> (run "/(3,2)")
;#(struct:num-val 1)
