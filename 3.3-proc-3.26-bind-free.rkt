#lang eopl
; Exercise 3.26 [**]  In our data-structure representation of procedures, we have kept the entire environment
; in the closure. But of course all we need are the bindings for the free variables.
; Modify the representation of procedures to retain only the free variables.

; filter the env according to the body of the procedure and eliminate duplicate variables.
; our data structure representation of environment is hard to iterate. Moreover,
; the `define-datatype` is very limited, for example, we can't `cases` two values at the same time.
; so finally we choose not to use `define-datatype` to represent the environment


;ExpVal = Int+Bool+Null+Pair+Proc
;DenVal = Int+Bool+Null+Pair+Proc
 
;syntax
;Program    ::= Expression
;               a-program (exp1)
;Expression ::= Number
;               const-exp (num)
;Expression ::= if Expression then Expression else Expression
;               if-exp (exp1 exp2 exp3)
;Expression ::= Identifier
;               var-exp (var)
;Expression ::= let {Identifier = Expression}* in Expression
;               let-exp (vars exps body)
;Expression ::= let* {Identifier = Expression}* in Expression
;               let*-exp (vars exps body)
;Expression ::= cond {Expression ==> Expression}∗ end
;               cond-exp (preds actions)
;Expression ::= unpack {Identifier}∗ = Expression in Expression
;               unpack-exp (vars exp1 exp2)
;Expression ::= proc ({Identifier}*) Expression
;               proc-exp (vars body)
;Expression ::= (Expression {Expression}*)
;               call-exp (rator rands)
;Operation  ::= +|-|*|/|equal?|greater?|less?|minus|cons|car|cdr|null?|list|print


; wonder why scanner-spec2 doesn't work
;(define special '("+" "-" "*" "/" "?"))
;(define scanner-spec2
;  `((white-sp (whitespace) skip)
;    (comment ("%" (arbno (not #\newline))) skip)
;    (identifier ((or letter ,@special) (arbno (or letter digit ,@special))) symbol)
;    (number (digit (arbno digit)) number)))

(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier ((or letter "+" "-" "*" "/" "?") (arbno (or letter digit "+" "-" "*" "/" "?"))) symbol)
    (number (digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("emptylist") null-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(" expression  (arbno expression) ")") call-exp)
    ))

(sllgen:make-define-datatypes scanner-spec grammar)
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec grammar)))
(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar))
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

(define identifier? symbol?)

;; Expressed values for the PROC
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (null-val)
  (pair-val (car expval?) (cdr expval?))
  (proc-val (proc proc?)))

; procedure
(define-datatype proc proc?
  (compound (vars (list-of identifier?)) (body expression?) (env env?))
  (primitive (name identifier?) (op procedure?)))

; used by print
(define (expval->sexp val)
  (cases expval val
    (num-val (num) num)
    (bool-val (bool) bool)
    (null-val () '())
    (pair-val (a d) (cons (expval->sexp a) (expval->sexp d)))
    (proc-val (a-proc) (cases proc a-proc
                         (compound (vars body env) (string->symbol "#<procedure>"))
                         (primitive (name op) (string->symbol (string-append "#<primitive:"
                                                                             (symbol->string name) ">")))))))

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

;expval->proc : ExpVal → Proc
(define (expval->proc val)
  (cases expval val
    (proc-val (proc) proc)
    (else (report-expval-extractor-error 'proc val))))

;expval->list : ExpVal → List
;convert only 1 layer. If val is not a list-val, reports error
(define (expval->list val)
  (cases expval val
    (null-val () '())
    (pair-val (a d) (cons a (expval->list d)))
    (else (report-expval-extractor-error 'list val))))

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
        (and (pair? l) (pred (car l)) (new-pred (cdr l)))))
  new-pred)

; any: predicate that always returns true
(define (any val) #t)

(define (binding? b) (and (pair? b) (identifier? (car b))))

(define (check-arg-type name pred arg)
  (if (pred arg)
      #t
      (eopl:error 'check-arg-type "expected ~s, got ~s" name arg)))

(define (empty-env) '(environment ()))
(define (env? x) (and (pair? x) (eq? (car x) 'environment) ((list-of binding?) (cadr x))))
(define (env-bindings env)
  (check-arg-type 'env? env? env)
  (cadr env))

(define (extend-env var val env)
  (check-arg-type 'identifier? identifier? var)
  (check-arg-type 'env? env? env)
  (list 'environment (cons (cons var val) (env-bindings env))))
  
(define (scan-env env search-var onsucc onfail)
  (check-arg-type 'env? env? env)
  (let ((b (ormap (lambda (b) (if (eqv? (car b) search-var) b #f)) (env-bindings env))))
    (if b (onsucc b) (onfail search-var))))

; if found, return the val; otherwise report error
(define (apply-env env search-var)
  (scan-env env search-var cdr report-no-binding-found))

; if found, returns the binding; otherwise returns #f
(define (lookup-binding env search-var)
  (scan-env env search-var (lambda (b) b) (lambda (v) #f)))

; merge multiple envs, eliminate the duplicate bindings 
(define (merge-envs env1 env2 . envs)
  (check-arg-type 'env? env? env1)
  (check-arg-type 'env? env? env2)
  (check-arg-type 'list-of-env? (list-of env?) envs)
  (define (merge-bindings bs1 bs2)
    (cond
      ((null? bs1) bs2)
      ((null? bs2) bs1)
      (else (fold/l (lambda (bs b) (if (assq (car b) bs)
                                       bs
                                       (cons b bs)))
                    bs1 bs2))))
  (list 'environment
        (fold/l (lambda (bs env)
                  (merge-bindings bs (env-bindings env)))
                (merge-bindings (env-bindings env1) (env-bindings env2))
                envs)))

; TODO: check duplicate vars
(define (extend-env+ vars vals env)
  (if (null? vars)
      env
      (extend-env+ (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))

(define (extend-env* vars exps env)
  (if (null? vars)
      env
      (extend-env* (cdr vars) (cdr exps) (extend-env (car vars) (value-of (car exps) env) env))))

; filter the env to keep only the bindings for the free variables of the expresison
; note for let-exp/let*-exp/proc ..., we need to add those vars into bound variables
(define (filter-env vars exp env)
  (let loop ((vars vars)
             (exp exp))
    (cases expression exp
      (const-exp (num) (empty-env))
      (var-exp (var) (if (memq var vars)
                         (empty-env)
                         (let ((b (lookup-binding env var)))
                           (if b (extend-env var (cdr b) (empty-env)) (empty-env)))))
      (if-exp (exp1 exp2 exp3) (merge-envs (loop vars exp1) (loop vars exp2) (loop vars exp3)))
      (let-exp (vars2 exps body) (merge-envs (apply merge-envs (map (lambda (exp) (loop vars exp)) exps))
                                            (loop (append vars vars2) body)))
      (let*-exp (vars2 exps body) (fold/l (lambda (env&vars var exp)
                                                        (cons (merge-envs (car env&vars)
                                                                          (loop (cdr env&vars) exp))
                                                              (cons var (cdr env&vars))))
                                                      (cons (loop (append vars vars2) body) vars)
                                                      vars2 exps))
      (null-exp () (empty-env))
      (cond-exp (preds actions) (apply merge-envs (map (lambda (exp) (loop vars exp)) (append preds actions))))
      (unpack-exp (vars2 exp1 body) (merge-envs (loop vars exp1) (loop (append vars vars2) body)))
      (proc-exp (vars2 body) (loop (append vars vars2) body))
      (call-exp (rator rands) (fold/l (lambda (env rand)
                                        (merge-envs env (loop vars rand)))
                                      (loop vars rator)
                                      rands))
      )))

;init-env : () → Env
;usage: (init-env) = [i=1,v=5,x=10,true=true,false=false,+=.,-=.,...]
(define (init-env)
  (extend-env+ '(i v x  true false)
                (list (num-val 1) (num-val 5) (num-val 10) true false)
     (fold/l (lambda (env p)
               (let ((name (car p))
                     (op (cdr p)))
                 (extend-env name (proc-val (primitive name op)) env))) (empty-env) primitives)))

; evaluation
;run : String → ExpVal ->Sexp
(define (run string)
  (expval->sexp (value-of-program (scan&parse string))))

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
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (vars exps body)
               (value-of body
                         (extend-env+ vars (value-of-explist exps env) env)))
      (let*-exp (vars exps body)
                (value-of body
                         (extend-env* vars exps env)))
      (null-exp () (null-val))
      (cond-exp (preds actions)
                (value-of-cond preds actions env))
      (unpack-exp (vars exp1 body)
                  (let* ((lst (value-of exp1 env))
                         (vals (expval->list lst)))
                    (if (equal-length? vars vals)
                        (value-of body (extend-env+ vars vals env))
                        (eopl:error 'unpack "the length of the list doesn't match the number of variables"))))
      (proc-exp (vars body) (proc-val (compound vars body (filter-env vars body env))))
      (call-exp (rator rands)
                (let ((a-proc (expval->proc (value-of rator env)))
                      (args (value-of-explist rands env)))
                  (apply-procedure a-proc args)))
      )))

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

(define (apply-procedure proc1 args)
  (cases proc proc1
    (compound (vars body env)
               (if (equal-length? vars args)
                   (value-of body (extend-env+ vars args env))
                   (eopl:error 'apply-procedure "arity mismatch, expected ~s, got ~s"
                               (length vars) (length args))))
    (primitive (name op) (apply op args))))

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

(define primitives
  (list (cons '+ prim-arith+)
        (cons '- prim-arith-)
        (cons '* prim-arith*)
        (cons '/ prim-arith/)
        (cons 'minus prim-minus)
        (cons 'equal? prim-compare=?)
        (cons 'greater? prim-compare>?)
        (cons 'less? prim-compare<?)
        (cons 'zero? prim-zero?)
        (cons 'cons prim-cons)
        (cons 'car prim-car)
        (cons 'cdr prim-cdr)
        (cons 'null? prim-null?)
        (cons 'list prim-list)
        (cons 'print prim-print)))

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

(define (andmap op lst)
  (let loop ((lst lst))
    (if (null? lst)
        #t
        (and (op (car lst)) (loop (cdr lst))))))

(define (ormap op lst)
  (let loop ((lst lst))
    (if (null? lst)
        #f
        (or (op (car lst)) (loop (cdr lst))))))

(define (equal-length? l1 l2)
  (= (length l1) (length l2)))

(define repl
  (sllgen:make-rep-loop "--> " value-of-program
                        (sllgen:make-stream-parser scanner-spec grammar)))

; test
;> (run "3")
;3
;> (run "x")
;10
;> (run "if (zero? 0) then i else x")
;1
;> (run "if (zero? 1) then i else x")
;10
;> (run "let a = 2 x = 5 in (cons a x)")
;(2 . 5)
;> (run "let* a = 2 b = (+ a 1) in (cons b x)")
;(3 . 10)
;> (run "emptylist")
;()
;> (run "unpack a b c = (list 1 2 3) in (list a b c)")
;(1 2 3)
;> (run "(proc (x) x 2)")
;2
;> (run "(cons 1 x)")
;(1 . 10)
;> (run "let f = proc (x y) (+ x y) in (f 3 1)")
;4
;> (run "let makerec = proc (f)
;                      (proc (h) (h h)
;                       proc (h) (f proc (x) ((h h) x)))
;      in let maketimes4 = proc (f)
;                            proc (x)
;                              if (zero? x)
;                              then 0
;                              else (+ (f (- x 1)) 4)
;         in let times4 = (makerec maketimes4)
;            in (times4 3)
;      ")
;12