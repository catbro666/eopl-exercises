#lang eopl
; Imperative Interpreter (based on 5.11 version)

;Exercise 5.25 [**] Registerize the interpreter for multiargument procedures (exercise 3.21).

;procedures communicate via shared registers: exp, env, cont, val and proc1. 

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
;Expression ::= letrec {Identifier ({Identifier}*) = Expression}* in Expression
;               letrec-exp (p-names b-varss p-bodys letrec-body)
;Expression ::= cond {Expression ==> Expression}∗ end
;               cond-exp (preds actions)
;Expression ::= unpack {Identifier}∗ = Expression in Expression
;               unpack-exp (vars exp1 exp2)
;Expression ::= proc ({Identifier}*) Expression5.3-imperative-interpreter-0.base.rkt 
;               proc-exp (vars body)
;Expression ::= traceproc ({Identifier}*) Expression
;               traceproc-exp (vars body)
;Expression ::= begin Expression {Expression}∗ end
;               begin-exp (exp1 exps)
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
    (identifier ((or letter "*" "/" "?") (arbno (or letter digit "+" "-" "*" "/" "?"))) symbol)
    (identifier ((or "+" "-")) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression) letrec-exp)
    (expression ("emptylist") null-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("traceproc" "(" (arbno identifier) ")" expression) traceproc-exp)
    (expression ("begin" expression (arbno expression) "end") begin-exp)
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
  (compound (vars (list-of identifier?)) (body expression?) (env env?) (trace boolean?))
  (primitive (name identifier?) (op procedure?)))

; used by print
(define (expval->sexp val)
  (cases expval val
    (num-val (num) num)
    (bool-val (bool) bool)
    (null-val () '())
    (pair-val (a d) (cons (expval->sexp a) (expval->sexp d)))
    (proc-val (a-proc) (cases proc a-proc
                         (compound (vars body env trace)
                                   (if trace
                                       (string->symbol "#<traceproc>")
                                       (string->symbol "#<procedure>")))
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

; ****environment****
(define env? (list-of pair?))

(define (empty-env) '())

(define (extend-env var val saved-env)
  (cons (cons var (newref val)) saved-env))

(define (apply-env env search-var)
  (let loop ((env env))
    (if (null? env)
        (report-no-binding-found search-var)
        (let ((var (caar env))
              (val (cdar env)))
          (if (eqv? var search-var)
              val
              (loop (cdr env)))))))

; TODO: check duplicate vars
(define (extend-env+ vars vals env)
  (if (null? vars)
      env
      (extend-env+ (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))

;init-env : () → Env
;usage: (init-env) = [i=1,v=5,x=10,true=true,false=false,+=.,-=.,...]
(define (init-env)
  (extend-env+ '(i v x  true false)
               (list (num-val 1) (num-val 5) (num-val 10) true false)
               (fold/l (lambda (env p)
                         (let ((name (car p))
                               (op (cdr p)))
                           (extend-env name (proc-val (primitive name op)) env))) (empty-env) primitives)))

; ****evaluation****
;run : String → ExpVal ->Sexp
(define (run string)
  (expval->sexp (value-of-program (scan&parse string))))

(define exp 'uninitialized)
(define env 'uninitialized)
(define cont 'uninitialized)
(define val 'uninitialized)
(define proc1 'uninitialized)

;value-of-program : Program → ExpVal
(define (value-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (exp1)
               (set! cont (end-cont))
               (set! exp exp1)
               (set! env (init-env))
               (value-of/k))))

;value-of/k : () → FinalAnswer
;relies on registers
;exp : Exp
;env : Env
;cont : Cont
(define value-of/k
  (lambda ()
    (cases expression exp
      (const-exp (num)
                 (set! val (num-val num))
                 (apply-cont))
      (var-exp (var)
               (set! val (deref (apply-env env var)))
               (apply-cont))
      (if-exp (exp1 exp2 exp3)
              (set! cont (if-test-cont exp2 exp3 env cont))
              (set! exp exp1)
              (value-of/k))
      (let-exp (vars exps body)
               (set! cont (let-exp-cont vars body env cont))
               (set! exp exps)
               (set! val '())
               (value-of-explist/k))
      (let*-exp (vars exps body)
                (set! cont (let*-exp-cont vars exps body env cont))
                (set! exp exps)
                (value-of-explist*/k))
      (letrec-exp (p-names b-varss p-bodys letrec-body)
                  (set! exp letrec-body)
                  (value-of-explist-rec/k p-names b-varss p-bodys))
      (null-exp ()
                (set! val (null-val))
                (apply-cont))
      (cond-exp (preds actions)
                (set! cont (cond-exp-cont preds actions env cont))
                (set! exp preds)
                (value-of-cond/k))
      (unpack-exp (vars exp1 body)
                  (set! cont (unpack-exp-cont vars body env cont))
                  (set! exp exp1)
                  (value-of/k))
      (proc-exp (vars body)
                (set! val (proc-val (compound vars body env #f)))
                (apply-cont))
      (traceproc-exp (vars body)
                     (set! val (proc-val (compound vars body env #t)))
                     (apply-cont))
      (begin-exp (exp1 exps)
                 (set! cont (begin-exp-cont exps env cont))
                 (set! exp exp1)
                 (value-of/k))
      (call-exp (rator rands)
                (set! cont (rator-cont rands env cont))
                (set! exp rator)
                (value-of/k))
      )))

;====continuation====
(define-datatype continuation continuation?
  (end-cont)
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (saved-env env?)
   (saved-cont continuation?))
  (let-exp-cont
   (vars (list-of identifier?))
   (body expression?)
   (saved-env env?)
   (saved-cont continuation?))
  (explist-cont
   (exps (list-of expression?))
   (vals (list-of expval?))
   (saved-env env?)
   (saved-cont continuation?))
  (let*-exp-cont
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?)
   (saved-env env?)
   (saved-cont continuation?))
  (cond-exp-cont
   (preds (list-of expression?))
   (actions (list-of expression?))
   (saved-env env?)
   (saved-cont continuation?))
  (unpack-exp-cont
   (vars (list-of identifier?))
   (body expression?)
   (saved-env env?)
   (saved-cont continuation?))
  (begin-exp-cont
    (exps (list-of expression?))
    (saved-env env?)
    (saved-cont continuation?))
  (rator-cont
   (rands (list-of expression?))
   (saved-env env?)
   (saved-cont continuation?))
  (rands-cont
   (val1 expval?)
   (saved-cont continuation?))
  (trace-cont
   (trace boolean?)
   (saved-cont continuation?)))

;apply-cont : Cont × ExpVal → FinalAnswer
;relies registers
;cont : Cont
;val  : ExpVal
(define (apply-cont)
  (cases continuation cont
    (end-cont () (eopl:printf "End of computation.~%") val)
    (if-test-cont (exp2 exp3 saved-env saved-cont)
                  (set! cont saved-cont)
                  (if (expval->bool val)
                      (set! exp exp2)
                      (set! exp exp3))
                  (set! env saved-env)
                  (value-of/k))
    (let-exp-cont (vars body saved-env saved-cont)
                  (set! cont saved-cont)
                  (set! env (extend-env+ vars val saved-env))
                  (set! exp body)
                  (value-of/k))
    (explist-cont (exps vals saved-env saved-cont)
                  (set! cont saved-cont)
                  (set! env saved-env)
                  (set! exp exps)
                  (set! val (cons val vals))
                  (value-of-explist/k))
    (let*-exp-cont (vars exps body saved-env saved-cont)
                   (if (null? vars)
                       (begin (set! cont saved-cont)
                              (set! env saved-env)
                              (set! exp body)
                              (value-of/k))
                       (begin (set! env (extend-env (car vars) val saved-env))
                              (set! cont (let*-exp-cont (cdr vars) (cdr exps) body env saved-cont))
                              (set! exp (cdr exps))
                              (value-of-explist*/k))))
    (cond-exp-cont (preds actions saved-env saved-cont)
                   (if (equal? true val)
                       (begin (set! exp (car actions))
                              (set! env saved-env)
                              (set! cont saved-cont)
                              (value-of/k))
                       (begin (set! cont (cond-exp-cont (cdr preds) (cdr actions) saved-env saved-cont))
                              (set! env saved-env)
                              (set! exp (cdr preds))
                              (value-of-cond/k))))
    (unpack-exp-cont (vars body saved-env saved-cont)
                     (let ((vals (expval->list val)))
                       (if (equal-length? vars vals)
                           (begin (set! cont saved-cont)
                                  (set! env (extend-env+ vars vals saved-env))
                                  (set! exp body)
                                  (value-of/k))
                           (eopl:error 'unpack "the length of the list doesn't match the number of variables"))))
    (begin-exp-cont (exps saved-env saved-cont)
                    (if (null? exps)
                        (begin (set! cont saved-cont)
                               (set! env saved-env)
                               (apply-cont))
                        (begin (set! cont (begin-exp-cont (cdr exps) saved-env saved-cont))
                               (set! env saved-env)
                               (set! exp (car exps))
                               (value-of/k))))
    (rator-cont (rands saved-env saved-cont)
                (set! cont (rands-cont val saved-cont))
                (set! exp rands)
                (set! env saved-env)
                (set! val '())
                (value-of-explist/k))
    (rands-cont (rator-val saved-cont)
                (let ((rator-proc (expval->proc rator-val)))
                  (set! cont saved-cont)
                  (set! proc1 rator-proc)
                  (set! val val)
                  (apply-procedure/k)))
    (trace-cont (trace saved-cont)
                (if trace (display "exit procedure\n") #t)
                (set! cont saved-cont)
                (apply-cont))))

;value-of-explist/k : () → FinalAnswer
;relies on registers
;exp : ListOf(Exp)
;env : Env
;cont : Cont
;val : ListOf(ExpVal)
(define (value-of-explist/k)
  (if (null? exp)
      (begin (set! val (reverse val))
             (apply-cont))
      (begin (set! cont (explist-cont (cdr exp) val env cont))
             (set! exp (car exp))
             (value-of/k))))

;value-of-explist*/k : () → FinalAnswer
;relies on registers
;exp : ListOf(Exp)
;env : Env
;cont : Cont
(define (value-of-explist*/k)
  (if (null? exp)
      (apply-cont)
      (begin (set! exp (car exp))
             (value-of/k))))

;value-of-explist-rec/k : () → FinalAnswer
;relies on registers
;exp : Exp
;env : Env
;cont : Cont
(define (value-of-explist-rec/k p-names b-varss p-bodys)
  (let* ((vecs (map (lambda (n) (make-vector 1)) p-names))
         (new-env (fold/l (lambda (env name vec) (extend-env name vec env)) env p-names vecs)))
    (for-each (lambda (vec b-vars body)
                (vector-set! vec 0 (proc-val (compound b-vars body new-env #f))))
              vecs b-varss p-bodys)
    (set! env new-env)
    (value-of/k)))

;value-of-cond/k : () → FinalAnswer
;relies on registers
;exp : ListOf(Exp)
;env : Env
;cont : Cont
(define (value-of-cond/k)
  (if (null? exp)
      (eopl:error 'value-of-cond/k "none of the cond predicates succeed")
      (begin (set! exp (car exp))
             (value-of/k))))

(define (check-arity vars args)
  (let ((l1 (length vars))
        (l2 (length args)))
    (if (not (= l1 l2))
        (eopl:error 'apply-procedure "arity mismatch, expected ~s, got ~s" l1 l2)
        #t)))

;apply-procedure/k : () → FinalAnswer
;proc1 : Proc
;val : ListOf(ExpVal)
;cont : Cont
(define (apply-procedure/k)
  (cases proc proc1
    (compound (vars body saved-env trace)
              (if trace (display "enter procedure\n") #t)
              (check-arity vars val)
              (set! cont (trace-cont trace cont))
              (set! env (extend-env+ vars val saved-env))
              (set! exp body)
              (value-of/k))
    (primitive (name op)
               (set! val (apply op val))
               (apply-cont))))

; ====store====
(define the-store 'uninitialized)

;empty-store : () → Sto
(define (empty-store) '())

;get-store : () → Sto
(define (get-store) the-store)

;initialize-store! : () → Unspecified
(define (initialize-store!)
  (set! the-store (empty-store)))

;reference? : SchemeVal → Bool
(define reference? integer?)

;newref : ExpVal → Ref
(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val))) ; note the `append` here
    next-ref))

;deref : Ref → ExpVal
(define (deref ref)
  (let ((val (list-ref the-store ref)))
    (if (vector? val)
        (vector-ref val 0)
        val)))

;setref! : Ref × ExpVal → Unspecified
;usage: sets the-store to a state like the original, but with position ref containing val.
(define (setref! ref val)
  (set! the-store
        (letrec
            ((setref-inner
              ;usage: returns a list like store1, except that position ref1 contains val.
              (lambda (store1 ref1)
                (cond
                  ((null? store1)
                   (report-invalid-reference ref the-store))
                  ((zero? ref1)
                   (cons val (cdr store1)))
                  (else
                   (cons
                    (car store1)
                    (setref-inner
                     (cdr store1) (- ref1 1))))))))
          (setref-inner the-store ref))))

(define (report-invalid-reference ref store)
  (eopl:error 'setref! "invalid reference ~s" ref))

; ****primitives****
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

; ****utils****
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

(define (filter pred lst . lsts)
  (reverse (apply fold/l (lambda (res e . l)
                           (if (apply pred e l)
                               (cons e res)
                               res))
                  '() lst lsts)))

(define (equal-length? l1 l2)
  (= (length l1) (length l2)))

(define repl
  (sllgen:make-rep-loop "--> " value-of-program
                        (sllgen:make-stream-parser scanner-spec grammar)))

; test
(run "1")
;1
(run "i")
;1
(run "cons")
;|#<primitive:cons>|
(run "(+ 1 1)")
;2
(run "if (equal? 0 0) then (+ 1 1) else (+ 2 2)")
;2
(run "if (equal? 0 1) then (+ 1 1) else (+ 2 2)")
;4
(run "let i=2 v=(+ i 1) a=v in (list i v a x)")
;(2 2 5 10)
(run "let* i=2 v=(+ i 1) a=v in (list i v a x)")
;(2 3 3 10)
(run "letrec even(x) = if (zero? x) then true else (odd (- x 1))
               odd(x) = if (zero? x) then false else (even (- x 1))
        in (list (odd 3) (even 3))")
;(#t #f)
(run "emptylist")
;()
(run "cond (zero? 0) ==> (cons 1 1)
           (zero? 0) ==> (cons 2 2) end")
;(1 . 1)
(run "cond (zero? 1) ==> (cons 1 1)
           (zero? 0) ==> (cons 2 2) end")
;;(2 . 2)
;(run "cond (zero? 1) ==> (cons 1 1)
;           (zero? 1) ==> (cons 2 2) end")
;;[error] value-of-cond/k: none of the cond predicates succeed
(run "unpack a b c = (list (+ 0 0) (+ 1 1) (+ 2 2)) in (list a b c)")
;(0 2 4)
(run "let f=proc(x) (* x 2) in
        (list (f 1) (f 2))")
;(2 4)
(run "begin (print 1) (print 2) 3 end")
;1 2 3
