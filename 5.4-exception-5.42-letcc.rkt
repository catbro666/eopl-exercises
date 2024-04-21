#lang eopl
; Exception (based on Exercise 5.40)

;Exercise 5.42 [**] Add to the language the ability to capture a continuation anywhere
; by adding the form letcc Identifier in Expression with the specification
;(value-of/k (letcc var body) ρ cont)
;= (value-of/k body (extend-env var cont ρ) cont)

; Such a captured continuation may be invoked with `throw`: the expression
;`throw Expression to Expression` evaluates the two subexpressions. The second expression
;should return a continuation, which is applied to the value of the first expression.
;The current continuation of the `throw` expression is ignored.

;Bounce = ExpVal ∪ (() → Bounce)
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
;Expression ::= proc ({Identifier}*) Expression
;               proc-exp (vars body)
;Expression ::= traceproc ({Identifier}*) Expression
;               traceproc-exp (vars body)
;Expression ::= begin Expression {Expression}∗ end
;               begin-exp (exp1 exps)
;Expression ::= try Expression catch (Identifier Identifier) Expression
;               try-exp (exp1 var1 var2 handler-exp)
;Expression ::= raise Expression
;               raise-exp (exp1)
;Expression ::= resume Identifier Expression
;               resume-exp (cont-var exp1)
;Expression ::= letcc Identifier in Expression
;               letcc-exp (var exp1)
;Expression ::= throw Expression to Expression
;               throw-exp (exp1 exp2)
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
    (expression ("try" expression "catch" "(" identifier identifier ")" expression) try-exp)
    (expression ("raise" expression) raise-exp)
    (expression ("resume" identifier expression) resume-exp)
    (expression ("letcc" identifier expression) letcc-exp)
    (expression ("throw" expression "to" expression) throw-exp)
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
  (proc-val (proc proc?))
  (cont-val (cont continuation?)))

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
                                                                             (symbol->string name) ">")))))
    (cont-val (cont) (string->symbol "#<continuation>"))))

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

;expval->cont : ExpVal → Cont
(define (expval->cont val)
  (cases expval val
    (cont-val (cont) cont)
    (else (report-expval-extractor-error 'cont val))))

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

; ====environment====
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

; ====evaluation====
;run : String → ExpVal ->Sexp
(define (run string)
  (expval->sexp (value-of-program (scan&parse string))))

;value-of-program : Program → FinalAnswer
(define (value-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (exp1)
               (trampoline (value-of/k exp1 (init-env) (end-cont))))))

;trampoline : Bounce → FinalAnswer
(define (trampoline bounce)
  (if (expval? bounce)
      bounce
      (trampoline (bounce))))

(define bounce? any)

;value-of/k : Exp × Env × Cont → Bounce
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (deref (apply-env env var))))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env
                          (if-test-cont exp2 exp3 env cont (get-saved-try-cont cont))))
      (let-exp (vars exps body)
               (value-of-explist/k exps '() env
                                   (explist-final-cont vars body env cont (get-saved-try-cont cont))))
      (let*-exp (vars exps body)
                (value-of-explist*/k vars exps env
                                     (explist*-final-cont body cont (get-saved-try-cont cont))))
      (letrec-exp (p-names b-varss p-bodys letrec-body)
                  (value-of-explist-rec/k p-names b-varss p-bodys env
                                          (explist-rec-final-cont letrec-body cont (get-saved-try-cont cont))))
      (null-exp () (apply-cont cont (null-val)))
      (cond-exp (preds actions)
                (value-of-cond/k preds actions env cont))
      (unpack-exp (vars exp1 body)
                  (value-of/k exp1 env
                              (unpack-exp-cont vars body env cont (get-saved-try-cont cont))))
      (proc-exp (vars body) (apply-cont cont (proc-val (compound vars body env #f))))
      (traceproc-exp (vars body) (apply-cont cont (proc-val (compound vars body env #t))))
      (begin-exp (exp1 exps)
                 (value-of-begin/k exp1 exps env cont))
      (try-exp (exp1 var1 var2 handler-exp)
               (value-of/k exp1 env (try-cont var1 var2 handler-exp env cont)))
      (raise-exp (exp1)
                 (value-of/k exp1 env (raise-cont cont (get-saved-try-cont cont))))
      (resume-exp (cont-var exp1)
                  (let* ((cont-val (deref (apply-env env cont-var)))
                         (cont2 (expval->cont cont-val)))
                    (value-of/k exp1 env (resume-cont cont2 (get-saved-try-cont cont))))) ;TBD: which try-cont to use?
      (letcc-exp (var exp1)
                 (value-of/k exp1 (extend-env var cont env) cont))
      (throw-exp (exp1 exp2)
                 (value-of/k exp1 env (throw-cont exp2 env cont (get-saved-try-cont cont))))
      (call-exp (rator rands)
                (value-of/k rator env
                            (rator-cont rands env cont (get-saved-try-cont cont))))
      )))

;====continuation====
(define-datatype continuation continuation?
  (end-cont)
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (explist-final-cont
   (vars (list-of identifier?))
   (body expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (explist-cont
   (exps (list-of expression?))
   (vals (list-of bounce?))
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (explist*-final-cont
   (body expression?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (explist*-cont
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (explist-rec-final-cont
   (body expression?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (cond-exp-cont
   (preds (list-of expression?))
   (actions (list-of expression?))
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (unpack-exp-cont
   (vars (list-of identifier?))
   (body expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (begin-exp-cont
    (exps (list-of expression?))
    (saved-env env?)
    (saved-cont continuation?)
    (saved-try-cont continuation?))
  (rator-cont
   (rands (list-of expression?))
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (rands-cont
   (proc1 proc?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (trace-cont
   (trace boolean?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (try-cont
   (var1 identifier?)
   (var2 identifier?)
   (handler-exp expression?)
   (saved-env env?)
   (saved-cont continuation?))
  (raise-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (resume-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (throw-cont
   (exp2 expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (throw-cont2
   (saved-val any)
   (saved-try-cont continuation?)))

;apply-cont : Cont × ExpVal → Bounce
(define (apply-cont cont val)
  (cases continuation cont
    (end-cont () (eopl:printf "End of computation.~%") val)
    (if-test-cont (exp2 exp3 saved-env saved-cont saved-try-cont)
                  (if (expval->bool val)
                      (value-of/k exp2 saved-env saved-cont)
                      (value-of/k exp3 saved-env saved-cont)))
    (explist-final-cont (vars body saved-env saved-cont saved-try-cont)
                        (value-of/k body (extend-env+ vars val saved-env) saved-cont))
    (explist-cont (exps vals saved-env saved-cont saved-try-cont)
                  (value-of-explist/k exps (cons val vals) saved-env saved-cont))
    (explist*-final-cont (body saved-cont saved-try-cont)
                         (value-of/k body val saved-cont))
    (explist*-cont (vars exps saved-env saved-cont saved-try-cont)
                   (value-of-explist*/k (cdr vars) exps (extend-env (car vars) val saved-env) saved-cont))
    (explist-rec-final-cont (body saved-cont saved-try-cont)
                            (value-of/k body val saved-cont))
    (cond-exp-cont (preds actions saved-env saved-cont saved-try-cont)
                   (if (equal? true val)
                       (value-of/k (car actions) saved-env saved-cont)
                       (value-of-cond/k preds (cdr actions) saved-env saved-cont)))
    (unpack-exp-cont (vars body saved-env saved-cont saved-try-cont)
                     (let ((vals (expval->list val)))
                       (if (equal-length? vars vals)
                           (value-of/k body (extend-env+ vars vals saved-env) saved-cont)
                           (eopl:error 'unpack "the length of the list doesn't match the number of variables"))))
    (begin-exp-cont (exps saved-env saved-cont saved-try-cont)
                    (value-of-begin/k (car exps) (cdr exps) saved-env saved-cont))
    (rator-cont (rands saved-env saved-cont saved-try-cont)
                (let ((rator-proc (expval->proc val)))
                  (value-of-explist/k rands '() saved-env
                                      (rands-cont rator-proc saved-cont saved-try-cont))))
    (rands-cont (proc1 saved-cont saved-try-cont)
                (apply-procedure/k proc1 val saved-cont))
    (trace-cont (trace saved-cont saved-try-cont)
                (if trace (display "exit procedure\n") #t)
                (apply-cont saved-cont val))
    (try-cont (var1 var2 handler-exp saved-env saved-cont)
              (apply-cont saved-cont val))
    (raise-cont (saved-cont saved-try-cont)
                (apply-handler val saved-cont saved-try-cont))
    (resume-cont (saved-cont saved-try-cont)
                 (apply-cont saved-cont val))
    (throw-cont (exp2 saved-env saved-cont saved-try-cont)
                (value-of/k exp2 saved-env (throw-cont2 val saved-try-cont)))
    (throw-cont2 (saved-val saved-try-cont)
                 (apply-cont val saved-val))))

(define (get-saved-try-cont cont)
  (cases continuation cont
    (end-cont () cont)
    (if-test-cont (exp2 exp3 saved-env saved-cont saved-try-cont) saved-try-cont)
    (explist-final-cont (vars body saved-env saved-cont saved-try-cont) saved-try-cont)
    (explist-cont (exps vals saved-env saved-cont saved-try-cont) saved-try-cont)
    (explist*-final-cont (body saved-cont saved-try-cont) saved-try-cont)
    (explist*-cont (vars exps saved-env saved-cont saved-try-cont) saved-try-cont)
    (explist-rec-final-cont (body saved-cont saved-try-cont) saved-try-cont)
    (cond-exp-cont (preds actions saved-env saved-cont saved-try-cont) saved-try-cont)
    (unpack-exp-cont (vars body saved-env saved-cont saved-try-cont) saved-try-cont)
    (begin-exp-cont (exps saved-env saved-cont saved-try-cont) saved-try-cont)
    (rator-cont (rands saved-env saved-cont saved-try-cont) saved-try-cont)
    (rands-cont (proc1 saved-cont saved-try-cont) saved-try-cont)
    (trace-cont (trace saved-cont saved-try-cont) saved-try-cont)
    (try-cont (var1 var2 handler-exp saved-env saved-cont) cont)
    (raise-cont (saved-cont saved-try-cont) saved-try-cont)
    (resume-cont (saved-cont saved-try-cont) saved-try-cont)
    (throw-cont (exp2 saved-env saved-cont saved-try-cont) saved-try-cont)
    (throw-cont2 (saved-val saved-try-cont) saved-try-cont)
    ))

;apply-handler : ExpVal × Cont → FinalAnswer
(define (apply-handler val cont saved-try-cont)
  (cases continuation saved-try-cont
    (try-cont (var1 var2 handler-exp saved-env saved-cont)
              (value-of/k handler-exp (extend-env var2 (cont-val cont) (extend-env var1 val saved-env)) saved-cont))
    (end-cont () (report-uncaught-exception))
    (else (report-invalid-try-continuation))))

(define (report-uncaught-exception)
  (eopl:error 'apply-handler "uncaught exception!"))

(define (report-invalid-try-continuation)
  (eopl:error 'apply-handler "internal error! not a expected continuation. "))

; ListOf(Exp) × Env × Cont → ListOf(FinalAnswer)
(define (value-of-explist/k exps vals env cont)
  (if (null? exps)
      (apply-cont cont (reverse vals))
      (value-of/k (car exps) env (explist-cont (cdr exps) vals env cont (get-saved-try-cont cont)))))

(define (value-of-explist*/k vars exps env cont)
  (if (null? exps)
      (apply-cont cont env)
      (value-of/k (car exps) env (explist*-cont vars (cdr exps) env cont (get-saved-try-cont cont)))))

(define (value-of-explist-rec/k p-names b-varss bodys env cont)
  (let* ((vecs (map (lambda (n) (make-vector 1)) p-names))
         (new-env (fold/l (lambda (env name vec) (extend-env name vec env)) env p-names vecs)))
    (for-each (lambda (vec b-vars body)
                (vector-set! vec 0 (proc-val (compound b-vars body new-env #f))))
              vecs b-varss bodys)
    (apply-cont cont new-env)))

(define (value-of-cond/k preds actions env cont)
  (if (null? preds)
      (eopl:error 'value-of-cond/k "none of the cond predicates succeed")
      (value-of/k (car preds) env
                  (cond-exp-cont (cdr preds) actions env cont (get-saved-try-cont cont)))))

(define (value-of-begin/k exp1 exps env cont)
  (if (null? exps)
      (value-of/k exp1 env cont)
      (value-of/k exp1 env (begin-exp-cont exps env cont (get-saved-try-cont cont)))))

(define (check-arity vars args)
  (let ((l1 (length vars))
        (l2 (length args)))
    (if (not (= l1 l2))
        (eopl:error 'apply-procedure "arity mismatch, expected ~s, got ~s" l1 l2)
        #t)))

;apply-procedure/k : Proc × ExpVal × Cont → Bounce
(define (apply-procedure/k proc1 args cont)
  (lambda ()
    (cases proc proc1
      (compound (vars body env trace)
                (if trace (display "enter procedure\n") #t)
                (check-arity vars args)
                (value-of/k body (extend-env+ vars args env)
                            (trace-cont trace cont (get-saved-try-cont cont))))
      (primitive (name op) (apply-cont cont (apply op args))))))

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

; ====primitives====
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

; ====utils====
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
(run "if (equal? 0 0) then (+ 1 1) else (+ 2 2)")
;2
(run "if (equal? 0 1) then (+ 1 1) else (+ 2 2)")
;4
(run "i")
;1
(run "cons")
;|#<primitive:cons>|
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
;(2 . 2)
;(run "cond (zero? 1) ==> (cons 1 1)
;           (zero? 1) ==> (cons 2 2) end")
;[error] value-of-cond/k: none of the cond predicates succeed
(run "unpack a b c = (list (+ 0 0) (+ 1 1) (+ 2 2)) in (list a b c)")
;(0 2 4)
(run "let f=proc(x) (* x 2) in
        (list (f 1) (f 2))")
;(2 4)
(run "begin (print 1) (print 2) 3 end")
;1 2 3
(run "let div=proc(x y) if (zero? y)
                        then raise 0
                        else (/ x y)
      in (div 6 2)")
;3
;(run "let div=proc(x y) if (zero? y)
;                        then raise 0
;                        else (/ x y)
;      in (div 6 0)")
;;apply-handler: uncaught exception!
(run "let div=proc(x y) if (zero? y)
                        then raise 0
                        else (/ x y)
      in try (div 6 0)
           catch (x cont) -1")
;-1
(run "let div=proc(x y) if (zero? y)
                        then raise 0
                        else (/ x y)
      in try (cons (div 6 2) (div 6 0))
           catch (x cont) resume cont -1")
;(3 . -1)
(run "letcc cont (+ 1 1)")
;2
(run "letcc cont throw (+ 2 2) to cont")
;4