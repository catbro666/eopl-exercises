#lang eopl
; Lexical Addressing
; Exercise 3.42 [***] Modify the lexical address translator and interpreter to use the trimmed representation
; of procedures from exercise 3.26. For this, you will need to translate the body of the procedure not
; (extend-senv var senv), but in a new static environment that tells exactly where each variable will be kept
; in the trimmed representation.

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
;Expression ::= (Expression {Expression}*)
;               call-exp (rator rands)
;Expression ::= %lexref number
;               nameless-var-exp (num)
;Expression ::= %let {Expression}* in Expression
;               nameless-let-exp (exps body)
;Expression ::= %let* {Expression}* in Expression
;               nameless-let*-exp (exps body)
;Expression ::= %letrec {Expression}* in Expression
;               nameless-letrec-exp (p-bodys letrec-body)
;Expression ::= %unpack Expression in Expression
;               nameless-unpack-exp (exp1 exp2)
;Expression ::= %lexproc Expression {Number}*
;               nameless-proc-exp (body indices)
;Expression ::= %lextraceproc Expression {Number}*
;               nameless-traceproc-exp (body indices)
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
    (expression ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression) letrec-exp)
    (expression ("emptylist") null-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("traceproc" "(" (arbno identifier) ")" expression) traceproc-exp)
    (expression ("(" expression  (arbno expression) ")") call-exp)
    (expression ("%lexref" number) nameless-var-exp)
    (expression ("%let" (arbno expression) "in" expression) nameless-let-exp)
    (expression ("%let*" (arbno expression) "in" expression) nameless-let*-exp)
    (expression ("%letrec" (arbno expression) "in" expression) nameless-letrec-exp)
    (expression ("%unpack" expression "in" expression) nameless-unpack-exp)
    (expression ("%lexproc" (arbno number) "in" expression) nameless-proc-exp)
    (expression ("%lextraceproc" (arbno number) "in" expression) nameless-traceproc-exp)
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
  (compound (body expression?) (saved-nameless-env nameless-environment?) (trace boolean?))
  (primitive (name identifier?) (op procedure?)))

; used by print
(define (expval->sexp val)
  (cases expval val
    (num-val (num) num)
    (bool-val (bool) bool)
    (null-val () '())
    (pair-val (a d) (cons (expval->sexp a) (expval->sexp d)))
    (proc-val (a-proc) (cases proc a-proc
                         (compound (body env trace)
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

; static environment
; Senv= Listof(Sym)
; Lexaddr = N
(define (report-unbound-var var)
  (eopl:error 'apply-senv "No binding for ~s" var))

(define (check-arg-type name pred arg)
  (if (pred arg)
      #t
      (eopl:error 'check-arg-type "expected ~s, got ~s" name arg)))

(define senv? (list-of identifier?))

(define (empty-senv) '())
(define empty-senv? null?)
(define (extend-senv var senv)
  (cons var senv))

(define (extend-senv+ vars senv)
  (if (null? vars)
      senv
      (extend-senv+ (cdr vars) (extend-senv (car vars) senv))))

; similar to extend-env*, each exp is translated in the env just extended in the previous step
; Listof(Var) x Listof(Exp) x Senv -> Pairof(Senv . Listof(NamelessExp))
(define (extend-senv* vars exps senv)
  (let loop ((vars vars)
             (exps exps)
             (senv senv))
    (if (null? vars)
        (cons senv '())
        (let ((res (loop (cdr vars) (cdr exps) (extend-senv (car vars) senv))))
          (cons (car res) (cons (translation-of (car exps) senv) (cdr res)))))))

; Senv x Var -> Lexaddr
(define (apply-senv senv search-var)
  (let loop ((senv senv)
             (idx 0))
    (if (empty-senv? senv)
        (report-unbound-var search-var)
        (if (eqv? (car senv) search-var)
            idx
            (loop (cdr senv) (+ 1 idx))))))

; Senv x Var -> Bool
(define (lookup-senv senv search-var)
  (let loop ((senv senv))
    (if (empty-senv? senv)
        #f
        (if (eqv? (car senv) search-var)
            #t
            (loop (cdr senv))))))

; merge multiple envs, eliminate the duplicate vars
(define (merge-senvs senv1 . senvs)
  (check-arg-type 'senv? senv? senv1)
  (check-arg-type 'list-of-senv? (list-of senv?) senvs)
  (define (merge-senv e1 e2)
    (cond
      ((empty-senv? e1) e2)
      ((empty-senv? e2) e1)
      (else (fold/l (lambda (env var) (if (memq var env)
                                          env
                                          (extend-senv var env)))
                    e1 e2))))
  (fold/l (lambda (res-env env)
            (merge-senv res-env env))
          senv1 senvs))

;init-senv : () → SEnv
;usage: (init-senv) = [i,v,x,true,false,+,-,...]
(define (init-senv)
  (fold/l (lambda (senv p)
            (extend-senv (car p) senv))
          (fold/l (lambda (senv p)
                    (extend-senv (car p) senv)) (empty-senv) primitives)
          global-bindings))

; filter the senv to keep only the bindings for the free variables of the expresison
; note for let-exp/let*-exp/proc-exp ..., we need to add those vars into bound variables
(define (filter-senv vars exp senv)
  (let loop ((vars vars)
             (exp exp))
    (cases expression exp
      (const-exp (num) (empty-senv))
      (var-exp (var) (if (memq var vars)
                         (empty-senv)
                         (let ((res (lookup-senv senv var)))
                           (if res (extend-senv var (empty-senv)) (empty-senv)))))
      (if-exp (exp1 exp2 exp3) (merge-senvs (loop vars exp1) (loop vars exp2) (loop vars exp3)))
      (let-exp (vars2 exps body) (merge-senvs (apply merge-senvs (map (lambda (exp) (loop vars exp)) exps))
                                              (loop (append vars vars2) body)))
      (let*-exp (vars2 exps body) (car (fold/l (lambda (env&vars var exp)
                                                 (cons (merge-senvs (car env&vars)
                                                                    (loop (cdr env&vars) exp))
                                                       (cons var (cdr env&vars))))
                                               (cons (loop (append vars vars2) body) vars)
                                               vars2 exps)))
      (null-exp () (empty-senv))
      (cond-exp (preds actions) (apply merge-senvs (map (lambda (exp) (loop vars exp)) (append preds actions))))
      (unpack-exp (vars2 exp1 body) (merge-senvs (loop vars exp1) (loop (append vars vars2) body)))
      (proc-exp (vars2 body) (loop (append vars vars2) body))
      (call-exp (rator rands) (fold/l (lambda (env rand)
                                        (merge-senvs env (loop vars rand)))
                                      (loop vars rator)
                                      rands))
      (else (report-invalid-source-expression exp))
      )))

; nameless environment
;nameless-environment? : SchemeVal→Bool
; because we need to store SchemeVector, so we loosen the constraint here
(define nameless-environment? (list-of any))

;empty-nameless-env : () → Nameless-env
(define (empty-nameless-env) '())

;extend-nameless-env : Expval × Nameless-env → Nameless-env
(define (extend-nameless-env val env)
  (cons val env))

;apply-nameless-env : Nameless-env × Lexaddr → DenVal
(define (apply-nameless-env env addr)
  (let ((val (list-ref env addr)))
    (if (expval? val)
        val
        (vector-ref val 0))))

(define (extend-nameless-env+ vals env)
  (if (null? vals)
      env
      (extend-nameless-env+ (cdr vals)
                            (extend-nameless-env (car vals) env))))

; each exp is evaluated in the env just extended in the previous step
(define (extend-nameless-env* exps env)
  (if (null? exps)
      env
      (extend-nameless-env* (cdr exps) (extend-nameless-env (value-of (car exps) env) env))))

(define (extend-nameless-env-rec bodys saved-env)
  (let* ((vecs (map (lambda (n) (make-vector 1)) bodys))
         (new-env (fold/l (lambda (env vec) (extend-nameless-env vec env)) saved-env vecs)))
    (for-each (lambda (vec body)
                (vector-set! vec 0 (proc-val (compound body new-env #f))))
              vecs bodys)
    new-env))

; we should not reverse the order
(define (filter-nameless-env indices env)
  (let loop ((indices indices)
             (env env)
             (i 0))
    (if (null? indices)
        '()
        (let ((idx (car indices)))
          (if (= i idx)
              (cons (car env) (loop (cdr indices) (cdr env) (+ i 1)))
              (loop indices (cdr env) (+ i 1)))))))

;init-nameless-env : () → NamelessEnv
;usage: (init-nameless-env) = [1,5,10,true,false,+,-,...]
(define (init-nameless-env)
  (fold/l (lambda (env p) (extend-nameless-env (cdr p) env))
          (fold/l (lambda (env p)
                    (let ((name (car p))
                          (op (cdr p)))
                      (extend-nameless-env (proc-val (primitive name op)) env)))
                  (empty-nameless-env)
                  primitives)
          global-bindings))

(define global-bindings
  (list (cons 'i (num-val 1))
        (cons 'v (num-val 5))
        (cons 'x (num-val 10))
        (cons 'true true)
        (cons 'false false)))

; translation
(define (translation-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (a-program (translation-of exp1 (init-senv))))))

; translation-of: Exp x Senv -> Nameless-exp
(define (translation-of exp senv)
  (cases expression exp
    (const-exp (num) (const-exp num))
    (var-exp (var) (nameless-var-exp (apply-senv senv var)))
    (if-exp (exp1 exp2 exp3)
            (if-exp
             (translation-of exp1 senv)
             (translation-of exp2 senv)
             (translation-of exp3 senv)))
    (let-exp (vars exps body)
             (nameless-let-exp
              (map (lambda (exp) (translation-of exp senv)) exps)
              (translation-of body (extend-senv+ vars senv))))
    (let*-exp (vars exps body)
              (let ((res (extend-senv* vars exps senv)))
                (nameless-let*-exp (cdr res) (translation-of body (car res)))))
    (letrec-exp (p-names b-varss p-bodys letrec-body)
                (let ((nsenv (extend-senv+ p-names senv)))
                  (nameless-letrec-exp
                   (map (lambda (b-vars p-body) (translation-of p-body (extend-senv+ b-vars nsenv))) b-varss p-bodys)
                   (translation-of letrec-body nsenv))))
    (null-exp () (null-exp))
    (cond-exp (preds actions) (cond-exp preds actions))
    (unpack-exp (vars exp1 body)
                (nameless-unpack-exp
                 (translation-of exp1 senv)
                 (translation-of body (extend-senv+ vars senv))))
    ; we must record the indices as well because a complete environment is split into the static env and nameless env,
    ; so after filtering the static env we also need to filter the nameless env according to these indices
    (proc-exp (vars body)
              (let* ((new-senv (filter-senv vars body senv))
                     (indices-vars (sort-filtered-senv senv new-senv)))
                (nameless-proc-exp (map car indices-vars) (translation-of body (extend-senv+ vars (map cdr indices-vars))))))  ; NOTE: first sort the filtered senv and then extend
    (traceproc-exp (vars body)
                   (let* ((new-senv (filter-senv vars body senv))
                          (indices-vars (sort-filtered-senv senv new-senv)))
                (nameless-traceproc-exp (map car indices-vars) (translation-of body (extend-senv+ vars (map cdr indices-vars))))))
    (call-exp (rator rands) (call-exp (translation-of rator senv)
                                      (map (lambda (rand) (translation-of rand senv)) rands)))
    (else (report-invalid-source-expression exp))
    ))

; collect the indices of the filtered vars in the original env and sort
; Senv x Senv -> Listof(Pairof(N . Identitifier))
(define (sort-filtered-senv senv new-senv)
  (sort/predicate (lambda (p1 p2) (< (car p1) (car p2)))
                  (let loop ((new-senv new-senv)
                             (indices-vars '()))
                    (if (empty-senv? new-senv)
                        indices-vars
                        (loop (cdr new-senv) (cons (cons (apply-senv senv (car new-senv)) (car new-senv)) indices-vars))))))

(define (report-invalid-source-expression exp)
  (eopl:error 'translation-of "invalid source expression ~s" exp))


; evaluation
(define (trans&eval pgm)
  (value-of-program (translation-of-program pgm)))

;run : String → ExpVal ->Sexp
(define (run string)
  (expval->sexp (trans&eval (scan&parse string))))

;value-of-program : NamelessProgram → ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (value-of exp1 (init-nameless-env)))))

;value-of : Exp × NamelessEnv → ExpVal
;we don't check the arity match for now.
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (nameless-var-exp (addr) (apply-nameless-env env addr))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (nameless-let-exp (exps body)
                        (value-of body
                                  (extend-nameless-env+ (value-of-explist exps env) env)))
      (nameless-let*-exp (exps body)
                         (value-of body (extend-nameless-env* exps env)))
      (nameless-letrec-exp (p-bodys letrec-body)
                           (value-of letrec-body (extend-nameless-env-rec p-bodys env)))
      (null-exp () (null-val))
      (cond-exp (preds actions)
                (value-of-cond preds actions env))
      (nameless-unpack-exp (exp1 body)
                           (let* ((lst (value-of exp1 env))
                                  (vals (expval->list lst)))
                             (value-of body (extend-nameless-env+ vals env))))
      (nameless-proc-exp (indices body) (proc-val (compound body (filter-nameless-env indices env) #f)))
      (nameless-traceproc-exp (indices body) (proc-val (compound body (filter-nameless-env indices env) #t)))
      (call-exp (rator rands)
                (let ((a-proc (expval->proc (value-of rator env)))
                      (args (value-of-explist rands env)))
                  (apply-procedure a-proc args)))
      (else (report-invalid-translated-expression exp))
      )))

(define (report-invalid-translated-expression exp)
  (eopl:error 'value-of "invalid translated expression ~s" exp))

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

(define (check-arity vars args)
  (let ((l1 (length vars))
        (l2 (length args)))
    (if (not (= l1 l2))
        (eopl:error 'apply-procedure "arity mismatch, expected ~s, got ~s" l1 l2)
        #t)))

(define (apply-procedure proc1 args)
  (cases proc proc1
    (compound (body env trace)
              (if trace (display "enter procedure\n") #t)
              ;(check-arity vars args)
              (let ((res (value-of body (extend-nameless-env+ args env))))
                (if trace (display "exit procedure\n") #t)
                res))
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

; From Exericse 1.29 [**] / 1.30[**]
; partition: partition the list into 2 lists from the middle
; usgae: List -> Pairof(List)
; > (partition '())
; (())
; > (partition '(1))
; (() 1)
; > (partition '(1 2))
; ((1) 2)
; > (partition '(1 2 3))
; ((1) 2 3)
; > (partition '(1 2 3 4))
; ((2 1) 3 4)
(define (partition loi)
  (define (iter lloi rloi p2) ; 2-pointers method
    (if (or (null? p2)
            (null? (cdr p2)))
        (cons lloi rloi)
        (iter (cons (car rloi) lloi) ; note lloi is in the reversed order, but it doesn't matter
              (cdr rloi)        ; 1 step
              (cddr p2))))		; 2 steps
  (iter '() loi loi))

; merge-pred: similar to merge, but compare by the predicate `pred`
(define (merge-pred pred loi1 loi2)
  (define (merge loi1 loi2)
    (cond
      ((null? loi1) loi2)
      ((null? loi2) loi1)
      (else
       (let ((i1 (car loi1))
             (i2 (car loi2)))
         (if (pred i1 i2)
             (cons i1 (merge (cdr loi1) loi2))
             (cons i2 (merge loi1 (cdr loi2))))))))
  (merge loi1 loi2))

; > (sort/predicate < '(8 2 5 2 3))
; (2 2 3 5 8)
; > (sort/predicate > '(8 2 5 2 3))
; (8 5 3 2 2)
(define (sort/predicate pred loi)
  (if (or (null? loi) (null? (cdr loi)))
      loi
      (let ((res (partition loi)))
        (merge-pred pred (sort/predicate pred (car res))
                    (sort/predicate pred (cdr res))))))

(define repl
  (sllgen:make-rep-loop "--> " trans&eval
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
;> (run "letrec
;               even(x) = if (zero? x) then 1 else (odd (- x 1))
;               odd(x) = if (zero? x) then 0 else (even (- x 1))
;        in (odd 13)")
;1
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
(run "unpack a b c = (list 1 2 3) in let* x = 4 y =5 in let f = proc(m n) proc(o p) (list a b c x y m n o p) in ((f 10 20) 30 40)")
;(1 2 3 4 5 10 20 30 40)
(run "unpack a b c = (list 1 2 3) in let* x = 4 y =5 in let f = proc(m n) let a= 0 x = 6 in proc(o p) (list a b c x y m n o p) in ((f 10 20) 30 40)")
;(0 2 3 6 5 10 20 30 40)