#lang eopl
; Mutable Pairs (add array)

;Exercise 4.29 [**] Add arrays to this language. Introduce new operators newarray,
;arrayref, and arrayset that create, dereference, and update arrays. The locations
;in an array are consecutive, and the array indices are zero-based.
;Exercise 4.30 [**] Add to the language of exercise 4.29 a procedure arraylength,
;which returns the size of an array. Your procedure should work in constant time.
;Make sure that arrayref and arrayset check to make sure that their indices are
;within the length of the array.

;As usual, we implement newarray/arrayref/arrayset/arrrylength as primitives.
;As a bonus, we finally managed to support negative number in our language :)

;ExpVal  = Int+Bool+Null+Pair+Proc+Void+Subr+MutPair+ArrVal
;DenVal  = Ref(ExpVal) + ExpVal
;MutPair = Ref(ExpVal) x Ref(ExpVal)
;ArrVal  = (Ref(ExpVal))*
 
;syntax
;Program    ::= Statement
;               a-program (state1)
;Statement  ::= Identifier = Expression
;               assign-state (var exp1)
;           ::= print Expression
;               print-state (exp1)
;           ::= { {Statement}*(;) }
;               multl-state (states)
;           ::= if Expression Statement Statement
;               if-state (exp1 state1 state2)
;           ::= while Expression Statement
;               while-state (exp1 state1)
;           ::= do Statement while Expression
;               dowhile-state (state1 exp1)
;           ::= var {Identifier = Expression}*(,) ; Statement
;               varblock-state (vars exps state1)
;           ::= read Identifier
;               read-state (var)
;           ::= call (Expression {Expression}*)
;               call-state (rator rands)
;           ::= %assign-state Number Expression
;               nameless-assign-state (addr exp1)
;           ::= %varblock-state {Expression}* Statement
;               nameless-varblock-state (exps state1)
;           ::= %read Number
;               nameless-read-state (num)
;Expression ::= Number
;               const-exp (num)
;Expression ::= if Expression then Expression else Expression
;               if-exp (exp1 exp2 exp3)
;Expression ::= Identifier
;               var-exp (var)
;Expression ::= let {Identifier = Expression}* in Expression
;               let-exp (vars exps body)
;Expression ::= letm {Identifier = Expression}* in Expression
;               letm-exp (vars exps body)
;Expression ::= let* {Identifier = Expression}* in Expression
;               let*-exp (vars exps body)
;Expression ::= letrec {Identifier = Expression}* in Expression
;               letrec-exp (vars exps letrec-body)
;Expression ::= cond {Expression ==> Expression}∗ end
;               cond-exp (preds actions)
;Expression ::= unpack {Identifier}∗ = Expression in Expression
;               unpack-exp (vars exp1 exp2)
;Expression ::= proc ({Identifier}*) Expression
;               proc-exp (vars body)
;Expression ::= traceproc ({Identifier}*) Expression
;               traceproc-exp (vars body)
;Expression ::= subr ({Identifier}*) Statement
;               subr-exp (vars body)
;Expression ::= begin Expression {Expression}∗ end
;               begin-exp (exp1 exps)
;Expression ::= set Identifier = Expression
;               assign-exp (var exp1)
;Expression ::= setdynamic Identifier = Expression during expression
;               setdynamic-exp (var exp1 body)
;Expression ::= (Expression {Expression}*)
;               call-exp (rator rands)
;Expression ::= %lexref number
;               nameless-var-exp (num)
;Expression ::= %let {Expression}* in Expression
;               nameless-let-exp (exps body)
;Expression ::= %let* {Expression}* in Expression
;               nameless-let*-exp (exps body)
;Expression ::= %letrec {Expression}* in Expression
;               nameless-letrec-exp (exps letrec-body)
;Expression ::= %unpack Expression in Expression
;               nameless-unpack-exp (exp1 exp2)
;Expression ::= %lexproc Expression
;               nameless-proc-exp (body)
;Expression ::= %lextraceproc Expression
;               nameless-traceproc-exp (body)
;Expression ::= %lexsubr Statement
;               nameless-subr-exp (body)
;Expression ::= %set number Expression
;               nameless-assign-exp (addr exp1)
;Expression ::= %setdynamic number Expression expression
;               nameless-setdynamic-exp (addr exp1 body)
;Operation  ::= +|-|*|/|equal?|greater?|less?|minus|cons|car|cdr|null?|list|print|not|mpair|left|right|setleft|
;               setright|newarray|arrayref|arrayset|arraylength


; wonder why scanner-spec2 doesn't work
;(define special '("+" "-" "*" "/" "?" "!"))
;(define scanner-spec2
;  `((white-sp (whitespace) skip)
;    (comment ("%" (arbno (not #\newline))) skip)
;    (identifier ((or letter ,@special) (arbno (or letter digit ,@special))) symbol)
;    (number (digit (arbno digit)) number)))

(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier ((or letter "*" "/" "?" "!") (arbno (or letter digit "+" "-" "*" "/" "?" "!"))) symbol)
    (identifier ((or "+" "-")) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define grammar
  '((program (statement) a-program)
    (statement (identifier "=" expression) assign-state)
    (statement ("print" expression) print-state)
    (statement ("{" (separated-list statement ";") "}") multi-state)
    (statement ("if" expression statement statement) if-state)
    (statement ("while" expression statement) while-state)
    (statement ("do" statement "while" expression) dowhile-state)
    (statement ("var" (separated-list identifier "=" expression ",") ";" statement) varblock-state)
    (statement ("read" identifier) read-state)
    (statement ("call" "(" expression (arbno expression) ")") call-state)
    (statement ("%assign-state" number expression) nameless-assign-state)
    (statement ("%varblock-state" (arbno expression) "in" statement) nameless-varblock-state) ; add "in" to avoid conflict
    (statement ("%read" number) nameless-read-state)
    (expression (number) const-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("letm" (arbno identifier "=" expression) "in" expression) letm-exp) ;****
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("letrec" (arbno identifier "=" expression) "in" expression) letrec-exp)
    (expression ("emptylist") null-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("traceproc" "(" (arbno identifier) ")" expression) traceproc-exp)
    (expression ("subr" "(" (arbno identifier) ")" statement) subr-exp)
    (expression ("begin" expression (arbno expression) "end") begin-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("setdynamic" identifier "=" expression "during" expression) setdynamic-exp)
    (expression ("(" expression  (arbno expression) ")") call-exp)
    (expression ("%lexref" number) nameless-var-exp)
    (expression ("%let" (arbno expression) "in" expression) nameless-let-exp)
    (expression ("%letm" (arbno expression) "in" expression) nameless-letm-exp) ;****
    (expression ("%let*" (arbno expression) "in" expression) nameless-let*-exp)
    (expression ("%letrec" (arbno expression) "in" expression) nameless-letrec-exp)
    (expression ("%unpack" expression "in" expression) nameless-unpack-exp)
    (expression ("%lexproc" expression) nameless-proc-exp)
    (expression ("%lextraceproc" expression) nameless-traceproc-exp)
    (expression ("%lexsubr" statement) nameless-subr-exp)
    (expression ("%set" number expression) nameless-assign-exp)
    (expression ("%setdynamic" number expression expression) nameless-setdynamic-exp)
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
  (mpair-val (left-loc reference?) (right-loc reference?))
  (proc-val (proc proc?))
  (subr-val (subr subr?))
  (void-val)
  (array-val (array array?)))

; procedure
(define-datatype proc proc?
  (compound (body expression?) (saved-nameless-env nameless-environment?) (trace boolean?))
  (primitive (name identifier?) (op procedure?)))

; subroutine
(define-datatype subr subr?
  (comp-subr (body statement?) (saved-nameless-env nameless-environment?)))

(define-datatype array array?
  (an-array (start number?) (length number?)))

; used by print
(define (expval->sexp val)
  (cases expval val
    (num-val (num) num)
    (bool-val (bool) bool)
    (null-val () '())
    (pair-val (a d) (cons (expval->sexp a) (expval->sexp d)))
    (mpair-val (l r) (cons 'mpair (cons (expval->sexp (deref l)) (expval->sexp (deref r)))))
    (proc-val (a-proc) (cases proc a-proc
                         (compound (body env trace)
                                   (if trace
                                       (string->symbol "#<traceproc>")
                                       (string->symbol "#<procedure>")))
                         (primitive (name op) (string->symbol (string-append "#<primitive:"
                                                                             (symbol->string name) ">")))))
    (subr-val (a-subr) (cases subr a-subr
                         (comp-subr (body env) (string->symbol "#<subroutine>"))))
    (void-val () "#<void>")
    (array-val (arr) (cases array arr
                       (an-array (start length)
                                 (let loop ((len length)
                                            (res '()))
                                   (if (= 0 len)
                                       (cons 'array res)
                                       (loop (- len 1) (cons (expval->sexp (deref (+ start (- len 1)))) res)))))))))

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

;expval->subr : ExpVal → Subr
(define (expval->subr val)
  (cases expval val
    (subr-val (subr) subr)
    (else (report-expval-extractor-error 'subr val))))

;expval->array : ExpVal → Array
(define (expval->array val)
  (cases expval val
    (array-val (vec) vec)
    (else (report-expval-extractor-error 'array val))))

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

; ====static environment====
; Senv= Listof(Sym)
; Lexaddr = N
(define (report-unbound-var var)
  (eopl:error 'apply-senv "No binding for ~s" var))

(define-datatype senv-type senv?
  (empty-senv)
  (extend-senv (var identifier?) (senv senv?)))

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
          (cons (car res) (cons (translation-of-exp (car exps) senv) (cdr res)))))))

; Senv x Var -> Lexaddr
(define (apply-senv senv search-var)
  (cases senv-type senv
    (empty-senv () (report-unbound-var search-var))
    (extend-senv (var senv) (if (eqv? var search-var)
                                0
                                (+ 1 (apply-senv senv search-var))))))

;init-senv : () → SEnv
;usage: (init-senv) = [i,v,x,true,false,+,-,...]
(define (init-senv)
  (fold/l (lambda (senv p)
            (extend-senv (car p) senv))
          (fold/l (lambda (senv p)
                    (extend-senv (car p) senv)) (empty-senv) primitives)
          global-bindings))

; ====nameless environment====
;nameless-environment? : SchemeVal→Bool
; because we need to store SchemeVector, so we loosen the constraint here
(define nameless-environment? (list-of any))

;empty-nameless-env : () → Nameless-env
(define (empty-nameless-env) '())

;extend-nameless-env : Expval × Nameless-env → Nameless-env
(define (extend-nameless-env val env mutable)
  (let ((denval (if mutable (newref val) val)))
    (cons denval env)))

;apply-nameless-env : Nameless-env × Lexaddr → DenVal
(define (apply-nameless-env env addr)
  (list-ref env addr))

(define (extend-nameless-env+ vals env mutable)
  (if (null? vals)
      env
      (extend-nameless-env+ (cdr vals)
                            (extend-nameless-env (car vals) env mutable) mutable)))

; each exp is evaluated in the env just extended in the previous step
(define (extend-nameless-env* exps env mutable)
  (if (null? exps)
      env
      (extend-nameless-env* (cdr exps) (extend-nameless-env (value-of (car exps) env) env mutable) mutable)))

; support procs and other expressions simultaneously
(define (extend-nameless-env-rec exps saved-env mutable)
  (let* ((vecs (map (lambda (n) (make-vector 1)) exps))
         (new-env (fold/l (lambda (env vec) (extend-nameless-env vec env mutable)) saved-env vecs)))
    ; evaluate procs first, then others
    (for-each (lambda (vec exp)
                (cases expression exp
                  (nameless-proc-exp (body) (vector-set! vec 0 (value-of exp new-env)))
                  (nameless-traceproc-exp (body) (vector-set! vec 0 (value-of exp new-env)))
                  (else #t)))
              vecs exps)
    (for-each (lambda (vec exp)
                (cases expression exp
                  (nameless-proc-exp (body) #t)
                  (nameless-traceproc-exp (body) #t)
                  (else (vector-set! vec 0 (value-of exp new-env)))))
              vecs exps)
    new-env))

;init-nameless-env : () → NamelessEnv
;usage: (init-nameless-env) = [1,5,10,true,false,+,-,...]
(define (init-nameless-env)
  (fold/l (lambda (env p) (extend-nameless-env (cdr p) env #f))
          (fold/l (lambda (env p)
                    (let ((name (car p))
                          (op (cdr p)))
                      (extend-nameless-env (proc-val (primitive name op)) env #f)))
                  (empty-nameless-env)
                  primitives)
          global-bindings))

(define global-bindings
  (list (cons 'i (num-val 1))
        (cons 'v (num-val 5))
        (cons 'x (num-val 10))
        (cons 'true true)
        (cons 'false false)))

; ====translation====
(define (translation-of-program pgm)
  (cases program pgm
    (a-program (state1)
               (a-program (translation-of-state state1 (init-senv))))))

; translation-of-state: State x Senv -> Nameless-statement
(define (translation-of-state state senv)
  (cases statement state
    (assign-state (var exp1) (nameless-assign-state (apply-senv senv var)
                                                    (translation-of-exp exp1 senv)))
    (print-state (exp1) (print-state (translation-of-exp exp1 senv)))
    (multi-state (states) (multi-state (map (lambda (state) (translation-of-state state senv)) states)))
    (if-state (exp1 state1 state2) (if-state (translation-of-exp exp1 senv)
                                             (translation-of-state state1 senv)
                                             (translation-of-state state2 senv)))
    (while-state (exp1 state1) (while-state (translation-of-exp exp1 senv) (translation-of-state state1 senv)))
    (dowhile-state (state1 exp1) (dowhile-state (translation-of-state state1 senv) (translation-of-exp exp1 senv)))
    ; similar to letrec-exp, the scope of a variable includes the body and all the initializers in the same block statement
    (varblock-state (vars exps state1) (let ((nsenv (extend-senv+ vars senv)))
                                         (nameless-varblock-state (map (lambda (exp) (translation-of-exp exp nsenv)) exps)
                                                                  (translation-of-state state1 nsenv))))
    (read-state (var) (nameless-read-state (apply-senv senv var)))
    (call-state (rator rands) (call-state (translation-of-exp rator senv)
                                          (map (lambda (rand) (translation-of-exp rand senv)) rands)))
    (else (report-invalid-source-statement state))
    ))

; translation-of-exp: Exp x Senv -> Nameless-exp
(define (translation-of-exp exp senv)
  (cases expression exp
    (const-exp (num) (const-exp num))
    (var-exp (var) (nameless-var-exp (apply-senv senv var)))
    (if-exp (exp1 exp2 exp3)
            (if-exp
             (translation-of-exp exp1 senv)
             (translation-of-exp exp2 senv)
             (translation-of-exp exp3 senv)))
    (let-exp (vars exps body)
             (nameless-let-exp
              (map (lambda (exp) (translation-of-exp exp senv)) exps)
              (translation-of-exp body (extend-senv+ vars senv))))
    (letm-exp (vars exps body)
              (nameless-letm-exp
               (map (lambda (exp) (translation-of-exp exp senv)) exps)
               (translation-of-exp body (extend-senv+ vars senv))))
    (let*-exp (vars exps body)
              (let ((res (extend-senv* vars exps senv)))
                (nameless-let*-exp (cdr res) (translation-of-exp body (car res)))))
    (letrec-exp (vars exps letrec-body)
                (let ((nsenv (extend-senv+ vars senv)))
                  (nameless-letrec-exp
                   (map (lambda (exp) (translation-of-exp exp nsenv)) exps)
                   (translation-of-exp letrec-body nsenv))))
    (null-exp () (null-exp))
    (cond-exp (preds actions) (cond-exp preds actions))
    (unpack-exp (vars exp1 body)
                (nameless-unpack-exp
                 (translation-of-exp exp1 senv)
                 (translation-of-exp body (extend-senv+ vars senv))))
    (proc-exp (vars body) (nameless-proc-exp (translation-of-exp body (extend-senv+ vars senv))))
    (traceproc-exp (vars body) (nameless-traceproc-exp (translation-of-exp body (extend-senv+ vars senv))))
    (subr-exp (vars body) (nameless-subr-exp (translation-of-state body (extend-senv+ vars senv))))
    (begin-exp (exp1 exps) (begin-exp
                             (translation-of-exp exp1 senv)
                             (map (lambda (exp) (translation-of-exp exp senv)) exps)))
    (assign-exp (var exp1) (nameless-assign-exp (apply-senv senv var)
                                                (translation-of-exp exp1 senv)))
    ; we need the address because it'll be used to resume the original value
    ; note we don't need to extend the senv when translating the body because the var already bound
    ; we just change the content of the reference
    (setdynamic-exp (var exp1 body) (nameless-setdynamic-exp (apply-senv senv var) 
                                                             (translation-of-exp exp1 senv)
                                                             (translation-of-exp body senv)))
    (call-exp (rator rands) (call-exp (translation-of-exp rator senv)
                                      (map (lambda (rand) (translation-of-exp rand senv)) rands)))
    (else (report-invalid-source-expression exp))
    ))

(define (report-invalid-source-statement state)
  (eopl:error 'translation-of-state "invalid source statement ~s" state))
(define (report-invalid-source-expression exp)
  (eopl:error 'translation-of-exp "invalid source expression ~s" exp))

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
    (if (uninitialized-val? val)
        (report-initialized-reference)
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

(define (maybe-deref denval)
  (let ((expval (if (reference? denval)
                    (deref denval)
                    denval)))
    (if (vector? expval)
        (vector-ref expval 0)
        expval)))

(define (report-invalid-reference ref store)
  (eopl:error 'setref! "invalid reference ~s" ref))

(define (uninitialized-val) 'uninitialized)

(define (uninitialized-val? val) (eq? val 'uninitialized))

(define (report-initialized-reference)
  (eopl:error 'deref "reference is uninitialized"))

; ====evaluation====
(define (trans&eval pgm)
  (result-of-program (translation-of-program pgm))
  (let ((x 0)) (set! x 1))) ; just to return void

;run : String → Effect
(define (run string)
  (trans&eval (scan&parse string)))

;result-of-program : NamelessProgram → Effect
(define (result-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (state1)
               (result-of state1 (init-nameless-env)))))

(define (result-of state env)
  (cases statement state
    (nameless-assign-state (addr exp1)
                           (let ((denval (apply-nameless-env env addr)))
                             (check-lvalue denval exp1)
                             (setref! denval (value-of exp1 env))))
    (print-state (exp1) (display (expval->sexp (value-of exp1 env))) (newline))
    (multi-state (states) (for-each (lambda (state) (result-of state env)) states))
    (if-state (exp1 state1 state2) (if (expval->bool (value-of exp1 env))
                                       (result-of state1 env)
                                       (result-of state2 env)))
    (while-state (exp1 state1) (let loop ()
                                 (if (expval->bool (value-of exp1 env))
                                     (begin (result-of state1 env) (loop))
                                     'ok)))
    (dowhile-state (state1 exp1) (let loop ()
                                   (result-of state1 env)
                                   (if (expval->bool (value-of exp1 env))
                                       (loop)
                                       'ok)))
    (nameless-varblock-state (exps state1)
                             (result-of state1 (extend-nameless-env-rec exps env #t))) ; mutable
    (nameless-read-state (addr) (let ((denval (apply-nameless-env env addr)))
                                  (check-lvalue denval "")
                                  (let ((num (read)))
                                    (if (and (integer? num) (not (negative? num)))
                                        (setref! denval (num-val num))
                                        (report-invalid-read-input num)))))
    (call-state (rator rands) (let ((a-proc (expval->subr (value-of rator env)))
                                    (args (value-of-explist rands env)))
                                (apply-subroutine a-proc args)))
    (else (report-invalid-translated-statement state))
    ))

;value-of : Exp × NamelessEnv → ExpVal
;we don't check the arity match for now.
(define (value-of exp env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (nameless-var-exp (addr) (maybe-deref (apply-nameless-env env addr))) ;****
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 env)))
              (if (expval->bool val1)
                  (value-of exp2 env)
                  (value-of exp3 env))))
    (nameless-let-exp (exps body)
                      (value-of body
                                (extend-nameless-env+ (value-of-explist exps env) env #f)))
    (nameless-letm-exp (exps body)
                       (value-of body
                                 (extend-nameless-env+ (value-of-explist exps env) env #t)))
    (nameless-let*-exp (exps body)
                       (value-of body (extend-nameless-env* exps env #f)))
    (nameless-letrec-exp (exps letrec-body)
                         (value-of letrec-body (extend-nameless-env-rec exps env #f)))
    (null-exp () (null-val))
    (cond-exp (preds actions)
              (value-of-cond preds actions env))
    (nameless-unpack-exp (exp1 body)
                         (let* ((lst (value-of exp1 env))
                                (vals (expval->list lst)))
                           (value-of body (extend-nameless-env+ vals env #f))))
    (nameless-proc-exp (body) (proc-val (compound body env #f)))
    (nameless-traceproc-exp (body) (proc-val (compound body env #t)))
    (nameless-subr-exp (body) (subr-val (comp-subr body env)))
    (begin-exp (exp1 exps) (let loop ((exp1 exp1)
                                      (exps exps))
                             (let ((val (value-of exp1 env)))
                               (if (null? exps)
                                   val
                                   (loop (car exps) (cdr exps))))))
    (nameless-assign-exp (addr exp1)
                         (let ((denval (apply-nameless-env env addr)))
                           (check-lvalue denval exp1) ;****
                           (setref! denval (value-of exp1 env))
                           (void-val)))
    (nameless-setdynamic-exp (addr exp1 body)
                             (let* ((denval (apply-nameless-env env addr))
                                    (_ (check-lvalue denval exp1))
                                    (oldval (deref denval)))
                               (setref! denval (value-of exp1 env))
                               (let ((res (value-of body env)))
                                 (setref! denval oldval)
                                 res)))
    (call-exp (rator rands)
              (let ((a-proc (expval->proc (value-of rator env)))
                    (args (value-of-explist rands env)))
                (apply-procedure a-proc args)))
    (else (report-invalid-translated-expression exp))
    ))

(define (check-lvalue denval exp)
  (if (not (reference? denval))
      (report-set-immutable-variable exp)
      #t))

(define (report-set-immutable-variable exp)
  (eopl:error 'value-of/result-of "can't set an immutable variable to ~s" exp))

(define (report-invalid-translated-statement state)
  (eopl:error 'result-of "invalid translated statement ~s" state))

(define (report-invalid-read-input num)
  (eopl:error 'read "not a non-negative integer ~s" num))

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
              (let ((res (value-of body (extend-nameless-env+ args env #f))))
                (if trace (display "exit procedure\n") #t)
                res))
    (primitive (name op) (apply op args))))

(define (apply-subroutine subr1 args)
  (cases subr subr1
    (comp-subr (body env)
               ;(check-arity vars args)
               (result-of body (extend-nameless-env+ args env #f)))))

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

; ExpVal(Bool) → ExpVal(Bool)
(define (prim-not val1)
  (let ((b (expval->bool val1)))
    (if b false true)))

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

; mutable pairs
;prim-mpair : ExpVal × ExpVal → ExpVal(MutPair)
(define (prim-mpair val1 val2)
  (mpair-val
   (newref val1)
   (newref val2)))

;prim-left : ExpVal(MutPair) → ExpVal
(define (prim-left p)
  (cases expval p
    (mpair-val (left-loc right-loc)
               (deref left-loc))
    (else (report-expval-extractor-error 'mpair p))))

;prim-right : ExpVal(MutPair) → ExpVal
(define (prim-right p)
  (cases expval p
    (mpair-val (left-loc right-loc)
               (deref right-loc))
    (else (report-expval-extractor-error 'mpair p))))

;prim-setleft : ExpVal(MutPair) × ExpVal → Unspecified
(define (prim-setleft p val)
  (cases expval p
    (mpair-val (left-loc right-loc)
               (setref! left-loc val))
    (else (report-expval-extractor-error 'mpair p))))

;prim-setright : ExpVal(MutPair) × ExpVal → Unspecified
(define (prim-setright p val)
  (cases expval p
    (mpair-val (left-loc right-loc)
               (setref! right-loc val))
    (else (report-expval-extractor-error 'mpair p))))

; array
;prim-newarray : ExpVal(Int) × ExpVal → ExpVal(Array)
(define (prim-newarray len init)
  (let ((n (expval->num len))
        (start -1))
    (let loop ((i 0))
      (if (= i n)
          (array-val (an-array start n))
          (let ((ref (newref init)))
            (if (= -1 start)
                (set! start ref)
                #t)
            (loop (+ i 1)))))))

;prim-arrayref : ExpVal(Array) × ExpVal(Int) → ExpVal
(define (prim-arrayref arr idx)
  (let ((a (expval->array arr))
        (i (expval->num idx)))
    (cases array a
      (an-array (start length)
                (begin (check-array-index i length)
                       (deref (+ start i)))))))

;prim-arrayref : ExpVal(Array) × ExpVal(Int) × ExpVal → Unspecified
(define (prim-arrayset arr idx val)
  (let ((a (expval->array arr))
        (i (expval->num idx)))
    (cases array a
      (an-array (start length)
                (begin (check-array-index i length)
                       (setref! (+ start i) val))))))

;prim-arraylength : ExpVal(Array) → Unspecified
(define (prim-arraylength arr)
  (let ((a (expval->array arr)))
    (cases array a
      (an-array (start length) (num-val length)))))

(define (check-array-index i len)
  (if (>= i len)
      (report-array-index-out-of-range i len)
      #t))

(define (report-array-index-out-of-range i len)
  (eopl:error 'array "array index out of range, length: ~s, index: ~s" len i))

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
        (cons 'print prim-print)
        (cons 'not prim-not)
        (cons 'mpair prim-mpair)
        (cons 'left prim-left)
        (cons 'right prim-right)
        (cons 'setleft prim-setleft)
        (cons 'setright prim-setright)
        (cons 'newarray prim-newarray)
        (cons 'arrayref prim-arrayref)
        (cons 'arrayset prim-arrayset)
        (cons 'arraylength prim-arraylength)
        ))
  

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

(define (equal-length? l1 l2)
  (= (length l1) (length l2)))

(define repl
  (sllgen:make-rep-loop "--> " trans&eval
                        (sllgen:make-stream-parser scanner-spec grammar)))

; test
(run "var x=3,y=4; {print (+ x y)}")
(run "var x=3, y=4, z=0; {while (not (zero? x)) {z = (+ z y); x = (- x 1)};
                         print z}")
(run "var x=3; {print x;
                var x=4; {print x};
                print x}")
(run "var f=proc (x y) (* x y), x=3; {print (f 4 x)}")
;(run "var x=1; {read x; print x}")
(run "var x=3,y=4,z=0; {do {z = (+ z y); x = (- x 1)} while (not (zero? x));
                        print z}")

(run "var odd=proc (x) if (zero? x) then false else (even (- x 1)), x=(odd 1), y = (even 1),
          even=proc (x) if (zero? x) then true else (odd (- x 1));
          {print (cons x y)}")
(run "print letrec odd=proc (x) if (zero? x) then false else (even (- x 1)) x=(odd 1) y = (even 1)
                   even=proc (x) if (zero? x) then true else (odd (- x 1))
             in (cons x y)")
(run "var sub = subr (x y) print (cons x y); call (sub 1 2)")

;(run "var sub = subr (x y) print (cons x y),
;          f = proc (x y) (cons x y); call (f 3 4)")
;(run "var sub = subr (x y) print (cons x y),
;          f = proc (x y) (cons x y); print (sub 3 4)")
(run "var x = (mpair 1 2); {print x; print (left x); print (right x);
                            print begin (setleft x 3) (left x) end;
                            print begin (setright x 4) (right x) end;
                            print x}")
;(mpair 1 . 2)
;1
;2
;3
;4
;(mpair 3 . 4)
(run "var a = (newarray 2 -1), p = proc(x) let v = (arrayref x 1) in (arrayset x 1 (+ v 1));
      {print a; print (arraylength a); print (arrayref a 0); print (arrayref a 1);
       print begin (p a) (arrayref a 1) end;  print begin (p a) (arrayref a 1) end }")
;(array -1 -1)
;2
;-1
;-1
;0
;1