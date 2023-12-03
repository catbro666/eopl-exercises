#lang eopl
; CPS-OUT Interpreter
;Exercise 6.15 [*] Observer that in the interpreter of the preceding exercise, there is
;only one possible value for cont. Use this observation to remove the cont argument entity.

;Program   ::= TfExp
;              a-program (exp1)
;SimpleExp ::= Number
;              const-exp (num)
;SimpleExp ::= Identifier
;              var-exp (var)
;SimpleExp ::= -(SimpleExp , SimpleExp)
;              cps-diff-exp (simple1 simple2)
;SimpleExp ::= zero?(SimpleExp)
;              cps-zero?-exp (simple1)
;SimpleExp ::= proc ({Identifier}∗) TfExp
;              cps-proc-exp (vars body)
;TfExp     ::= SimpleExp
;              simple-exp->exp (simple-exp1)
;TfExp     ::= let {Identifier = SimpleExp}* in TfExp
;              cps-let-exp (var simple1 body)
;TfExp     ::= letrec {Identifier ({Identifier}∗(,)) = TfExp}∗ in TfExp
;              cps-letrec-exp (p-names b-varss p-bodies body)
;TfExp     ::= if SimpleExp then TfExp else TfExp
;              cps-if-exp (simple1 body1 body2)
;TfExp     ::= (SimpleExp {SimpleExp}∗)
;              cps-call-exp (rator rands)
;Primitives:  +|-|*|/|equal?|greater?|less?|minus|cons|car|cdr|null?|list|print|empty-list

(define scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier ((or letter "*" "/" "?") (arbno (or letter digit "+" "-" "*" "/" "?"))) symbol)
    (identifier ((or "+" "-")) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define grammar
  '((program (tfexp) a-program)
    (simpleexp (number) cps-const-exp)
    (simpleexp (identifier) cps-var-exp)
    (simpleexp ("-" "(" simpleexp simpleexp ")") cps-diff-exp)
    (simpleexp ("zero?" "(" simpleexp ")") cps-zero?-exp)
    (simpleexp ("proc" "(" (arbno identifier) ")" tfexp) cps-proc-exp)
    (tfexp (simpleexp) simple-exp->exp)
    (tfexp ("let" (arbno identifier "=" simpleexp) "in" tfexp) cps-let-exp)
    (tfexp ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp) "in" tfexp) cps-letrec-exp)
    (tfexp ("if" simpleexp "then" tfexp "else" tfexp) cps-if-exp)
    (tfexp ("(" simpleexp (arbno simpleexp)")") cps-call-exp)))

(sllgen:make-define-datatypes scanner-spec grammar)
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec grammar)))
(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar))
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

(define identifier? symbol?)

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

;; Expressed values
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (null-val)
  (pair-val (car expval?) (cdr expval?))
  (proc-val (proc proc?)))

; procedure
(define-datatype proc proc?
  (compound (vars (list-of identifier?)) (body tfexp?) (env env?))
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

(define (report-no-binding-found search-var)
  (eopl:error 'apply-env "No binding for ~s" search-var))

; ****environment****
(define env? (list-of pair?))

(define (empty-env) '())

(define (extend-env var val saved-env)
  (cons (cons var val) saved-env))

(define (apply-env env search-var)
  (let loop ((env env))
    (if (null? env)
        (report-no-binding-found search-var)
        (let ((var (caar env))
              (val (cdar env)))
          (if (eqv? var search-var)
              (if (vector? val)
                  (vector-ref val 0)
                  val)
              (loop (cdr env)))))))

; TODO: check duplicate vars
(define (extend-env+ vars vals env)
  (if (null? vars)
      env
      (extend-env+ (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))

(define (extend-env-rec** p-names b-varss p-bodies env)
  (let* ((vecs (map (lambda (n) (make-vector 1)) p-names))
         (new-env (fold/l (lambda (env name vec) (extend-env name vec env)) env p-names vecs)))
    (for-each (lambda (vec b-vars body)
                (vector-set! vec 0 (proc-val (compound b-vars body new-env))))
              vecs b-varss p-bodies)
    new-env))

;init-env : () → Env
;usage: (init-env) = [i=1^N,v=5^N,x=10^N,true=true,false=false,+=.,-=.,...]
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

;value-of-program : Program → ExpVal
(define (value-of-program pgm)
  (cases program pgm
    (a-program (tfexp1)
               ((end-cont) (value-of/k tfexp1 (init-env))))))

;value-of/k : TfExp × Env × Cont → FinalAnswer
(define value-of/k
  (lambda (exp env)
    (cases tfexp exp
      (simple-exp->exp (simple)
                       (value-of-simple-exp simple env))
      (cps-let-exp (vars rhss body)
                   (let ((vals (map (lambda (rhs) (value-of-simple-exp rhs env)) rhss)))
                     (value-of/k body
                                 (extend-env+ vars vals env))))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (value-of/k letrec-body
                                  (extend-env-rec** p-names b-varss p-bodies env)))
      (cps-if-exp (simple1 body1 body2)
                  (if (expval->bool (value-of-simple-exp simple1 env))
                      (value-of/k body1 env)
                      (value-of/k body2 env)))
      (cps-call-exp (rator rands)
                    (let ((rator-proc
                           (expval->proc
                            (value-of-simple-exp rator env)))
                          (rand-vals
                           (map
                            (lambda (simple)
                              (value-of-simple-exp simple env))
                            rands)))
                      (apply-procedure/k rator-proc rand-vals))))))

(define (value-of-simple-exp simexp env)
  (cases simpleexp simexp
    (cps-const-exp (num) (num-val num))
    (cps-var-exp (var) (apply-env env var))
    (cps-diff-exp (simp1 simp2) (prim-arith- (value-of-simple-exp simp1 env)
                                             (value-of-simple-exp simp2 env)))
    (cps-zero?-exp(simp1) (prim-zero? (value-of-simple-exp simp1 env)))
    (cps-proc-exp (vars body) (proc-val (compound vars body env)))))

;end-cont : () → Cont
(define (end-cont)
  (lambda (val)
    (begin
      ;(eopl:printf "End of computation.~%")
      val)))

;apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure/k
  (lambda (proc1 args)
    (cases proc proc1
      (compound (vars body saved-env)
                (value-of/k body 
                            (extend-env+ vars args saved-env)))
      (primitive (name op) (apply op args)))))

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

(define (prim-empty-list)
  (null-val))

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
        (cons 'empty-list prim-empty-list)))

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

(define (ormap op lst1)
  (if (null? lst1)
      #f
      (or (op (car lst1)) (ormap op (cdr lst1)))))

(define (andmap op lst1)
  (if (null? lst1)
      #t
      (and (op (car lst1)) (andmap op (cdr lst1)))))

;test
(run "1") ; 1
(run "i") ;1
(run "cons");|#<primitive:cons>|
(run "(empty-list)");'()
(run "let i=2 v=i a=v in (list i a x)") ;(2 5 10)
(run "let double = proc (x) (* x 2)
      in (double 3)") ;6
; zero? and - are keywords but not primitives here
; because procedure calls are TfExp, so we can't use them
; in non tail positions.
(run "letrec even(x) = if zero?(x) then true else (odd -(x 1))
               odd(x) = if zero?(x) then false else (even -(x 1))
        in (odd 3)") ;#t
(run "letrec even(x) = if zero?(x) then true else (odd -(x 1))
               odd(x) = if zero?(x) then false else (even -(x 1))
        in (even 3)") ;#f
