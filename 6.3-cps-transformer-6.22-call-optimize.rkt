#lang eopl
; 6.3 CPS transformer (CPS-IN -> CPS-OUT)
; Exercise 6.22 [*] Sometimes, when we generate (K simp), K is already a proc-exp.
;Modify make-send-to-cont to generate this better code. When does the new rule apply?

; when the operand position is not a simpleexp
; e.g. (transform "zero?(let x=1 in x)") 

(define in-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier ((or letter "*" "/" "?") (arbno (or letter digit "+" "-" "*" "/" "?"))) symbol)
    (identifier ((or "+" "-")) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define in-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression expression ")") diff-exp)
    (expression ("+" "(" (arbno expression) ")") sum-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression) letrec-exp)
    (expression ("(" expression  (arbno expression) ")") call-exp)
    ))

(sllgen:make-define-datatypes in-spec in-grammar)
(define list-in-datatypes
  (lambda ()
    (sllgen:list-define-datatypes in-spec in-grammar)))
(define just-scan
  (sllgen:make-string-scanner in-spec in-grammar))
(define scan&parse
  (sllgen:make-string-parser in-spec in-grammar))

(define out-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier ((or letter "*" "/" "?") (arbno (or letter digit "+" "-" "*" "/" "?"))) symbol)
    (identifier ((or "+" "-")) symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)))

(define out-grammar
  '((cps-program (tfexp) cps-a-program)
    (simpleexp (number) cps-const-exp)
    (simpleexp (identifier) cps-var-exp)
    (simpleexp ("-" "(" simpleexp simpleexp ")") cps-diff-exp)
    (simpleexp ("+" "(" (arbno simpleexp) ")") cps-sum-exp)
    (simpleexp ("zero?" "(" simpleexp ")") cps-zero?-exp)
    (simpleexp ("proc" "(" (arbno identifier) ")" tfexp) cps-proc-exp)
    (tfexp (simpleexp) simple-exp->exp)
    (tfexp ("let" (arbno identifier "=" simpleexp) "in" tfexp) cps-let-exp)
    (tfexp ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp) "in" tfexp) cps-letrec-exp)
    (tfexp ("if" simpleexp "then" tfexp "else" tfexp) cps-if-exp)
    (tfexp ("(" simpleexp (arbno simpleexp)")") cps-call-exp)))

(sllgen:make-define-datatypes out-spec out-grammar)
(define list-out-datatypes
  (lambda ()
    (sllgen:list-define-datatypes out-spec out-grammar)))

; transformer
;cps-of-program : InpExp → TfExp
(define cps-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (cps-a-program
                  (cps-of-exps (list exp1)
                               (lambda (new-args)
                                 (simple-exp->exp (car new-args)))))))))

;cps-of-exps : Listof(InpExp) × (Listof(InpExp) → TfExp) → TfExp
(define cps-of-exps
  (lambda (exps builder)
    (let cps-of-rest ((exps exps))
      ;cps-of-rest : Listof(InpExp) → TfExp
      (let ((pos (list-index
                  (lambda (exp)
                    (not (inp-exp-simple? exp)))
                  exps)))
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ((var (fresh-identifier 'var)))
              (cps-of-exp
               (list-ref exps pos)
               (cps-proc-exp (list var)
                             (cps-of-rest
                              (list-set exps pos (var-exp var)))))))))))

;cps-of-exp : InpExp × SimpleExp → TfExp
(define cps-of-exp
  (lambda (exp k-exp)
    (cases expression exp
      (zero?-exp (exp1)
                 (cps-of-zero?-exp exp1 k-exp))
      (diff-exp (exp1 exp2)
                (cps-of-diff-exp exp1 exp2 k-exp))
      (sum-exp (exps) (cps-of-sum-exp exps k-exp))
      (if-exp (exp1 exp2 exp3)
              (cps-of-if-exp exp1 exp2 exp3 k-exp))
      (let-exp (vars exps body)
               (cps-of-let-exp vars exps body k-exp))
      (letrec-exp (p-names b-varss p-bodies letrec-body)
                  (cps-of-letrec-exp
                   p-names b-varss p-bodies letrec-body k-exp))
      (call-exp (rator rands)
                (cps-of-call-exp rator rands k-exp))
      (else (make-send-to-cont k-exp (cps-of-simple-exp exp))))))

;inp-exp-simple? : InpExp → Bool
(define inp-exp-simple?
  (lambda (exp)
    (cases expression exp
      (const-exp (num) #t)
      (var-exp (var) #t)
      (diff-exp (exp1 exp2)
                (and (inp-exp-simple? exp1) (inp-exp-simple? exp2)))
      (zero?-exp (exp1) (inp-exp-simple? exp1))
      (proc-exp (ids exp) #t)
      (sum-exp (exps) (every? inp-exp-simple? exps))
      (else #f))))

;cps-of-simple-exp : InpExp → SimpleExp
;usage: assumes (inp-exp-simple? exp).
(define cps-of-simple-exp
  (lambda (exp)
    (cases expression exp
      (const-exp (num) (cps-const-exp num))
      (var-exp (var) (cps-var-exp var))
      (diff-exp (exp1 exp2)
                (cps-diff-exp
                 (cps-of-simple-exp exp1)
                 (cps-of-simple-exp exp2)))
      (zero?-exp (exp1)
                 (cps-zero?-exp (cps-of-simple-exp exp1)))
      (proc-exp (ids exp)
                (cps-proc-exp (append ids (list 'k%00))
                              (cps-of-exp exp (cps-var-exp 'k%00))))
      (sum-exp (exps)
               (cps-sum-exp (map cps-of-simple-exp exps)))
      (else
       (report-invalid-exp-to-cps-of-simple-exp exp)))))

(define (report-invalid-exp-to-cps-of-simple-exp exp)
  (eopl:error 'cps-of-simple-exp "invalid simple exp ~s" exp))

;cps-of-zero?-exp : InpExp × SimpleExp → TfExp
(define cps-of-zero?-exp
  (lambda (exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (make-send-to-cont
                    k-exp
                    (cps-zero?-exp
                     (car simples)))))))

;cps-of-sum-exp : Listof(InpExp) × SimpleExp → TfExp
(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (simples)
                   (make-send-to-cont
                    k-exp
                    (cps-sum-exp simples))))))

;cps-of-diff-exp : InpExp × InpExp × SimpleExp → TfExp
(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps
     (list exp1 exp2)
     (lambda (simples)
       (make-send-to-cont
        k-exp
        (cps-diff-exp
         (car simples)
         (cadr simples)))))))

;cps-of-if-exp : InpExp × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (simples)
                   (cps-if-exp (car simples)
                               (cps-of-exp exp2 k-exp)
                               (cps-of-exp exp3 k-exp))))))

;cps-of-let-exp : Var × InpExp × InpExp × SimpleExp → TfExp
(define cps-of-let-exp
  (lambda (ids rhss body k-exp)
    (cps-of-exps rhss
                 (lambda (simples)
                   (cps-let-exp ids
                                simples
                                (cps-of-exp body k-exp))))))
;cps-of-letrec-exp :
;Listof(Var) × Listof(Listof(Var)) × Listof(InpExp) × SimpleExp → TfExp
(define cps-of-letrec-exp
  (lambda (p-names b-varss p-bodies letrec-body k-exp)
    (cps-letrec-exp
     p-names
     (map
      (lambda (b-vars) (append b-vars (list 'k%00)))
      b-varss)
     (map
      (lambda (p-body)
        (cps-of-exp p-body (cps-var-exp 'k%00)))
      p-bodies)
     (cps-of-exp letrec-body k-exp))))

;cps-of-call-exp : InpExp × Listof(InpExp) × SimpleExp → TfExp
(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                 (lambda (simples)
                   (cps-call-exp
                    (car simples)
                    (append (cdr simples) (list k-exp)))))))

;make-send-to-cont : SimpleExp × SimpleExp → TfExp
(define make-send-to-cont
  (lambda (k-exp simple-exp)
    (cases simpleexp k-exp
      (cps-proc-exp (vars body)
                    (cps-let-exp vars (list simple-exp) body))
      (else (cps-call-exp k-exp (list simple-exp))))))

(define fresh-identifier
  (let ((i 0))
    (lambda (identifier)
      (set! i (+ i 1))
      (string->symbol (string-append (symbol->string identifier) (number->string i))))))

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
               (empty-env)))

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

;evaluation
;value-of : TfExp × Env × Cont → FinalAnswer
(define value-of
  (lambda (exp env)
    (cases tfexp exp
      (simple-exp->exp (simple)
                       (value-of-simple-exp simple env))
      (cps-let-exp (vars rhss body)
                   (let ((vals (map (lambda (rhs) (value-of-simple-exp rhs env)) rhss)))
                     (value-of body
                               (extend-env+ vars vals env))))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                      (value-of letrec-body
                                (extend-env-rec** p-names b-varss p-bodies env)))
      (cps-if-exp (simple1 body1 body2)
                  (if (expval->bool (value-of-simple-exp simple1 env))
                      (value-of body1 env)
                      (value-of body2 env)))
      (cps-call-exp (rator rands)
                    (let ((rator-proc
                           (expval->proc
                            (value-of-simple-exp rator env)))
                          (rand-vals
                           (map
                            (lambda (simple)
                              (value-of-simple-exp simple env))
                            rands)))
                      (apply-procedure rator-proc rand-vals))))))

(define (value-of-simple-exp simexp env)
  (cases simpleexp simexp
    (cps-const-exp (num) (num-val num))
    (cps-var-exp (var) (apply-env env var))
    (cps-diff-exp (simp1 simp2)
                  (let ((val1 (value-of-simple-exp simp1 env))
                        (val2 (value-of-simple-exp simp2 env)))
                    (prim-arith- val1 val2)))
    (cps-sum-exp (simps) (apply prim-arith+ (map (lambda (simp) (value-of-simple-exp simp env)) simps)))
    (cps-zero?-exp(simp1) (prim-zero? (value-of-simple-exp simp1 env)))
    (cps-proc-exp (vars body) (proc-val (compound vars body env)))))

;apply-procedure : Proc × ExpVal → ExpVal
(define apply-procedure
  (lambda (proc1 args)
    (cases proc proc1
      (compound (vars body saved-env)
                (value-of body
                          (extend-env+ vars args saved-env)))
      (primitive (name op) (apply op args)))))

(define (value-of-cps pgm)
  (cases cps-program pgm
    (cps-a-program (tfexp1) (value-of tfexp1 (init-env)))))

(define (transform string)
  (cps-of-program (scan&parse string)))

(define (run string)
  (let ((transformed (cps-of-program (scan&parse string))))
    (expval->sexp (value-of-cps transformed))))

; ****primitives****
; arithmetic operations
; ExpVal(Int) × ExpVal(Int) → ExpVal(Int)
(define (prim-arith+ val1 . vals)
  (apply arith-bin + val1 vals))

(define (prim-arith- val1 val2)
  (arith-bin - val1 val2))

(define (prim-arith* val1 . vals)
  (apply arith-bin * val1 vals))

(define (prim-arith/ val1 val2)
  (arith-bin quotient val1 val2))

(define (arith-bin proc val1 . vals)
  (let ((num1 (expval->num val1)))
    (num-val (apply proc num1 (map expval->num vals)))))

(define (prim-minus val1)
  (num-val (- (expval->num val1))))

(define (prim-zero? val1)
  (if (zero? (expval->num val1))
      true
      false))

; utils
(define (list-index pred lst)
  (define (iter l i)
    (if (null? l)
        #f
        (let ((a (car l)))
          (if (pred a)
              i
              (iter (cdr l) (+ i 1))))))
  (iter lst 0))

(define (every? pred lst)
  (cond
    ((null? lst) #t)
    ((not (pred (car lst))) #f)
    (else (every? pred (cdr lst)))))

(define (list-set lst n x)
  (cond
    ((null? lst) (eopl:error 'list-set "list too short"))
    ((= n 0) (cons x (cdr lst)))
    (else (cons (car lst) (list-set (cdr lst) (- n 1) x)))))

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

(run "1") ; 1
(run "i") ; 1
(run "-(2 1)") ;1
(run "+(1 1 1)") ;3
(run "zero?(0)") ;#t
(run "proc (x y) +(x y)") ;|#<procedure>|
(run "if zero?(0) then 1 else 2") ; 1
(run "if zero?(1) then 1 else 2") ; 2
(run "let x = 1
          inc = proc (x) +(x 1)
      in (inc x)") ;2
(run "letrec sum(n) = if zero?(n)
                       then 0
                       else +(n (sum -(n 1)))
      in (sum 3)") ;6