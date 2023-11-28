#lang eopl
; Thread (based on Exercise 5.55)
; Exercise 5.57 [***] There are lots of different synchronization mechanisms in your
;favorite OS book. Pick three and implement them in this framework.

; we already added semaphore. now we add condition variable and waittid

;Bounce = ExpVal ∪ (() → Bounce)
;ExpVal = Int+Bool+Null+Pair+Proc+Mutex+Semaphore+CondVar
;DenVal = Ref(ExpVal)
 
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
;Expression ::= cwcc Expression
;               cwcc-exp (exp1)
;Expression ::= spawn Expression
;               spawn-exp (exp1)
;Expression ::= yield
;               yield-exp
;Expression ::= set Identifier = Expression
;               set-exp (var exp1)
;Expression ::= mutex
;               mutex-exp
;Expression ::= semaphore Expression
;               semaphore-exp (exp1)
;Expression ::= condvar
;               condvar-exp
;Expression ::= wait Expression
;               wait-exp (exp1)
;Expression ::= singal Expression
;               signal-exp (exp1)
;Expression ::= waitcond Expression Expression
;               waitcond-exp (condexp procexp)
;Expression ::= waitcondmutex Expression Expression Expression ; wait on cond and unlock the mutex, then acquire the mutex before returning .
;               waitcondmutex-exp (condexp mtxexp procexp)
;Expression ::= notifyone Expression
;               notifyone-exp (exp1)
;Expression ::= notifyall Expression
;               notifyall-exp (exp1)
;Expression ::= kill Expression
;               kill-exp (exp1)
;Expression ::= nop Expression
;               nop-exp (exp1)
;Expression ::= send Expression to Expression
;               send-exp (exp1 exp2)
;Expression ::= recv
;               recv-exp ()
;Expression ::= waittid Expression ; wait the child thread specified by the id. 0 means all, 1 means any one
;               waittid-exp (exp1)
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
    (identifier ((or letter "*" "/" "?" "_") (arbno (or letter digit "+" "-" "*" "/" "?" "_"))) symbol)
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
    (expression ("letcc" identifier "in" expression) letcc-exp)
    (expression ("throw" expression "to" expression) throw-exp)
    (expression ("cwcc" expression) cwcc-exp)
    (expression ("spawn" expression) spawn-exp)
    (expression ("yield") yield-exp)
    (expression ("set" identifier "=" expression) set-exp)
    (expression ("mutex") mutex-exp)
    (expression ("semaphore" expression) semaphore-exp)
    (expression ("condvar") condvar-exp)
    (expression ("wait" expression) wait-exp)
    (expression ("signal" expression) signal-exp)
    (expression ("waitcond" expression expression) waitcond-exp)
    (expression ("waitcondmutex" expression expression expression) waitcondmutex-exp)
    (expression ("notifyone" expression) notifyone-exp)
    (expression ("notifyall" expression) notifyall-exp)
    (expression ("kill" expression) kill-exp)
    (expression ("nop" expression) nop-exp)
    (expression ("send" expression "to" expression) send-exp)
    (expression ("recv") recv-exp)
    (expression ("waittid" expression) waittid-exp)
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
  (cont-val (cont continuation?))
  (mutex-val (a-mutex mutex?))
  (semaphore-val (a-semaphore semaphore?))
  (condvar-val (a-condvar condvar?)))

; procedure
(define-datatype proc proc?
  (compound (vars (list-of identifier?)) (body expression?) (env env?) (trace boolean?))
  (primitive (name identifier?) (op procedure?))
  (cwccproc (saved-cont continuation?)))

(define-datatype mutex mutex?
  (a-mutex
   (ref-to-holder reference?) ; if no holder, is #f; else is the thread
   (ref-to-wait-queue reference?)))

(define-datatype semaphore semaphore?
  (a-semaphore
   (ref-to-count reference?)
   (ref-to-wait-queue reference?)))

(define-datatype condvar condvar?
  (a-condvar
   (ref-to-wait-queue reference?)))

; ====thread====
(define-datatype thread thread?
  (a-thread
   (id integer?)
   (pid integer?)
   (ref-thunk reference?) ; reference of the procedure to run when the thread is ready
   (ref-time-remaining reference?) ; reference of the integer
   (ref-buffer reference?) ; reference of the buffer used to receive message from other threads
   (buffer-mtx mutex?)     ; mutex of the buffer
   (ref-state reference?) ;reference of the current state of the thread: running, ready, waiting-mutex, waiting-msg, waiting-condvar, waiting-child, zombie, dead
   (ref-waiting-lock reference?) ; reference of the mutex/semaphore that the thread is currently waiting for
   (ref-holding-mutexes reference?) ; reference of the mutexes that the thread is currently holding
   (ref-children reference?) ; reference of the child threads (queue)
   ))

(define (get-thread-field th field)
  (cases thread th
    (a-thread (id pid ref-thunk ref-time-remaining ref-buffer buffer-mtx ref-state ref-waiting-lock ref-holding-mutexes ref-children)
              (case field
                ((id) id)
                ((pid) pid)
                ((thunk) (deref ref-thunk))
                ((time-remaining) (deref ref-time-remaining))
                ((buffer) (deref ref-buffer))
                ((buffer-mtx) buffer-mtx)
                ((state) (deref ref-state))
                ((waiting-lock) (deref ref-waiting-lock))
                ((holding-mutexes) (deref ref-holding-mutexes))
                ((children) (deref ref-children))
                (else (eopl:error 'get-thread-field "invalid field ~s to get" field))))))

(define (get-thread-id th) (get-thread-field th 'id))
(define (get-thread-pid th) (get-thread-field th 'pid))
(define (get-thread-thunk th) (get-thread-field th 'thunk))
(define (get-thread-time-remaining th) (get-thread-field th 'time-remaining))
(define (get-thread-buffer th) (get-thread-field th 'buffer))
(define (get-thread-buffer-mtx th) (get-thread-field th 'buffer-mtx))
(define (get-thread-state th) (get-thread-field th 'state))
(define (get-thread-waiting-lock th) (get-thread-field th 'waiting-lock))
(define (get-thread-holding-mutexes th) (get-thread-field th 'holding-mutexes))
(define (get-thread-children th) (get-thread-field th 'children))

(define (set-thread-field th field val)
  (cases thread th
    (a-thread (id pid ref-thunk ref-time-remaining ref-buffer buffer-mtx ref-state ref-waiting-lock ref-holding-mutexes ref-children)
              (case field
                ((thunk) (setref! ref-thunk val))
                ((time-remaining) (setref! ref-time-remaining val))
                ((buffer) (setref! ref-buffer val))
                ((state) (setref! ref-state val))
                ((waiting-lock) (setref! ref-waiting-lock val))
                ((holding-mutexes) (setref! ref-holding-mutexes val))
                ((children) (setref! ref-children val))
                (else (eopl:error 'set-thread-field "invalid field ~s to set" field))))))

(define (set-thread-thunk th val) (set-thread-field th 'thunk val))
(define (set-thread-time-remaining th val) (set-thread-field th 'time-remaining val))
(define (set-thread-buffer th val) (set-thread-field th 'buffer val))
(define (set-thread-state th val) (set-thread-field th 'state val))
(define (set-thread-waiting-lock th val) (set-thread-field th 'waiting-lock val))
(define (set-thread-holding-mutexes th val) (set-thread-field th 'holding-mutexes val))
(define (set-thread-children th val) (set-thread-field th 'children val))


(define (insert-mutex mtx mtxes)
  (cons mtx mtxes))

(define (remove-mutex mtx mtxes)
  (let loop ((ms mtxes))
    (if (null? ms)
        '()
        (if (eq? mtx (car ms))
            (cdr ms)
            (cons (car ms) (loop (cdr ms)))))))

(define (insert-holding-mutex th mtx)
  (let ((mutexes (get-thread-holding-mutexes th)))
    (set-thread-holding-mutexes the-current-thread (insert-mutex mtx mutexes))))

(define (remove-holding-mutex th mtx)
  (let ((mutexes (get-thread-holding-mutexes th)))
    (set-thread-holding-mutexes the-current-thread (remove-mutex mtx mutexes))))

(define (add-child th child)
  (let ((children (get-thread-children th)))
    (set-thread-children th (cons child children))))

(define (new-thread pid thunk)
  (let* ((id (new-thread-id))
         (th (a-thread id (or pid id)
                       (newref thunk)
                       (newref the-max-time-slice)
                       (newref (empty-queue)) ;buffer
                       (new-mutex) ;buffer-mutex
                       (newref #f) ;state
                       (newref #f) ;waiting-lock
                       (newref '()) ;holding-mutexes
                       (newref '()) ;children
                       )))
    (insert-thread id th)
    th))

(define (insert-thread id th)
  (set! the-threads (cons (cons id th) the-threads)))

(define (remove-thread searched-id)
  (set! the-threads
        (let loop ((ths the-threads))
          (if (null? ths)
              '()
              (if (= searched-id (caar ths))
                  (cdr ths)
                  (cons (car ths) (loop (cdr ths))))))))

(define (find-thread id)
  (let ((res (assq id the-threads)))
    (if res
        (cdr res)
        res)))

(define (notify-parent-if-wait th)
  (let* ((p (find-thread (get-thread-pid th)))
         (state (get-thread-state p)))
    (if (eq? state 'waiting-child)
        (place-on-ready-queue! p)
        (nop))))

(define (wait-child id cont)
  ; returns #f if no children or all children are dead, the specified id isn't a child or not existent.
  ; returns the thread id(or #t when waiting all children) if the specified child(ren) is/are over
  ; otherwise, suspend the thread again
  (let* ((children (get-thread-children the-current-thread))
         (has-non-dead (ormap (lambda (c) (not (eq? 'dead (get-thread-state c)))) children)))
    (if (not has-non-dead)
        (apply-cont cont false)
        (case id
          ((0) (if (andmap (lambda (c)
                             (let ((state (get-thread-state c)))
                               (case state
                                 ((dead) #t)
                                 ((zombie) (set-thread-state c 'dead) #t)
                                 (else #f))))
                           children)
                   (apply-cont cont true)
                   (continue-wait-child id cont))) ; all
          ((1) (let ((cid (ormap (lambda (c)
                                  (let ((state (get-thread-state c)))
                                    (case state
                                      ((zombie) (set-thread-state c 'dead) (get-thread-id c))
                                      (else #f))))
                                children)))
                 (if cid
                     (apply-cont cont (num-val cid))
                     (continue-wait-child id cont)))) ; any
          (else (let ((c (find-thread id))) ; specified one
                  (if c
                      (let ((pid (get-thread-pid c))
                            (id (current-thread-id)))
                        (if (eq? pid id)
                            (let ((state (get-thread-state c)))
                              (case state
                                ((zombie) (set-thread-state c 'dead) (apply-cont cont (num-val (get-thread-id c))))
                                ((dead) (apply-cont cont false))
                                (else (continue-wait-child id cont))))
                            (apply-cont cont false)))
                      (apply-cont cont false))))))))

(define (continue-wait-child id cont)
  (set-thread-thunk the-current-thread (lambda () (wait-child id cont)))
  (set-thread-state the-current-thread 'waiting-child)
  (run-next-thread))

(define next-thread-id 0)
(define (new-thread-id)
  (set! next-thread-id (+ next-thread-id 1))
  next-thread-id)

(define (current-thread-id)
  (get-thread-id the-current-thread))

(define (remove-thread-from-queue q th)
  (let loop ((q q))
    (if (empty? q)
        (eopl:error 'remove-thread-from-queue "thread (id: ~s) isn't in the queue" (get-thread-id th))
        (if (eq? th (car q))
            (cdr q)
            (cons (car q) (loop (cdr q)))))))

(define (kill-thread id)
  (let ((th (find-thread id)))
    (if th
        (begin (destroy-thread th) #t)
        #f)))

; the cleanup job, specifically,
; - release the mutexes that it's holding
; - remove the thread from the waiting queue or the ready queue.
(define (destroy-thread th)
  (let ((mutexes (get-thread-holding-mutexes th))
        (state (get-thread-state th)))
    (for-each (lambda (mtx) (signal-mutex mtx th)) mutexes)
    (case state
      ((ready) (set! the-ready-queue (remove-thread-from-queue the-ready-queue th)))
      ((waiting-mutex)
       (let* ((mtx (get-thread-waiting-lock th))
              (wait-queue (get-mutex-wait-queue mtx)))
         (set-mutex-wait-queue mtx (remove-thread-from-queue wait-queue th))))
      ((waiting-semaphore)
       ((let* ((sem (get-thread-waiting-lock th))
               (wait-queue (get-semaphore-wait-queue sem)))
          (set-semaphore-wait-queue sem (remove-thread-from-queue wait-queue th)))))
      ((waiting-condvar)
       ((let* ((cond (get-thread-waiting-lock th))
               (wait-queue (get-condvar-wait-queue cond)))
          (set-condvar-wait-queue cond (remove-thread-from-queue wait-queue th)))))
      )
    (set-thread-state th 'zombie)
    (notify-parent-if-wait th)))

;interthread communication
(define (send-message tid expval cont)
  (let ((th (find-thread tid)))
    (let ((m (get-thread-buffer-mtx th))
          (buf (get-thread-buffer th)))
      (set-thread-thunk the-current-thread
                        (lambda ()
                          (if (and (empty? buf) (eq? (get-thread-state th) 'waiting-msg))
                              (place-on-ready-queue! th)
                              (nop))
                          (enqueue buf expval)
                          (signal-mutex m the-current-thread)
                          (apply-cont cont (num-val 55))))
      (wait-for-mutex m the-current-thread))))

(define (recv-message cont)
  (let ((m (get-thread-buffer-mtx the-current-thread))
        (buf (get-thread-buffer the-current-thread)))
    (set-thread-thunk the-current-thread
                      (lambda ()
                        (if (empty? buf)
                            (begin (signal-mutex m the-current-thread)
                                   (set-thread-state the-current-thread 'waiting-msg)
                                   (set-thread-thunk the-current-thread (lambda () (recv-message cont)))
                                   (run-next-thread))
                            (dequeue buf (lambda (first rest)
                                           (set-thread-buffer the-current-thread rest)
                                           (signal-mutex m the-current-thread)
                                           (apply-cont cont first))))))
    (wait-for-mutex m the-current-thread)))

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
                                                                             (symbol->string name) ">")))
                         (cwccproc (saved-cont) (string->symbol "#<cwccproc>"))))
    (cont-val (cont) (string->symbol "#<continuation>"))
    (mutex-val (a-mutex) (string->symbol "#<mutex>"))
    (semaphore-val (a-semaphore) (string->symbol "#<semaphore>"))
    (condvar-val (a-condvar) (string->symbol "#<condvar>"))))

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

;expval->mutex : ExpVal → Mutex
(define (expval->mutex val)
  (cases expval val
    (mutex-val (a-mutex) a-mutex)
    (else (report-expval-extractor-error 'mutex val))))

;expval->semaphore : ExpVal → Semaphore
(define (expval->semaphore val)
  (cases expval val
    (semaphore-val (a-semaphore) a-semaphore)
    (else (report-expval-extractor-error 'semaphore val))))

;expval->condvar : ExpVal → CondVar
(define (expval->condvar val)
  (cases expval val
    (condvar-val (a-condvar) a-condvar)
    (else (report-expval-extractor-error 'condvar val))))

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
  (expval->sexp (value-of-program 40 (scan&parse string))))

;value-of-program : Program → FinalAnswer
(define (value-of-program timeslice pgm)
  (initialize-store!)
  (initialize-scheduler! timeslice)
  (cases program pgm
    (a-program (exp1)
               (begin (place-on-ready-queue!
                       (new-thread #f (lambda () (trampoline (value-of/k exp1 (init-env) (end-main-thread-cont))))))
                      (run-next-thread)))))

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
      (cwcc-exp (exp1) (value-of/k exp1 env (cwcc-cont env cont (get-saved-try-cont cont))))
      (spawn-exp (exp1) (value-of/k exp1 env (spawn-cont cont (get-saved-try-cont cont))))
      (yield-exp ()
                 (set-thread-thunk the-current-thread
                                   (lambda () (apply-cont cont (num-val 99))))
                 (place-on-ready-queue! the-current-thread)
                 (run-next-thread))
      (set-exp (var exp1) (value-of/k exp1 env (set-cont (apply-env env var) cont (get-saved-try-cont cont))))
      (mutex-exp () (apply-cont cont (mutex-val (new-mutex))))
      (semaphore-exp (exp1) (value-of/k exp1 env (semaphore-cont cont (get-saved-try-cont cont))))
      (condvar-exp () (apply-cont cont (condvar-val (new-condvar))))
      (wait-exp (exp1) (value-of/k exp1 env (wait-cont cont (get-saved-try-cont cont))))
      (signal-exp (exp1) (value-of/k exp1 env (signal-cont cont (get-saved-try-cont cont))))
      (waitcond-exp (exp1 procexp) (value-of/k exp1 env (waitcond-cont procexp env cont (get-saved-try-cont cont))))
      (waitcondmutex-exp (condexp mtxexp procexp) (value-of/k condexp env (waitcondmutex-cont mtxexp procexp env cont (get-saved-try-cont cont))))
      (notifyone-exp (exp1) (value-of/k exp1 env (notifyone-cont cont (get-saved-try-cont cont))))
      (notifyall-exp (exp1) (value-of/k exp1 env (notifyall-cont cont (get-saved-try-cont cont))))
      (kill-exp (exp1) (value-of/k exp1 env (kill-cont cont (get-saved-try-cont cont))))
      (call-exp (rator rands)
                (value-of/k rator env
                            (rator-cont rands env cont (get-saved-try-cont cont))))
      (nop-exp (exp1) (value-of/k exp1 env (nop-cont cont (get-saved-try-cont cont))))
      (send-exp (exp1 exp2) (value-of/k exp1 env (send-cont exp2 env cont (get-saved-try-cont cont))))
      (recv-exp () (recv-message cont))
      (waittid-exp (exp1) (value-of/k exp1 env (waittid-cont cont (get-saved-try-cont cont))))
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
   (saved-try-cont continuation?))
  (cwcc-cont
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (spawn-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (end-main-thread-cont)
  (end-subthread-cont)
  (set-cont
   (loc reference?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (wait-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (signal-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (kill-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (nop-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (send-cont
   (saved-exp expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (send-cont2
   (saved-val expval?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (semaphore-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (waitcond-cont
   (procexp expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (waitcond-cont2
   (saved-condvar condvar?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (waitcondmutex-cont
   (mtxexp expression?)
   (procexp expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (waitcondmutex-cont2
   (saved-condvar condvar?)
   (procexp expression?)
   (saved-env env?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (waitcondmutex-cont3
   (saved-condvar condvar?)
   (saved-mutex mutex?)
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (notifyone-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (notifyall-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?))
  (waittid-cont
   (saved-cont continuation?)
   (saved-try-cont continuation?)))

;apply-cont : Cont × ExpVal → Bounce
(define (apply-cont cont val)
  (if (decrement-timer!)
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
                     (apply-cont val saved-val))
        (cwcc-cont (saved-env saved-cont saved-try-cont)
                   (apply-procedure/k (expval->proc val) (list (proc-val (cwccproc saved-cont))) saved-cont))
        (spawn-cont (saved-cont saved-try-cont)
                    (let ((proc1 (expval->proc val))
                          (pid (current-thread-id)))
                      (let* ((nth (new-thread pid (lambda ()
                                                    (apply-procedure/k proc1
                                                                       (list (num-val (current-thread-id)))
                                                                       (end-subthread-cont)))))
                             (id (get-thread-id nth)))
                        (place-on-ready-queue! nth)
                        (add-child the-current-thread nth)
                        (apply-cont saved-cont (num-val id)))))
        (end-main-thread-cont ()
                              (set-final-answer! val)
                              (destroy-thread the-current-thread)
                              (run-next-thread))
        (end-subthread-cont ()
                            (destroy-thread the-current-thread)
                            (run-next-thread))
        (set-cont (loc saved-cont saved-try-cont)
                  (setref! loc val)
                  (apply-cont saved-cont (num-val 22)))
        (wait-cont (saved-cont saved-try-cont)
                   (set-thread-thunk the-current-thread (lambda () (apply-cont saved-cont (num-val 52))))
                   (cases expval val
                     (mutex-val (a-mutex) (wait-for-mutex a-mutex the-current-thread))
                     (semaphore-val (a-semaphore) (wait-for-semaphore a-semaphore the-current-thread))
                     (else (eopl:error 'apply-cont "invalid object to wait, must be a mutex or semaphore"))))
        (signal-cont (saved-cont saved-try-cont)
                     (cases expval val
                       (mutex-val (a-mutex) (signal-mutex a-mutex the-current-thread))
                       (semaphore-val (a-semaphore) (signal-semaphore a-semaphore))
                       (else (eopl:error 'apply-cont "invalid object to signal, must be a mutex or semaphore")))
                     (apply-cont saved-cont (num-val 53)))
        (kill-cont (saved-cont saved-try-cont)
                   (let* ((id (expval->num val))
                          (res (kill-thread id)))
                     (apply-cont saved-cont (bool-val res))))
        (nop-cont (saved-cont saved-try-cont)
                  (let ((n (expval->num val)))
                    (if (> n 0)
                        (apply-cont (nop-cont saved-cont saved-try-cont) (num-val (- n 1)))
                        (apply-cont saved-cont (num-val 54)))))
        (send-cont (saved-exp saved-env saved-cont saved-try-cont)
                   (value-of/k saved-exp saved-env (send-cont2 val saved-cont saved-try-cont)))
        (send-cont2 (saved-val saved-cont saved-try-cont)
                    (send-message (expval->num val) saved-val saved-cont))
        (semaphore-cont (saved-cont saved-try-cont)
                        (apply-cont saved-cont (semaphore-val (new-semaphore (expval->num val)))))
        (waitcond-cont (procexp saved-env saved-cont saved-try-cont)
                       (value-of/k procexp saved-env (waitcond-cont2 (expval->condvar val) saved-cont saved-try-cont)))
        (waitcond-cont2 (saved-condvar saved-cont saved-try-cont)
                        (let ((proc (expval->proc val)))
                          (set-thread-thunk the-current-thread (lambda () (apply-procedure/k proc '() saved-cont)))
                          (wait-for-condvar saved-condvar the-current-thread)))
        (waitcondmutex-cont (mtxexp procexp saved-env saved-cont saved-try-cont)
                            (value-of/k mtxexp saved-env (waitcondmutex-cont2 (expval->condvar val) procexp saved-env saved-cont saved-try-cont)))
        (waitcondmutex-cont2 (saved-condvar procexp saved-env saved-cont saved-try-cont)
                             (value-of/k procexp saved-env (waitcondmutex-cont3 saved-condvar (expval->mutex val) saved-cont saved-try-cont)))
        (waitcondmutex-cont3 (saved-condvar saved-mutex saved-cont saved-try-cont)
                             (let ((proc (expval->proc val)))
                               (set-thread-thunk the-current-thread
                                                 (lambda ()
                                                   (set-thread-thunk the-current-thread
                                                                     (lambda () (apply-procedure/k proc '() saved-cont)))
                                                   (wait-for-mutex saved-mutex the-current-thread)))
                               (wait-for-condvar-mutex saved-condvar saved-mutex the-current-thread)))
        (notifyone-cont (saved-cont saved-try-cont)
                        (notifyone-condvar (expval->condvar val))
                        (apply-cont saved-cont (num-val 56)))
        (notifyall-cont (saved-cont saved-try-cont)
                        (notifyall-condvar (expval->condvar val))
                        (apply-cont saved-cont (num-val 57)))
        (waittid-cont (saved-cont saved-try-cont)
                      (let ((id (expval->num val)))
                        (wait-child id saved-cont))))
      ; run out of time
      (begin (set-thread-thunk the-current-thread (lambda () (apply-cont cont val)))
             (set-thread-time-remaining the-current-thread the-max-time-slice)
             (place-on-ready-queue! the-current-thread)
             (run-next-thread))))

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
    (cwcc-cont (saved-env saved-cont saved-try-cont) saved-try-cont)
    (spawn-cont (saved-cont saved-try-cont) saved-try-cont)
    (end-main-thread-cont () cont)
    (end-subthread-cont () cont)
    (set-cont (loc saved-cont saved-try-cont) saved-try-cont)
    (wait-cont (saved-cont saved-try-cont) saved-try-cont)
    (signal-cont (saved-cont saved-try-cont) saved-try-cont)
    (kill-cont (saved-cont saved-try-cont) saved-try-cont)
    (nop-cont (saved-cont saved-try-cont) saved-try-cont)
    (send-cont (saved-exp saved-env saved-cont saved-try-cont) saved-try-cont)
    (send-cont2 (saved-val saved-cont saved-try-cont) saved-try-cont)
    (semaphore-cont (saved-cont saved-try-cont) saved-try-cont)
    (waitcond-cont (procexp saved-env saved-cont saved-try-cont) saved-try-cont)
    (waitcond-cont2 (saved-condvar saved-cont saved-try-cont) saved-try-cont)
    (waitcondmutex-cont (mtxexp procexp saved-env saved-cont saved-try-cont) saved-try-cont)
    (waitcondmutex-cont2 (saved-condvar procexp saved-env saved-cont saved-try-cont) saved-try-cont)
    (waitcondmutex-cont3 (saved-condvar saved-mutex saved-cont saved-try-cont) saved-try-cont)
    (notifyone-cont (saved-cont saved-try-cont) saved-try-cont)
    (notifyall-cont (saved-cont saved-try-cont) saved-try-cont)
    (waittid-cont (saved-cont saved-try-cont) saved-try-cont)
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
      (primitive (name op) (apply-cont cont (apply op args)))
      (cwccproc (saved-cont) (apply-cont saved-cont (car args))) ; must have and only have 1 arg
      )))

; ====store====
(define the-store 'uninitialized-store)

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

; ====scheduler====
;internal state
(define the-ready-queue 'uninitialized-ready-queue)
(define the-final-answer 'uninitialized-final-answer)
(define the-max-time-slice 'uninitialized-max-time-slice)
(define the-current-thread 'uninitialized-current-thread)
(define the-mutexes 'uninitialized-mutexes)
(define the-threads 'uninitialized-thread)

(define (empty-queue) '())

(define empty? null?)

(define (enqueue q val)
  (append q (list val)))

(define (dequeue q f)
  (f (car q) (cdr q)))

;initialize-scheduler! : Int → Unspecified
(define initialize-scheduler!
  (lambda (ticks)
    (set! the-ready-queue (empty-queue))
    (set! the-final-answer 'uninitialized-final-answer)
    (set! the-max-time-slice ticks)
    (set! the-current-thread 'uninitialized-current-thread)
    (set! next-thread-id 0)
    (set! the-mutexes '())
    (set! the-threads '())))

;place-on-ready-queue! : Thread → Unspecified
(define place-on-ready-queue!
  (lambda (th)
    (set-thread-state th 'ready)
    (set! the-ready-queue
          (enqueue the-ready-queue th))))

;run-next-thread : () → FinalAnswer
(define run-next-thread
  (lambda ()
    (if (empty? the-ready-queue)
        the-final-answer
        (dequeue the-ready-queue
                 (lambda (first-ready-thread other-ready-threads)
                   (set! the-ready-queue other-ready-threads)
                   (set! the-current-thread first-ready-thread)
                   (set-thread-state the-current-thread 'running)
                   (run-thread first-ready-thread))))))

(define (run-thread th)
  (cases thread th
    (a-thread (id pid ref-thunk ref-time-remaining ref-buffer buffer-mtx ref-state ref-waiting-mutex ref-holding-mutexes ref-children)
              (let ((thunk (deref ref-thunk)))
                (setref! ref-thunk #f)
                ;(display "run thread ")
                ;(display id)
                ;(display ", parent ")
                ;(display pid)
                ;(display ", time-remaining")
                ;(display time-remaining)
                ;(newline)
                (thunk)))))

;set-final-answer! : ExpVal → Unspecified
(define set-final-answer!
  (lambda (val)
    (set! the-final-answer val)))

;decrement-timer! : () → Boolean
;if no time remains, returns false; otherwise returns true
(define decrement-timer!
  (lambda ()
    (let ((time-remaining (get-thread-time-remaining the-current-thread)))
      (if (zero? time-remaining)
          #f
          (begin (set-thread-time-remaining the-current-thread (- time-remaining 1))
                 #t)))))

; ====mutex====
;new-mutex : () → Mutex
(define (new-mutex)
  (let ((mtx (a-mutex
              (newref #f)
              (newref (empty-queue)))))
    (set! the-mutexes (cons mtx the-mutexes))
    mtx))

(define (get-mutex-field mtx field)
  (cases mutex mtx
    (a-mutex (ref-to-holder ref-to-wait-queue)
             (case field
               ((holder) (deref ref-to-holder))
               ((wait-queue) (deref ref-to-wait-queue))))))

(define (get-mutex-holder mtx) (get-mutex-field mtx 'holder))
(define (get-mutex-wait-queue mtx) (get-mutex-field mtx 'wait-queue))

(define (set-mutex-field mtx field val)
  (cases mutex mtx
    (a-mutex (ref-to-holder ref-to-wait-queue)
             (case field
               ((holder) (setref! ref-to-holder val))
               ((wait-queue) (setref! ref-to-wait-queue val))))))

(define (set-mutex-holder mtx val) (set-mutex-field mtx 'holder val))
(define (set-mutex-wait-queue mtx val) (set-mutex-field mtx 'wait-queue val))

;wait-for-mutex : Mutex × Thread → FinalAnswer
;usage: waits for mutex to be open, then closes it.
(define (wait-for-mutex m th)
  (let ((holder (get-mutex-holder m)))
    (cond
      ((not holder) (set-mutex-holder m th)
                    (insert-holding-mutex th m)
                    ;(display (get-thread-id th))
                    ;(display " hold open mutex\n")
                    (run-thread th))
      ((eq? holder th) (run-thread th)) ; held by itself
      (else ; held by other
       (let ((wait-queue (get-mutex-wait-queue m)))
         ;(display (get-thread-id th))
         ;(display " wait for mutex \n")
         (set-mutex-wait-queue m (enqueue wait-queue th))
         (set-thread-waiting-lock th m)
         (set-thread-state th 'waiting-mutex)
         (run-next-thread))))))

;signal-mutex : Mutex × thread → ()
(define (signal-mutex m th)
  ;(display (get-thread-id th))
  ;(display " signal-mutex ")
  (let ((holder (get-mutex-holder m)))
    (if (eq? holder th)
        (let ((wait-queue (get-mutex-wait-queue m)))
          (remove-holding-mutex th m)
          (if (empty? wait-queue)
              (begin ;(display " no holder now\n")
                (set-mutex-holder m #f))
              (dequeue wait-queue
                       (lambda (first-waiting-th other-waiting-ths)
                         ;(display (get-thread-id first-waiting-th))
                         ;(display "hold mutex now\n")
                         (set-mutex-holder m first-waiting-th)
                         (set-mutex-wait-queue m other-waiting-ths)
                         (place-on-ready-queue! first-waiting-th)
                         (set-thread-waiting-lock first-waiting-th #f)))))
        (if holder
            (eopl:printf "thread ~s is releasing a mutex held by thread ~s\n" (get-thread-id th) (get-thread-id holder))
            (eopl:printf "thread ~s is releasing an open mutex\n" (get-thread-id th))))))

; ====semaphore====
;new-semaphore : (Int) → Mutex
(define (new-semaphore init-count)
  (a-semaphore (newref init-count) (newref (empty-queue))))

(define (get-semaphore-field sem field)
  (cases semaphore sem
    (a-semaphore (ref-to-count ref-to-wait-queue)
                 (case field
                   ((count) (deref ref-to-count))
                   ((wait-queue) (deref ref-to-wait-queue))))))

(define (get-semaphore-count sem) (get-semaphore-field sem 'count))
(define (get-semaphore-wait-queue sem) (get-semaphore-field sem 'wait-queue))

(define (set-semaphore-field sem field val)
  (cases semaphore sem
    (a-semaphore (ref-to-count ref-to-wait-queue)
                 (case field
                   ((count) (setref! ref-to-count val))
                   ((wait-queue) (setref! ref-to-wait-queue val))))))

(define (set-semaphore-count sem val) (set-semaphore-field sem 'count val))
(define (set-semaphore-wait-queue sem val) (set-semaphore-field sem 'wait-queue val))

(define (inc-semaphore-count sem)
  (let* ((count (get-semaphore-count sem))
         (ncount (+ count 1)))
    (set-semaphore-count sem ncount)
    ncount))

(define (dec-semaphore-count sem)
  (let* ((count (get-semaphore-count sem))
         (ncount (- count 1)))
    (set-semaphore-count sem ncount)
    ncount))

;wait-for-semaphore : Semaphore × Thread → FinalAnswer
;usage: waits for semaphore to have resource, then get one
(define (wait-for-semaphore sem th)
  ;(display (get-thread-id th))
  ;(display "wait-for-semaphore, ")
  (let ((count (dec-semaphore-count sem)))
    (if (< count 0)
        (let ((wait-queue (get-semaphore-wait-queue sem)))
          ;(display "no available, waiting...\n")
          (set-semaphore-wait-queue sem (enqueue wait-queue th))
          (set-thread-waiting-lock th sem)
          (set-thread-state th 'waiting-semaphore)
          (run-next-thread))
        (begin ;(display count)
          ;(display "left\n")
          (run-thread th)))))

;signal-semaphore : Semaphore × thread → ()
(define (signal-semaphore sem)
  (let ((count (inc-semaphore-count sem))
        (wait-queue (get-semaphore-wait-queue sem)))
    ;(display (current-thread-id))
    ;(display "signal-semaphore ")
    ;(display "count = ")
    ;(display count)
    ;(display " now\n")
    (if (not (empty? wait-queue))
        (dequeue wait-queue
                 (lambda (first others)
                   ;(display "wake up ")
                   ;(display (get-thread-id first))
                   ;(display "\n")
                   (place-on-ready-queue! first)
                   (set-semaphore-wait-queue sem others)
                   (set-thread-waiting-lock first #f)))
        (nop))))

; ====condvar====
;new-condvar : () → CondVar
(define (new-condvar)
  (a-condvar (newref (empty-queue))))

(define (get-condvar-field cond field)
  (cases condvar cond
    (a-condvar (ref-to-wait-queue)
               (case field
                 ((wait-queue) (deref ref-to-wait-queue))))))

(define (get-condvar-wait-queue cond) (get-condvar-field cond 'wait-queue))

(define (set-condvar-field cond field val)
  (cases condvar cond
    (a-condvar (ref-to-wait-queue)
               (case field
                 ((wait-queue) (setref! ref-to-wait-queue val))))))

(define (set-condvar-wait-queue cond val) (set-condvar-field cond 'wait-queue val))

;wait-for-condvar : CondVar × Thread → FinalAnswer
;usage: waits for condvar
(define (wait-for-condvar c th)
  (let ((wait-queue (get-condvar-wait-queue c)))
    ;(display (get-thread-id th))
    ;(display " wait for condvar \n")
    (set-condvar-wait-queue c (enqueue wait-queue th))
    (set-thread-waiting-lock th c)
    (set-thread-state th 'waiting-condvar)
    (run-next-thread)))

;wait-for-condvar-mutex : CondVar × Mutex × Thread → FinalAnswer
;usage: waits for condvar
(define (wait-for-condvar-mutex c m th)
  (let ((wait-queue (get-condvar-wait-queue c)))
    ;(display (get-thread-id th))
    ;(display " wait for condvar(unlock) \n")
    (signal-mutex m th)
    (set-condvar-wait-queue c (enqueue wait-queue th))
    (set-thread-waiting-lock th c)
    (set-thread-state th 'waiting-condvar)
    (run-next-thread)))

;notifyone-condvar : CondVar → ()
(define (notifyone-condvar c)
  ;(display (current-thread-id))
  ;(display " notifyone-condvar ")
  (let ((wait-queue (get-condvar-wait-queue c)))
    (if (empty? wait-queue)
        (begin ;(display " no one is waiting for the condvar\n")
          #t)
        (dequeue wait-queue
                 (lambda (first others)
                   ;(display "wake up ")
                   ;(display (get-thread-id first))
                   ;(newline)
                   (set-condvar-wait-queue c others)
                   (place-on-ready-queue! first)
                   (set-thread-waiting-lock first #f))))))

;notifyall-condvar : CondVar → ()
(define (notifyall-condvar c)
  ;(display (current-thread-id))
  ;(display " notifyall-condvar ")
  (let loop ((q (get-condvar-wait-queue c)))
    (if (empty? q)
        #t
        (dequeue q
                 (lambda (first rest)
                   ;(display "wake up ")
                   ;(display (get-thread-id first))
                   ;(newline)
                   (set-condvar-wait-queue c rest)
                   (place-on-ready-queue! first)
                   (set-thread-waiting-lock first #f)
                   (loop rest))))))


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
(define (ormap op lst1)
  (if (null? lst1)
      #f
      (or (op (car lst1)) (ormap op (cdr lst1)))))

(define (andmap op lst1)
  (if (null? lst1)
      #t
      (and (op (car lst1)) (andmap op (cdr lst1)))))

(define (filter pred lst . lsts)
  (reverse (apply fold/l (lambda (res e . l)
                           (if (apply pred e l)
                               (cons e res)
                               res))
                  '() lst lsts)))

(define (equal-length? l1 l2)
  (= (length l1) (length l2)))

(define (nop) #t)

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
(run "letcc cont in (+ 1 1)")
;2
(run "letcc cont in throw (+ 2 2) to cont")
;4
(run "cwcc proc (jmp) (+ 1 1)")
;2
(run "cwcc proc (jmp) (jmp (+ 2 2))")
;4
(run "letrec noisy(l) = if (null? l)
                        then 0
                        else begin (print (car l))
                                   (noisy (cdr l)) end
      in begin
           spawn proc (d) (noisy (list 1 2 3 4 5))
           spawn proc (d) (noisy (list 6 7 8 9 10))
           (print 100)
           33
         end")
;100 1 2 6 7 3 4 8 9 5 10
;(run "let buffer = 0
;      in let producer = proc (n)
;           letrec
;              wait(k) = if (zero? k)
;                        then set buffer = n
;                        else begin (print (+ k 200))
;                                   (wait (- k 1)) end
;           in (wait 5)
;         in let consumer = proc (id)
;                 letrec busywait (k) = if (zero? buffer)
;                                       then begin (print (+ k 100))
;                                                  (busywait (+ k 1)) end
;                                       else buffer
;                 in (busywait 0)
;            in begin spawn proc (d) (producer 44)
;                     (print 300)
;                     (consumer 86) end")
;300 100 205 204 101 102 203 202 103 104 201 105
(run "let x = 0
      in let mut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait mut
                                 set x = (+ x 1)
                                 signal mut
                           end
            in begin spawn (incr_x 100)
                     spawn (incr_x 200)
                     spawn (incr_x 300)
               end")

(run "begin spawn proc (dummy) (print 11)
            (print 22) end")
;22 11
(run "begin spawn proc (dummy) (print 11)
            yield
           (print 22) end")
;11 22
(run "let buffer = 0
      in let rdsem = semaphore 0
             wtsem = semaphore 1
      in let producer = proc (n)
           letrec
              loop(k) = if (zero? k)
                        then begin wait wtsem
                                   set buffer = n
                                   signal rdsem end
                        else begin (print (+ k 200))
                                   (loop (- k 1)) end
           in (loop 5)
         in let consumer = proc (id)
                            begin wait rdsem
                                  (print buffer)
                                  set buffer = 0
                                  signal wtsem end
            in begin spawn proc (d) (producer 44)
                     (print 300)
                     (consumer 86)
                     (print 400)
                     spawn proc (d) (producer 55)
                     spawn proc (d) (producer 66)
                     (consumer 87)
                     (consumer 88) end")
;300 205 204 203 202 201 44
;400 205 204 205 204 203 202 203 202 201 201 55 66

(run "let x = 0
      in let wtmut = mutex
      in let sem = semaphore 0
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                                 signal sem
                           end
            in begin spawn (incr_x 100)
                     spawn (incr_x 200)
                     spawn (incr_x 300)
                     wait sem
                     wait sem
                     wait sem
                     (print x)
               end")
;3

(run "let x = 0
      in let xmut = mutex
             sem = semaphore 0
         in let incr_x = proc (id)
                          proc (dummy)
                           begin (print id)
                                 wait xmut
                                 nop 50
                                 set x = (+ x 1)
                                 signal xmut
                                 (print (+ id x))
                                 signal sem
                           end
            in begin let id1 = spawn (incr_x 100)
                         id2 = spawn (incr_x 200)
                         id3 = spawn (incr_x 300)
                     in begin nop 10
                              (print kill id3)
                              wait sem
                              wait sem
                              (print x)
                              end
               end")
;kill id1: 100 200 300 #t 201 302 2
;kill id2: 100 200 300 #t 101 302 2
;kill id3: 100 200 300 #t 101 202 2

(run "let x = 0
          cv = condvar
      in let fn = proc (id)
                    begin
                     set x = id
                     nop 100
                     notifyone cv
                    end
          in begin spawn fn
                   (print waitcond cv proc () x)
             end")
;2

(run "let cv = condvar
          sem = semaphore 0
      in let fn = proc (id)
                   begin waitcond cv proc () (print id)
                         signal sem
                   end
         in begin spawn fn
                  spawn fn
                  spawn fn
                  yield
                  notifyall cv
                  wait sem
                  wait sem
                  wait sem
                  (print 1)
            end")
;2 3 4 1

(run "let cv = condvar
          mtx = mutex
          endsem = semaphore 0
          x = false
      in let init = proc (dummy)
                     begin wait mtx
                           set x = 0
                           yield
                           yield
                           yield
                           notifyall cv
                           signal mtx
                           signal endsem
                     end
             inc = proc (dummy)
                    begin wait mtx
                          (print waitcondmutex cv mtx proc () begin set x = (+ x 1) x end)
                          signal mtx
                          signal endsem
                    end
         in begin spawn inc
                  spawn inc
                  spawn inc
                  spawn inc
                  spawn init
                  wait endsem
                  wait endsem
                  wait endsem
                  wait endsem
                  wait endsem
                  (print 0)
            end")
; 1 2 3 4 0

(run "let x = 0
      in let wtmut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                           end
            in let id1 = spawn (incr_x 100)
                   id2 = spawn (incr_x 200)
                   id3 = spawn (incr_x 300)
               in begin (print waittid 0)
                        (print x)
                  end")
;#t 3

(run "let x = 0
      in let wtmut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                           end
            in let id1 = spawn (incr_x 100)
                   id2 = spawn (incr_x 200)
                   id3 = spawn (incr_x 300)
               in begin (print waittid id1)
                        (print waittid id2)
                        (print waittid id3)
                        (print x)
                  end")
; 2 3 4 3

(run "let x = 0
      in let wtmut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                           end
            in let id1 = spawn (incr_x 100)
                   id2 = spawn (incr_x 200)
                   id3 = spawn (incr_x 300)
               in begin (print waittid 1)
                        (print waittid 1)
                        (print waittid 1)
                        (print x)
                  end")
; 2 3 4 3

(run "let x = 0
      in let wtmut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                           end
            in let id1 = spawn (incr_x 100)
                   id2 = spawn (incr_x 200)
                   id3 = spawn (incr_x 300)
               in begin (print waittid 1)
                        (print waittid 0)
                        (print x)
                  end")
; 2 #t 3

(run "let x = 0
      in let wtmut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                           end
            in let id1 = spawn (incr_x 100)
                   id2 = spawn (incr_x 200)
                   id3 = spawn (incr_x 300)
               in begin (print waittid 10)
                        (print waittid 0)
                        (print x)
                  end")
; #f #t 3

(run "let x = 0
      in let wtmut = mutex
         in let incr_x = proc (id)
                          proc (dummy)
                           begin wait wtmut
                                 let tmp = x
                                 in begin yield
                                          set x = (+ tmp 1)
                                    end
                                 signal wtmut
                           end
            in let id1 = spawn (incr_x 100)
                   id2 = spawn (incr_x 200)
                   id3 = spawn (incr_x 300)
               in begin (print waittid 0)
                        (print waittid 0)
                        (print waittid 1)
                        (print waittid 2)
                        (print x)
                  end")
;#t #f #f #f 3