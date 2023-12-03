; Exercise 6.1 [*] Consider figure 6.2 without `(set! pc fact/k)` in the definition of
; `fact/k` and without `(set! pc apply-cont)` in the definition of `apply-cont`.
; Why does the program still work?

; When calling `fact/k`, the same logic repeats until n = 0.
; Similarly, when executing continuations, the same logic repeats until reaching the end-cont

;Exercise 6.2 [*] Prove by induction on n that for any g, `(fib/k n g) = (g (fib n))`.

; For base step, `(fib/k 0 g) = (g 1) = (g (fib 0))`
;                `(fib/k 1 g) = (g 1) = (g (fib 1))`
; For induction setep, we assume that the equation is valid for n = k, and n = k+1, i.e.,
; `(fib/k k g) = (g (fib k))` and `(fib/k k+1 g) = (g (fib k+1))`
; then (fib/k k+2 g) = (fib/k k+1 (lambda (val1) (fib/k k (lambda (val2) (g (+ val1 val2))))))
;                    = ((lambda (val1) (fib/k k (lambda (val2) (g (+ val1 val2)))))
;                       (fib k+1)) ; by the induction hypothesis
;                    = (fib/k k (lambda (val2) (g (+ (fib k+1) val2))))
;                    = ((lambda (val2) (g (+ (fib k+1) val2)))
;                       (fib/k)) ; by the induction hypothesis
;                   = (g (+ (fib k+1) (fib k)))
;                   = (g (fib k+2)) ; by the definition of Fibonacci sequence

;Exercise 6.3 [*] Rewrite each of the following Scheme expressions in continuationpassing style.
;Assume that any unknown functions have also been rewritten in CPS.

;1. (lambda (x y) (p (+ 8 x) (q y)))
;   (lambda (x y cont) (q y (lambda (v1) (p (+ 8 x) v1 cont))))
;2. (lambda (x y u v) (+ 1 (f (g x y) (+ u v))))
;   (lambda (x y u v cont) (g x y (lambda (v1) (f v1 (+ u v) (lambda (v2) (cont (+ 1 v2)))))))
;3. (+ 1 (f (g x y) (+ u (h v))))
;   (g x y (lambda (v1) (h v (lambda (v2) (f v1 (+ u v2) (lambda (v3) (cont (+ 1 v3))))))))
;4. (zero? (if a (p x) (p y)))
;   (if a (p x zero? (p y zero?))
;5. (zero? (if (f a) (p x) (p y)))
;   (f a (lambda (v1) (if v1 (p x zero?) (p y zero?))))
;6. (let ((x (let ((y 8)) (p y)))) x)
;   (let ((y 8))
;     (p y (lambda (v1)
;             (let ((x v1))
;                x))))
;7. (let ((x (if a (p x) (p y)))) x)
;   (let ((cont (lambda (v1)
;                 (let ((x v1))
;                    x)))
;     (if a (p x cont) (p y cont))))


