From Chapter 3, the exercises are in the source files. We implement the languages accumulatively and generally the latter exercises builds on the previous.
So the exercises may not be exactly the same as what's described on the book. We modify them to fit our languages.



## 1 Inductive Sets of Data

**Exercise 1.1 [*]** Write inductive definitions of the following sets. Write each definition in all three styles (top-down, bottom-up, and rules of inference). Using your rules, show the derivation of some sample elements of each set.

1. {3*n* + 2 | *n* ∈ *N*}
2. {2*n* + 3*m* + 1 | *n*, *m* ∈ *N*}
3. {(*n*, 2*n* + 1) | *n* ∈ *N*}
4. {(*n*, n^2) | *n* ∈ *N*} Do not mention squaring in your rules. As a hint, remember the equation (*n* + 1)^2 = *n*2 + 2*n* + 1.

top-down:  x is in S if and only if 1. x = 2 or 2. x - 3 ∈ S

bottom-up: S is the smallest set contained in N and satisfying the following two properties:

1. 2 ∈ S, and
2. if x ∈ S, then x + 3 ∈ S

rules-of-inference: skip



top-down: 1. x = 1 or 2. x -2 ∈ S or 3. x - 3 ∈ S

bottom-up: 1. x ∈ S, and 2. if x ∈ S, then x + 2∈ S, x + 3 ∈ S



top-down: x = (m, n) ∈ S if and only if 1. x = (0, 1) or 2. (m-1, n-2) ∈ S

bottom-up: 1. (0, 1) ∈ S and 2. if (m, n) ∈ S, then (m+1, n+2) ∈ S



top-down: 1. x = (0, 0) or 2. (m-1, n-2m+1) ∈ S

bottom-up: 1. (0, 0) ∈ S and 2. if (m, n) ∈ S, then (m+1, n+2m+1)∈ S



**Exercise 1.2 [\*\*]** What sets are defined by the following pairs of rules? Explain why.

the smallest set that satisfying
{(n, 7n+1) | n ∈ N}

{(n, 2^n) | n ∈ N}

{(n, Fib(n), Fib(n+1)) | n ∈ N, Fib(0)=0, Fib(1)=1, Fib(n+2)=Fib(n)+Fib(n+1)}

{(n, 2n+1, n^2) | n ∈ N}

结论中每次加几，则表达式的斜率就为几，做个积分再把base case的值代入。



**Exercise 1.3 [\*]** Find a set *T* of natural numbers such that 0 ∈ *T*, and whenever *n* ∈ *T*, then *n* + 3 ∈ *T*, but *T* ≠ *S*, where *S* is the set defined in definition 1.1.2.

0 ∈ T, 1 ∈ T, and if n ∈ T,then n + 3∈ T



**Exercise 1.6 [\*]** If we reversed the order of the tests in nth-element, what would go wrong?

If `lst` is empty-list, then `(car lst)` or `(cdr lst)` will fail.

**Exercise 1.7 [\*\* ]** The error message from nth-element is uninformative. Rewrite nth-element so that it produces a more informative error message, such as “(a b c) does not have 8 elements.”

pass the original n, then report the original n on error message

**Exercise 1.8 [\*]** In the definition of remove-first, if the last line were replaced by (remove-first s (cdr los)), what function would the resulting procedure compute? Give the contract, including the usage statement, for the revised procedure.

sublist: Sym x Listof(Sym) -> Listof(Sym)

usage: (sublist s los) returns a sublist starting from the next symbol after the first occurence of the symbol s. If there is no occurrence of s in los, then () is returned.

```scheme
(define remove-first
  (lambda (s los)
    (if (null? los)
        '()
        (if (eqv? (car los) s)
            (cdr los)
            (remove-first s (cdr los))))))
```



**Exercise 1.9 [\*\*]** Define remove, which is like remove-first, except that it removes all occurrences of a given symbol from a list of symbols, not just the first.

```scheme
(define remove
  (lambda (s los)
    (if (null? los)
        '()
        (if (eqv? (car los) s)
            (remove (cdr los))
            (cons (car los) (remove s (cdr los)))))))
```

**Exercise 1.10 [\*]** We typically use “or” to mean “inclusive or.” What other meanings can “or” have?

exclusive or. inclusive or means at least one is true. exclusive or means exactly one is true.

**Exercise 1.11 [\*]** In the last line of `subst-in-s-exp`, the recursion is on `sexp` and not a smaller substructure. Why is the recursion guaranteed to halt?

Actually, we already make progress by excluding the possibility of `sexp` is a symbol, so `sexp` must be a s-list.

**Exercise 1.12 [\*]** Eliminate the one call to `subst-in-s-exp` in `subst` by replacing it by its definition and simplifying the resulting procedure. The result will be a version of `subst` that does not need `subst-in-s-exp`. This technique is called inlining, and is used by optimizing compilers.

```scheme
(define subst
  (lambda (new old slist)
    (if (null? slist)
        '()
        (cons
         (let ((sexp (car slist)))
           (if (symobl? sexp)
               (if (eqv? sexp old) new sexp)
               (subst new old sexp)))
         (subst new old (cdr slist))))))
```



**Exercise 1.13 [\*\*]** In our example, we began by eliminating the Kleene star in the grammar for S-list. Write `subst` following the original grammar by using `map`.

```scheme
(define subst
  (lambda (new old slist)
    (map (lambda (sexp)
           (subst-in-s-exp new old sexp))
         slist)))
```

**Exercise 1.14 [\*\*]** Given the assumption 0 ≤ n < length(v), prove that partialvector-sum is correct.

Mathematical induction.



```scheme
; Exercise 1.15 [*] `(duple n x)` returns a list containing `n` copies of `x`
; > (duple 2 3)
; (3 3)
; > (duple 4 '(ha ha))
; ((ha ha) (ha ha) (ha ha) (ha ha))
; > (duple 0 '(blah))
; ()
; usage: N X SchemeValue -> Listof(Schemevalue)
(define (duple n x)
  (if (= n 0)
      '()
      (cons x (duple (- n 1) x))))

; Exercise 1.16 [*] `(invert lst)`, where `lst` is a list of 2-lists (lists of length two), returns a list with each 2-list reversed.
; > (invert '((a 1) (a 2) (1 b) (2 b)))
; ((1 a) (2 a) (b 1) (b 2))
; > (invert '())
; ()
; usage: Listof(2-lists) -> Listof(2-lists)
(define (invert lst)
  (if (null? lst)
      '()
      (cons (list (cadr (car lst))
                  (car (car lst)))
            (invert (cdr lst)))))

; Exercise 1.17 [*] `(down lst)` wraps parentheses around each top-level element of `lst`.
; > (down '(1 2 3))
; ((1) (2) (3))
; > (down '((a) (fine) (idea)))
; (((a)) ((fine)) ((idea)))
; > (down '(a (more (complicated)) object))
; ((a) ((more (complicated))) (object))
; > (down '())
; ()
; usage: Listof(Any) -> Listof(Any)
(define (down lst)
  (if (null? lst)
      '()
      (cons (list (car lst))
            (down (cdr lst)))))

; Exercise 1.18 [*] `(swapper s1 s2 slist)` returns a list the same as `slist`, but with all occurrences of `s1` replaced by `s2` and all occurrences of `s2` replaced by `s1`.
; > (swapper 'a 'd '(a b c d))
; (d b c a)
; > (swapper 'a 'd '(a d () c d))
; (d a () c a)
; > (swapper 'x 'y '((x) y (z (x))))
; ((y) x (z (y)))
; usage: Symbol x Symbol x S-list -> S-list
(define (swapper s1 s2 slist)
  (cond
   ((null? slist) '())
   ((symbol? (car slist))
    (let ((s (car slist)))
      (cond
       ((eq? s1 s) (cons s2 (swapper s1 s2 (cdr slist))))
       ((eq? s2 s) (cons s1 (swapper s1 s2 (cdr slist))))
       (else (cons s (swapper s1 s2 (cdr slist)))))))
   (else
    (cons (swapper s1 s2 (car slist))
          (swapper s1 s2 (cdr slist))))))

; Exercise 1.19 [**] `(list-set lst n x)` returns a list like `lst`, except that the n-th element, using zero-based indexing, is x.
; > (list-set '(a b c d) 2 '(1 2))
; (a b (1 2) d)
; > (list-ref (list-set '(a b c d) 3 '(1 5 10)) 3)
; (1 5 10)
(define (list-set lst n x)
  (cond
   ((null? lst) (error "list too short"))
   ((= n 0) (cons x (cdr lst)))
   (else (cons (car lst) (list-set (cdr lst) (- n 1) x)))))

; Exercise 1.20 [*] `(count-occurrences s slist)` returns the number of occurrences of `s` in `slist`.
; > (count-occurrences 'x '((f x) y (((x z) x))))
; 3
; > (count-occurrences 'x '((f x) y (((x z) () x))))
; 3
; > (count-occurrences 'w '((f x) y (((x z) x))))
; 0
(define (count-occurrences s slist)
  (define (iter l n)
    (cond
     ((null? l) n)
     ((symbol? (car l))
      (if (eq? s (car l))
          (iter (cdr l) (+ n 1))
          (iter (cdr l) n)))
     (else (iter (cdr l) (iter (car l) n)))))
  (iter slist 0))

; Exercise 1.21 [**] `(product sos1 sos2)`, where `sos1` and `sos2` are each a list of symbols without repetitions, returns a list of 2-lists that represents the Cartesian product of `sos1` and `sos2`. The 2-lists may appear in any order.
; > (product '(a b c) '(x y))
; ((a x) (a y) (b x) (b y) (c x) (c y))
; > (product '(a b) '())
; ()
; > (product '() '(x y))
; ()
; > (product '() '())
; ()
(define (product sos1 sos2)
  (define (product-helper sos1 sos2 res)
    (if (null? sos1)
        res
        (product-helper (cdr sos1)
                        sos2
                        (product-1d (car sos1) sos2 res))))
  (define (product-1d sym sos res)
    (if (null? sos)
        res
        (product-1d sym (cdr sos) (cons (list sym (car sos)) res))))
  (product-helper sos1 sos2 '()))

; Exercise 1.22 [**] `(filter-in pred lst)` returns the list of those elements in `lst` that satisfy the predicate `pred`.
; > (filter-in number? '(a 2 (1 3) b 7))
; (2 7)
; > (filter-in symbol? '(a (b c) 17 foo))
; (a foo)
(define (filter-in pred lst)
  (if (null? lst)
      '()
      (let ((x (car lst)))
        (if (pred x)
            (cons x (filter-in pred (cdr lst)))
            (filter-in pred (cdr lst))))))

; Exercise 1.23 [**] `(list-index pred lst)` returns the 0-based position of the first element of `lst` that satisfies the predicate `pred`. If no element of `lst` satisfies the predicate, then `list-index` returns `#f`.
; > (list-index number? '(a 2 (1 3) b 7))
; 1
; > (list-index symbol? '(a (b c) 17 foo))
; 0
; > (list-index symbol? '(1 2 (a b) 3))
; #f
(define (list-index pred lst)
  (define (iter l i)
    (if (null? l)
        #f
        (let ((a (car l)))
          (if (pred a)
              i
              (iter (cdr l) (+ i 1))))))
  (iter lst 0))

; Exercise 1.24 [**] `(every? pred lst)` returns `#f` if any element of `lst` fails to satisfy `pred`, and returns `#t` otherwise.
; > (every? number? '(a b c 3 e))
; #f
; > (every? number? '(1 2 3 5 4))
; #t
; (every? number? '())
; #t
(define (every? pred lst)
  (cond
   ((null? lst) #t)
   ((not (pred (car lst))) #f)
   (else (every? pred (cdr lst)))))

; Exercise 1.25 [**] `(exists? pred lst)` returns `#t` if any element of `lst` satisfies `pred`, and returns `#f` otherwise.
; > (exists? number? '(a b c 3 e))
; #t
; > (exists? number? '(a b c d e))
; #f
; > (exists? number? '())
; #f
(define (exists? pred lst)
  (cond
   ((null? lst) #f)
   ((pred (car lst)) #t)
   (else (exists? pred (cdr lst)))))

; Exercise 1.26 [**] `(up lst)` removes a pair of parentheses from each top-level element of `lst`. If a top-level element is not a list, it is included in the result, as is. The value of `(up (down lst))` is equivalent to `lst`, but `(down (up lst))` is not necessarily `lst`. (See exercise 1.17.)
; > (up '((1 2) (3 4)))
; (1 2 3 4)
; > (up '((x (y)) z))
; (x (y) z)
(define (up lst)
  (if (null? lst)
      '()
      (let ((a (car lst)))
        (if (pair? a)
            (append a (up (cdr lst)))
            (cons a (up (cdr lst)))))))

; Exercise 1.27 [**] `(flatten slist)` returns a list of the symbols contained in `slist` in the order in which they occur when `slist` is printed. Intuitively, `flatten` removes all the inner parentheses from its argument.
; > (flatten '(a b c))
; (a b c)
; > (flatten '((a) () (b ()) () (c)))
; (a b c)
; > (flatten '((a b) c (((d)) e)))
; (a b c d e)
; > (flatten '(a b (() (c))))
; (a b c)
(define (flatten slist)
  (define (iter slist res)
    (cond
     ((null? slist) res)
     ((symbol? (car slist)) (iter (cdr slist) (cons (car slist) res)))
     (else (iter (cdr slist) (iter (car slist) res)))))
  (reverse (iter slist '())))

; Exercise 1.28 [**] `(merge loi1 loi2)`, where `loi1` and `loi2` are lists of integers that are sorted in ascending order, returns a sorted list of all the integers in `loi1` and `loi2`.
; > (merge '(1 4) '(1 2 8))
; (1 1 2 4 8)
; > (merge '(35 62 81 90 91) '(3 83 85 90))
; (3 35 62 81 83 85 90 90 91)
(define (merge loi1 loi2)
  (cond
   ((null? loi1) loi2)
   ((null? loi2) loi1)
   (else
    (let ((i1 (car loi1))
          (i2 (car loi2)))
      (if (< i1 i2)
          (cons i1 (merge (cdr loi1) loi2))
          (cons i2 (merge loi1 (cdr loi2))))))))

; Exercise 1.29 [**] `(sort loi)` returns a list of the elements of `loi` in ascending order.
; > (sort '(8 2 5 2 3))
; (2 2 3 5 8)
(define (sort loi)
  (if (or (null? loi) (null? (cdr loi)))
      loi
      (let ((res (partition loi)))
        (merge (sort (car res)) (sort (cdr res))))))

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

; Exercise 1.30 [**] `(sort/predicate pred loi)` returns a list of elements sorted by the predicate.
; > (sort/predicate < '(8 2 5 2 3))
; (2 2 3 5 8)
; > (sort/predicate > '(8 2 5 2 3))
; (8 5 3 2 2)
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

(define (sort/predicate pred loi)
  (if (or (null? loi) (null? (cdr loi)))
      loi
      (let ((res (partition loi)))
        (merge-pred pred (sort/predicate pred (car res))
                    (sort/predicate pred (cdr res))))))

; Exercise 1.31 [*] Write the following procedures for calculating on a bintree (definition 1.1.7 `Bintree ::= Int | (Symbol Bintree Bintree)`): `leaf` and `interior-node`, which build bintrees, `leaf?`, which tests whether a bintree is a leaf, and `lson`, `rson`, and `contents-of`, which extract the components of a node. `contents-of` should work on both leaves and interior nodes.
(define (leaf n)
  n)
(define (interior-node s lt rt)
  (list s bt bt))
(define (leaf? x)
  (integer? x))
(define (lson node)
  (cadr node))
(define (rson node)
  (caddr node))
(define (contents-of x)
  (if (leaf? x)
      x
      (car x)))

; Exercise 1.32 [*] Write a procedure `double-tree` that takes a bintree, as represented in definition 1.1.7, and produces another bintree like the original, but with all the integers in the leaves doubled.
(define (double-tree bt)
  (if (leaf? bt)
      (leaf (* 2 (contents-of bt)))
      (interior-node (contents-of bt) (double-tree (lson bt))
                     (double-tree (rson bt)))))

; Exercise 1.33 [**] Write a procedure mark-leaves-with-red-depth that takes a bintree (definition 1.1.7), and produces a bintree of the same shape as the original, except that in the new tree, each leaf contains the integer of nodes between it and the root that contain the symbol red. For example, the expression
;(mark-leaves-with-red-depth
; (interior-node 'red
;   (interior-node 'bar
;     (leaf 26)
;     (leaf 12))
;   (interior-node 'red
;     (leaf 11)
;     (interior-node 'quux
;       (leaf 117)
;       (leaf 14)))))
; which is written using the procedures defined in exercise 1.31, should return the bintree
;(red
;  (bar 1 1)
;  (red 2 (quux 2 2)))
; (mark-leaves-with-red-depth (leaf 6))
; > 0
(define (mark-leaves-with-red-depth bt)
  (define (iter bt n)
    (if (leaf? bt)
        (leaf n)
        (let ((s (contents-of bt)))
          (if (eq? 'red s)
              (interior-node s (iter (lson bt) (+ n 1))
                               (iter (rson bt) (+ n 1)))
              (interior-node s (iter (lson bt) n)
                               (iter (rson bt) n))))))
  (iter bt 0))

; Exercise 1.34 [***] Write a procedure `path` that takes an integer n and a binary search tree bst (page 10) that contains the integer n, and returns a list of lefts and rights showing how to find the node containing n. If n is found at the root, it returns the empty list.
; > (path 17 '(14 (7 () (12 () ()))
; (26 (20 (17 () ())
; ())
; (31 () ()))))
; (right left left)
(define (path n bst)
  (define (iter bst res)
    (cond
     ((null? bst) #f)
     ((eqv? n (car bst)) res)
     (else
      (or (iter (cadr bst) (cons 'left res))
          (iter (caddr bst) (cons 'right res))))))
  (reverse (iter bst '())))

; Exercise 1.35 [***] Write a procedure `number-leaves` that takes a bintree, and produces a bintree like the original, except the contents of the leaves are numbered starting from 0. For example,
(number-leaves
  (interior-node 'foo
    (interior-node 'bar
      (leaf 26)
      (leaf 12))
    (interior-node 'baz
      (leaf 11)
      (interior-node 'quux
        (leaf 117)
        (leaf 14)))))
;(foo
;  (bar 0 1)
;  (baz
;    2
;    (quux 3 4)))
; >(number-leaves (leaf 2))
; 0
(define (number-leaves bt)
  (define (iter bt n)
    (if (leaf? bt)
        (cons (+ n 1) (leaf n))
        (let* ((lres (iter (lson bt) n))
               (rres (iter (rson bt) (car lres))))
          (cons (car rres)
                (interior-node (contents-of bt)
                               (cdr lres)
                               (cdr rres))))))
  (cdr (iter bt 0)))

; Exercise 1.36 [***] Write a procedure `g` such that `number-elements` from page 23 could be defined as
; > (number-elements '(x y z))
; ((0 x) (1 y) (2 z))
; > (number-elements '())
; ()
(define number-elements
  (lambda (lst)
    (if (null? lst) '()
        (g (list 0 (car lst)) (number-elements (cdr lst))))))

(define (g p lop)
  (define (add1 lop)
    (if (null? lop)
        '()
        (let ((p (car lop)))
          (cons (cons (+ 1 (car p)) (cdr p))
                (add1 (cdr lop))))))
  (cons p (add1 lop)))
```



## 2 Data Abstraction

```scheme
; Exercise 2.1 [*] Implement the four required operations for bigits. Then use your implementation to calculate the factorial of 10. How does the execution time vary as this argument changes? How does the execution time vary as the base changes? Explain why.
(define zero (lambda () '()))
(define is-zero? (lambda (n) (null? n)))
(define N 256)
(define successor
  (lambda (n)
    (if (is-zero? n)
        '(1)
        (let ((a (car n))
              (d (cdr n)))
          (if (= a (- N 1))
              (cons 0 (successor d)) 	; carry 1
              (cons (+ a 1) d))))))
(define predecessor
  (lambda (n)
    (let ((a (car n))
          (d (cdr n)))
      (cond
       ((= a 0) (cons (- N 1) (predecessor d)))
       ((and (= a 1) (is-zero? d)) (zero))
       (else (cons (- a 1) d))))))

(define (get-n n)
  (if (= n 0)
      (zero)
      (successor (get-n (- n 1)))))
(define plus
  (lambda (x y)
    (if (is-zero? x)
         y
        (successor (plus (predecessor x) y)))))
(define (multiply x y)
  (cond
   ((is-zero? x) (zero))
   ((is-zero? y) (zero))
   (else (plus y (multiply (predecessor x) y)))))
(define (fact n)
  (if (is-zero? n)
      (successor (zero))
      (multiply n (fact (predecessor n)))))

; fact2 is actually slower, because it multiply from the biggest number
(define (fact2 n)
  (define (iter n res)
    (if (is-zero? n)
        res
        (iter (predecessor n) (multiply n res))))
  (iter n (successor (zero))))

; (fact 10)
; |N| 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10| 16|256|4096|65536|
; | |1.6|1.6|1.5|1.5|1.5|1.5|1.5|1.5|1.4|1.3|1.0|1.0 | 1.0|

; N=2, (fact n)
; |n|6|7| 8|  9|  10| 11|
; | |0|1|20|119|1382|oom|
; less time as the base become larger, but not so much.
; more time as the argument become larger, and rapidly.

; Exercise 2.2 [**] Analyze each of these proposed representations critically. To what extent do they succeed or fail in satisfying the specification of the data type?
; unary representation: no limit in priciple, but the space is limited. actually in my env, it oom when calculating (fact 10)
; scheme number representation: space occupation is efficient, and it's the faster among the 3, but it has limit.
; bignum: between the above 2, slower than 2, but fast and efficient than 1.

; Exercise 2.3 [**] Define a representation of all the integers (negative and nonnegative) as diff-trees, where a diff-tree is a list defined by the grammar
; Diff-tree ::= (one) | (diff Diff-tree Diff-tree)
; The list `(one)` represents 1. If `t1` represents `n1` and `t2` represents `n2`, then `(diff t1 t2)` is a representation of `n1 − n2`.
; So both `(one)` and `(diff (one) (diff (one) (one)))` are representations of 1; `(diff (diff (one) (one)) (one))` is a representation of −1.
; 1. Show that every number has infinitely many representations in this system.
; if x is a representation of number n, then (diff x (diff (one) (one))) is another representation of it.

; 2. Turn this representation of the integers into an implementation by writing `zero`, `is-zero?`, `successor`, and `predecessor`, as specified on page 32, except that now the negative integers are also represented. Your procedures should take as input any of the multiple legal representations of an integer in this scheme. For example, if your `successor` procedure is given any of the infinitely many legal representations of 1, it should produce one of the legal representations of 2. It is permissible for different legal representations of 1 to yield different legal representations of 2.

; 1  (one)
; 0  (diff (one) (one))
; -1 (diff (diff (one) (one)) (one))
; 2 (diff (one) (diff (diff (one) (one)) (one)))
; -2 (diff (diff (diff (one) (one)) (one)) (one))

(define (get-left dif)
  (cadr dif))
(define (get-right dif)
  (caddr dif))
(define (diff x y)
  (list 'diff x y))

(define (zero)
  '(diff (one) (one)))
(define (one)
  '(one))
(define (neg-one)
  (diff (zero) (one)))

(define (is-one? n)
  (and (eq? (car n) 'one)
       (null? (cdr n))))
(define (simple-zero? n)
  (and (not (is-one? n))
       (is-one? (get-left n))
       (is-one? (get-right n))))

; won't complicate n except when n is (one)
(define (negate n)
  (if (is-one? n)
      (diff (zero) '(one))
      (diff (get-right n) (get-left n))))

; for the simplest form, either n is (one), or at least one of x and y in (diff x y) is (one).
(define (reduce n)
  (cond
   ((is-one? n) n)
   ((simple-zero? n) n)
   (else (let ((l (reduce (get-left n)))
               (r (reduce (get-right n))))
           (cond
            ((and (is-one? l) (is-one? r))
             (diff l r))
            ((is-one? l)
             (if (is-one? (get-left r))
                 (get-right r)		; 1 - (1 - x) -> x
                 (diff l r)))
            ((is-one? r)
             (if (is-one? (get-left l))
                 (if (is-one? (get-right l))
                     (diff l r)
                     (reduce (negate (get-right l))))	; (1 - x) - 1 -> -x
                 (diff l r)))
            (else
             (let ((lol (get-left l))
                   (rol (get-right l))
                   (lor (get-left r))
                   (ror (get-right r)))
               (cond
                ((and (is-one? lol) (is-one? lor))
                 (reduce (diff ror rol)))	; (1 - x) - (1 - y) -> (y - x)
                ((and (is-one? rol) (is-one? ror))
                 (reduce (diff lol lor))) 	; (x - 1) - (y - 1) -> (x - y)
                (else
                 (diff l r))))))))))

(define (is-zero? n)
  (simple-zero? (reduce n)))
(define (successor n)
  (if (or (is-one? n)
          (not (is-one? (get-right n))))
      (reduce (diff n (neg-one)))
      (get-left n)))
(define (predecessor n)
  (cond
   ((is-one? n) (zero))
   ((is-one? (get-left n)) (negate (get-right n)))
   (else (reduce (diff n (one))))))
; 3. Write a procedure `diff-tree-plus` that does addition in this representation. Your procedure should be optimized for the diff-tree representation, and should do its work in a constant amount of time (independent of the size of its inputs). In particular, it should not be recursive.
; x + y = x - (0 - y)
; (plus x y) = (diff x (diff 0 y))
(define (diff-tree-plus x y)
  (diff x (diff (zero) y)))
```



**Exercise 2.4 [\*\*]** Consider the data type of stacks of values, with an interface consisting of the procedures empty-stack, push, pop, top, and empty-stack?. Write a specification for these operations in the style of the example above. Which operations are constructors and which are observers?

```
(empty-stack) = [ø]
(push [f] v) = [g], where g[0] = v, g(n+1)=f(n)
(pop [f]) = [g], where g(n)=f(n+1)
(top [f]) = [f(0)]
(empty-stack? [f]), is #t if f = ø, otherwise #f
```



**Exercise 2.5 [\*]** We can use any data structure for representing environments, if we can distinguish empty environments from non-empty ones, and in which one can extract the pieces of a non-empty environment. Implement environments using a representation in which the empty environment is represented as the empty list, and in which extend-env builds an environment that looks like . This is called an a-list or association-list representation.

```scheme
(define (empty-env)
  '())
(define (extend-env env var val)
  (cons (cons var val) env))
(define (apply-env env var)
  (if (null? env)
      (error "undefined variable")
      (let ((p (car env)))
        (if (eq? (car p) var)
            (cdr p)
            (apply-env (cdr env) var)))))
; Exercise 2.8[*]
(define (empty-env? env)
  (null? env))
; Exercise 2.9[*]
(define (has-binding? env var)
  (if (null? env)
      #f
      (let ((p (car env)))
        (if (eq? (car p) var)
            #t
            (apply-env (cdr env) var)))))
; Exercise 2.10[*]
(define (extend-env* env lvar lval))
```



**Exercise 2.13 [\*\*]** Extend the procedural representation to implement `empty-env?` by representing the environment by a list of two procedures: one that returns the value associated with a variable, as before, and one that returns whether or not the environment is empty.

**Exercise 2.14 [\*\*]** Extend the representation of the preceding exercise to include a third procedure that implements has-binding? (see exercise 2.9).

```scheme
;Env = Var → SchemeVal
;empty-env : () → Env
(define empty-env
  (lambda ()
    (list
     (lambda (search-var)
       (report-no-binding-found search-var))
     (lambda () #t)
     (lambda (search-var) #f))))

;extend-env : Var × SchemeVal × Env → Env
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (list
     (lambda (search-var)
      (if (eqv? search-var saved-var)
        saved-val
        (apply-env saved-env search-var)))
     (lambda () #f)
     (lambda (search-var)
       (if (eqv? search-var saved-var)
           #t
           (has-binding? saved-env search-var))))))

;apply-env : Env × Var → SchemeVal
(define apply-env
  (lambda (env search-var)
    ((car env) search-var)))

; empty-env? : Env -> Bool
(define (empty-env? env)
  ((cadr env)))

(define (has-binding? env search-var)
  ((caddr env) search-var))
```

**Exercise 2.15 [\*]** Implement the lambda-calculus expression interface for the representation specified by the grammar above.

```scheme
; constructors
(define (var-exp var)
  var)
(define (lambda-exp bound-var body)
  `(lambda (,bound-var) ,body))
(define (app-exp operator operand)
  `(,operator ,operand))

; predicates
(define var-exp? symbol?)
(define (lambda-exp? exp)
  (and (pair? exp)
       (eqv? (car exp) 'lambda)))
(define (app-exp? exp)
  (and (pair? exp)
       (not (eqv? (car exp) 'lambda))))

; extractors
(define (var-exp->var exp)
  exp)
(define lambda-exp->bound-var caadr)
(define lambda-exp->body caddr)
(define app-exp->rator car)
(define app-exp->rand cadr)
```

**Exercise 2.18 [\*]** We usually represent a sequence of values as a list. In this representation, it is easy to move from one element in a sequence to the next, but it is hard to move from one element to the preceding one without the help of context arguments. Implement non-empty bidirectional sequences of integers, as suggested by the grammar

`NodeInSequence ::= (Int Listof(Int) Listof(Int))`

The first list of numbers is the elements of the sequence preceding the current one, in reverse order, and the second list is the elements of the sequence after the current one. For example, (6 (5 4 3 2 1) (7 8 9)) represents the list (1 2 3 4 5 6 7 8 9), with the focus on the element 6.

In this representation, implement the procedure `number->sequence`, which takes a number and produces a sequence consisting of exactly that number. Also implement `current-element`, `move-to-left`, `move-to-right`, `insert-to-left`, `insert-to-right`, `at-left-end?`, and `at-right-end?`. For example:

```scheme
> (number->sequence 7)
(7 () ())
> (current-element '(6 (5 4 3 2 1) (7 8 9)))
6
> (move-to-left '(6 (5 4 3 2 1) (7 8 9)))
(5 (4 3 2 1) (6 7 8 9))
> (move-to-right '(6 (5 4 3 2 1) (7 8 9)))
(7 (6 5 4 3 2 1) (8 9))
> (insert-to-left 13 '(6 (5 4 3 2 1) (7 8 9)))
(6 (13 5 4 3 2 1) (7 8 9))
> (insert-to-right 13 '(6 (5 4 3 2 1) (7 8 9)))
(6 (5 4 3 2 1) (13 7 8 9))
```

The procedure `move-to-right` should fail if its argument is at the right end of the sequence, and the procedure `move-to-left` should fail if its argument is at the left end of the sequence.

```scheme
(define get-value car)
(define get-prev cadr)
(define get-next caddr)

(define (number->sequence n)
  `(,n () ()))

(define (current-element seq)
  (car seq))

(define (move-to-left seq)
  (let ((v (get-value seq))
        (p (get-prev seq))
        (n (get-next seq)))
    (if (null? p)
        (error "already the leftmost element!")
        (list (car p) (cdr p) (cons v n)))))

(define (move-to-right seq)
  (let ((v (get-value seq))
        (p (get-prev seq))
        (n (get-next seq)))
    (if (null? n)
        (error "already the rightmost element!")
        (list (car n) (cons v p) (cdr n)))))

(define (insert-to-left nv seq)
  (let ((v (get-value seq))
        (p (get-prev seq))
        (n (get-next seq)))
    (list v (cons nv p) n)))

(define (insert-to-right nv seq)
  (let ((v (get-value seq))
        (p (get-prev seq))
        (n (get-next seq)))
    (list v p (cons nv n))))

(define (at-left-end? seq)
  (null? (get-prev seq)))

(define (at-right-end? seq)
  (null? (get-next seq)))
```



**Exercise 2.19 [\*]** A binary tree with empty leaves and with interior nodes labeled with integers could be represented using the grammar
`Bintree ::= () | (Int Bintree Bintree)`
In this representation, implement the procedure `number->bintree`, which takes a number and produces a binary tree consisting of a single node containing that number. Also implement `current-element`, `move-to-left-son`, `move-to-rightson`, `at-leaf?`, `insert-to-left`, and `insert-to-right`. For example,

```scheme
;> (number->bintree 13)
;(13 () ())
;> (define t1 (insert-to-right 14
;(insert-to-left 12
;(number->bintree 13)))
;> t1
;(13
;(12 () ())
;(14 () ()))
;> (move-to-left t1)
;(12 () ())
;> (current-element (move-to-left t1))
;12
;> (at-leaf? (move-to-right (move-to-left t1)))
;#t
;> (insert-to-left 15 t1)
;(13
;(15
;(12 () ())
;())
;(14 () ()))

(define bt-value car)
(define bt-lson cadr)
(define bt-rson caddr)
    
(define (number->bintree n)
  `(,n () ()))

(define (current-element bt)
  (if (at-leaf? bt)
      (error "already the empty leaf!")
      (bt-value bt)))

(define (move-to-left-son bt)
  (if (at-leaf? bt)
      (error "already the empty leaf!")
      (bt-lson bt)))

(define (move-to-right-son bt)
  (if (at-leaf? bt)
      (error "already the empty leaf!")
      (bt-rson bt)))

(define at-leaf? null?)

(define (insert-to-left nv bt)
  (let ((v (bt-value bt))
        (l (bt-lson bt))
        (r (bt-rson bt)))
    (list v (list nv l '()) r)))

(define (insert-to-left nv bt)
  (let ((v (bt-value bt))
        (l (bt-lson bt))
        (r (bt-rson bt)))
    (list v l (list nv '() r))))
```



**Exercise 2.20 [\*\*\*]** In the representation of binary trees in exercise 2.19 it is easy to move from a parent node to one of its sons, but it is impossible to move from a son to its parent without the help of context arguments. Extend the representation of lists in exercise 2.18 to represent nodes in a binary tree. As a hint, consider representing the portion of the tree above the current node by a reversed list, as in exercise 2.18. In this representation, implement the procedures from exercise 2.19. Also implement `move-up`, `at-root?`, and `at-leaf?`.

```scheme
; if we don't have set-car!
; then use context to save the ancients
; Bintree ::= (Parent) | (Parent Int Bintree Bintree))
; Leaves also have parent
(define bt-parent car)
(define bt-main cdr)
(define bt-value cadr)
(define bt-lson caddr)
(define bt-rson cadddr)

; set the parent of lson
(define (set-polson bt)
  (set-car! (caddr bt) bt))

(define (set-porson bt)
  (set-car! (cadddr bt) bt))

(define (number->bintree n)
  (let ((node `(() ,n (*undefined*) (*undefined*))))
    (set-polson node)
    (set-porson node)
    node))

(define (current-element bt)
  (if (at-leaf? bt)
      (error "already the empty leaf!")
      (bt-value bt)))

(define (move-to-left-son bt)
  (if (at-leaf? bt)
      (error "already the empty leaf!")
      (bt-lson bt)))

(define (move-to-right-son bt)
  (if (at-leaf? bt)
      (error "already the empty leaf!")
      (bt-rson bt)))

(define (move-up bt)
  (if (at-root? bt)
      (error "already the root!")
      (bt-parent bt)))

(define (at-leaf? bt)
  (null? (bt-main bt)))

(define (at-root? bt)
  (null? (bt-parent bt)))

(define (insert-to-left nv bt)
  (let ((p (bt-parent bt))
        (v (bt-value bt))
        (l (bt-lson bt))
        (r (bt-rson bt)))
    (let ((node `(,bt ,nv (*undefined* ,(bt-main l)) (*undefined*))))
      (set-polson node)
      (set-porson node)
      `(p v node r))))

(define (insert-to-right nv bt)
  (let ((p (bt-parent bt))
        (v (bt-value bt))
        (l (bt-lson bt))
        (r (bt-rson bt)))
    (let ((node `(,bt ,nv (*undefined*) (*undefined* ,(bt-main r)) )))
      (set-polson node)
      (set-porson node)
      `(p v l node))))

; test
> (insert-to-left 4 (insert-to-right 5 (number->bintree 3)))
(() 3 #0=((() 3 #1=(#2=(() 3 #1# (#2#))) #3=(#2# 5 (#3#) (#3#))) 4 (#0#) (#0#)) #3#)
> (define a (insert-to-left 4 (insert-to-right 5 (number->bintree 3))))
> (current-element a)
3
> (move-to-left-son a)
#0=((() 3 #1=(#2=(() 3 #1# (#2#))) #3=(#2# 5 (#3#) (#3#))) 4 (#0#) (#0#))
> (current-element (move-to-left-son a))
4
> (current-element (move-to-right-son a))
5
> (move-up a)
. . already the root!
> (move-to-left-son (move-to-left-son a))
#0=(#1=((() 3 #2=(#3=(() 3 #2# (#3#))) #4=(#3# 5 (#4#) (#4#))) 4 #0# (#1#)))
> (at-leaf? (move-to-left-son (move-to-left-son a)))
#t
> (at-root? a)
#t
> (at-root? (move-up (move-to-left-son a)))
#t
```



**Exercise 2.21 [\*]** Implement the data type of environments, as in section 2.2.2, using `define-datatype`. Then include `has-binding?` of exercise 2.9.

```scheme
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error ’apply-env "No binding for ~s" search-var)))
(define report-invalid-env
  (lambda (env)
    (eopl:error ’apply-env "Bad environment: ~s" env)))

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
```



**Exercise 2.22 [\*]** Using `define-datatype`, implement the stack data type of exercise 2.4.

```scheme
(define (any? v) #t)

(define-datatype stack-type stack?
  (empty-stack)
  (push (saved-stack stack?)
        (val any?)))

(define (pop stack)
  (cases stack-type stack
    (empty-stack () (eopl:error 'pop "Can not pop an empty stack."))
    (push (saved-stack val) saved-stack)))

(define (top stack)
  (cases stack-type stack
    (empty-stack () (eopl:error 'pop "Can not top an empty stack."))
    (push (saved-stack val) val)))

(define (empty-stack? stack)
  (cases stack-type stack
    (empty-stack () #t)
    (push (saved-stack val) #f)))
```

**Exercise 2.25 [\*\*]** Use cases to write max-interior, which takes a binary tree of integers (as in the preceding exercise) with at least one interior node and returns the symbol associated with an interior node with a maximal leaf sum.

先深度优先遍历树，求每个interior节点的叶子的和，然后再遍历一次获取最大值节点。

**Exercise 2.26 [\*\*]** Here is another version of exercise 1.33. Consider a set of trees given by the following grammar:
Red-blue-tree       ::= Red-blue-subtree
Red-blue-subtree ::= (red-node Red-blue-subtree Red-blue-subtree)
                                ::= (blue-node {Red-blue-subtree}∗)
                                ::= (leaf-node Int)
Write an equivalent definition using `define-datatype`, and use the resulting interface to write a procedure that takes a tree and builds a tree of the same shape, except that each leaf node is replaced by a leaf node that contains the number of red nodes on the path between it and the root.

```scheme
(define-datatype rbtree rbtree?
                 (leaf-node (num integer?))
                 (red-node (lson rbtree?) (rson rbtree?))
                 (blue-node (sons (list-of rbtree?))))

(define (rbtree-red-depth tree)
  (define (iter tree dep)
    (cases rbtree tree
           (leaf-node (_) (leaf-node dep))
           (red-node (lson rson) (red-node (iter lson (+ dep 1))
                                           (iter rson (+ dep 1))))
           (blue-node (sons) (blue-node (map (lambda (son)
                                               (iter son dep))
                                             sons))))))
```

**Exercise 2.29 [\*]** Where a Kleene star or plus (page 7) is used in concrete syntax, it is most convenient to use a list of associated subtrees when constructing an abstract syntax tree. For example, if the grammar for lambda-calculus expressions had been

```
Lc-exp ::= Identifier
           var-exp (var)
       ::= (lambda ({Identifier}∗) Lc-exp)
           lambda-exp (bound-vars body)
       ::= (Lc-exp {Lc-exp}∗)
            app-exp (rator rands)
```

then the predicate for the `bound-vars` field could be `(list-of identifier?)`, and the predicate for the `rands` field could be `(list-of lc-exp?)`. Write a `define-datatype` and a parser for this grammar that works in this way.

```scheme
(define-datatype lc-exp lc-exp?
                 (var-exp (var identifier?))
                 (lambda-exp (bound-vars (list-of identifier?))
                             (body lc-exp?))
                 (app-exp (rator lc-exp?)
                          (rands (list-of lc-exp?))))

;parse-expression : SchemeVal → LcExp
(define parse-expression
  (lambda (datum)
    (cond
      ((identifier? datum) (var-exp datum))
      ((pair? datum)
       (if (eqv? (car datum) 'lambda)
           (lambda-exp
            (cadr datum)
            (parse-expression (caddr datum)))
           (app-exp
            (parse-expression (car datum))
            (map parse-expression (cdr datum)))))
      (else (report-invalid-concrete-syntax datum)))))
```

