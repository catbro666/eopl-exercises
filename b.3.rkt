#lang epol
; Exercise B.2 [**] Interpreter
; We use `;` to denote the termination of program, see ***

(define scanner-spec-1
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (var (letter (arbno letter)) symbol)
    (number (digit (arbno digit)) number)
    (additive-op ((or "+" "-")) symbol)
    (multiplicative-op ((or "*" "/")) symbol)))

(define grammar-1
  '((arith-program
     (arith-expr ";")  ; ***
     program)
    (arith-expr
     (arith-term (arbno additive-op arith-term))
     expr)
    (arith-term
     (arith-factor (arbno multiplicative-op arith-factor))
     term)
    (arith-factor
     (number)
     num-factor)
    (arith-factor
     ("(" arith-expr ")")
     expr-factor)
    (arith-factor
     (var))))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-1 grammar-1)))
(define just-scan
  (sllgen:make-string-scanner scanner-spec-1 grammar-1))
(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))

(define (value-of-program a-program)
  (cases arith-program a-program
         (program (expr)
               (value-of-expr expr))))

(define (value-of-expr a-expr)
  (cases arith-expr a-expr
         (expr (term ops terms)
               (value-of-comb value-of-term term ops terms))))

(define (value-of-term a-term)
  (cases arith-term a-term
         (term (factor ops factors)
               (value-of-comb value-of-factor factor ops factors))))

(define (value-of-factor a-factor)
  (cases arith-factor a-factor
         (num-factor (num) num)
         (expr-factor (expr) (value-of-expr expr))))

(define (value-of-comb value-of term ops terms)
  (fold/l (lambda (op term res)
            ((symbol->proc op) res (value-of term)))
          (value-of term) ops terms))

(define (symbol->proc s)
  (case s
   ((+) +)
   ((-) -)
   ((*) *)
   ((/) /)))

(define (fold/l op init lst1 lst2)
  (if (null? lst1)
      init
      (fold/l op (op (car lst1) (car lst2) init) (cdr lst1) (cdr lst2))))

(define (fold/r op init lst1 lst2)
  (if (null? lst1)
      init
      (op (fold/r op init (cdr lst1) (cdr lst2)) (car lst1) (car lst2))))

(define repl
  (sllgen:make-rep-loop "--> " value-of-program
     (sllgen:make-stream-parser scanner-spec-1 grammar-1)))
