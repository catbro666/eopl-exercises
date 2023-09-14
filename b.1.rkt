#lang eopl
; Exercise B.1 [*] Scanner & Parser
; Arith-expr        ::= Arith-term {Additive-op Arith-term}∗
; Arith-term        ::= Arith-factor {Multiplicative-op Arith-factor}∗
; Arith-factor      ::= Number
;                   ::= ( Arith-expr )
; Additive-op       ::= + | -
; Multiplicative-op ::= * | /

(define scanner-spec-1
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (additive-op ((or "+" "-")) symbol)
    (multiplicative-op ((or "*" "/")) symbol)))

(define grammar-1
  '((arith-expr
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
     expr-factor)))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)
(define list-the-datatypes
  (lambda ()
    (sllgen:list-define-datatypes scanner-spec-1 grammar-1)))
(define just-scan
  (sllgen:make-string-scanner scanner-spec-1 grammar-1))
(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))

; test
(scan&parse "1+1")
; #(struct:expr #(struct:term #(struct:num-factor 1) () ()) (+) (#(struct:term #(struct:num-factor 1) () ())))
(scan&parse "3+2*66-5")
;#(struct:expr
;  #(struct:term #(struct:num-factor 3) () ())
;  (+ -)
;  (#(struct:term #(struct:num-factor 2) (*) (#(struct:num-factor 66)))
;   #(struct:term #(struct:num-factor 5) () ())))
