#lang eopl
; CALL-BY-RERERENCE (based on 4.33 version)

;Exercise 4.36 [*] If an operand is an array reference, then the location referred to, rather than its contents,
;is passed to the called procedure. This allows, for example, a swap procedure to be used in commonly
;occurring situations in which the values in two array elements are to be exchanged.

; We didn't do this exercise, because we implement array as primitives, it's hard to achieve this.
;`arrayref` either to return the content or to return the location. It's difficult to support both.