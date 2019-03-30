; Integer Arithmetic
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "operations")

(include-book "rules")

(include-book "meta-rules")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This library defines integer arithmetic,
; i.e. integer fixed versions of the operations +, *, and -.
; Specifically, we define
;
;   (binary-i+ x y) = (binary-+ (ifix x) (ifix y))
;   (binary-i* x y) = (binary-* (ifix x) (ifix y))
;   (unary-i- x) = (unary-- (ifix x))

; The motivation for such operations is
; to define congruence rules strictly on the integer domain.
; Consider the following example for modular arithmetic.
; First define an equivalence relation
;
;   (=p x y) := (equal (mod x p) (mod y p))
;
; where p is a fixed positive integer constant or constrained 0-ary function
; (this definition avoids the need to define n-ary equivalence relation;
; see [books]/coi/nary/).

; Ideally we would like to show the following congruences
;
;   (defcong =p =p (+ x y) 1)
;   (defcong =p =p (+ x y) 2)
;   ...
;
; and similarly for * and -.

; In order for these to hold,
; they would need to hold for arbitrary acl2-numberp inputs,
; but this is not the case.
; Instead, what we would like are conditional congruence rules like
;
; (implies (and (integerp x)
;               (integerp x-equiv)
;               (integerp y))
;          (implies (=p x x-equiv)
;                   (=p (+ x y) (+ x-equiv y))))
;
; But ACL2 does not accept this as a congruence rule.

; To remedy this, we instead do arithmetic over i+, i*, and i-,
; with the following congruence rules:
;
;   (defcong =p =p (i+ x y) 1)
;   (defcong =p =p (i+ x y) 2)
;   ...
;
; and similarly for i* and i-.

; Unfortunately there is a certain degree of redundancy in these definitions,
; since we would also like all the usual arithmetic libraries to work.
; So this library replicates some rules and meta rules for integers.
