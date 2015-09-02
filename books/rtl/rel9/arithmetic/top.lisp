; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

;An attempt to include all the books in arithmetic/ (to check for name conflicts and so forth).

;Keep this list up-to-date:

(include-book "ground-zero") ;disables some of the built-in functions which should be disabled when ACL2 starts

(include-book "induct") ;Induction schemes

(include-book "denominator")
(include-book "numerator")
(include-book "nniq") ;lemmas about nonnegative-integer-quotient

(include-book "complex-rationalp")
(include-book "rationalp")
(include-book "integerp")

;BOZO What's the difference between these 4?
(include-book "arith")
(include-book "arith2")
(include-book "fp2")
(include-book "basic") ;this is Doc's book.  mixed lemmas about fl, mod, expt, and squaring

(include-book "unary-divide")
(include-book "product") ;mostly stuff about comparing a product to zero.

(include-book "inverted-factor")

(include-book "negative-syntaxp") ;handy recognizer for terms with look negative, needed by some of the other books.

(include-book "predicate") ;splits an equality of two "predicates" into two implications
(include-book "x-2xx") ;A very special-purpose lemma having to do with 2x^2

(include-book "power2p") ;recognizer for powers of 2
(include-book "expt")
(include-book "expo") ;sort of my top-level book dealing with powers of 2.

;I commented out these two because we don't need them in support/.
;(include-book "hacks")			 ;BOZO Figure out exactly what this is.
(include-book "fl-hacks") ; needed for fl-m-n, at the least

(include-book "even-odd2") ;recursive analogues of evenp and oddp
(include-book "even-odd") ;lemmas 1/2 and even and odd numbers


;;(include-book "floor-proofs")
(include-book "floor")
(include-book "fl")
(include-book "cg")
(include-book "mod")

(include-book "fl-expt") ;lemmas mixing fl and expt
(include-book "mod-expt") ;lemmas mixing mod and expt

(include-book "common-factor") ;

