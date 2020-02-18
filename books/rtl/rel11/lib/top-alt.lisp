; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "../../../misc/rtl-untranslate")
; to inhibit expansion of macros in proof output.

(include-book "doc")

;; These books are useful for most floating-point applications:

(include-book "basic") ;basic arithmetic functions: floor, ceiling, and mod

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "reps") ;floating-point formats and representations

(include-book "round") ;floating-point rounding

;; Special-purpose theories:

(include-book "sqrt") ;approximation to square root

(include-book "add") ;support for reasoning about addition

(include-book "mult") ;integer multiplication

(include-book "srt") ;SRT division and square root

(include-book "div") ;Newton-Raphson division

(include-book "excps") ;specifications of elementary arithmetic operastions (SSE, x87, Arm)

;; Miscellaneous helpful stuff including a few macros;

(include-book "util")

;; This is relevant to code derived from C++:

(include-book "rac")

;; This must be included to use GL with this library:

(include-book "gl")

;; We can't do much without some arithmetic book.  Currently, the best choice
;; is probably this:

;;(include-book "arithmetic-5/top" :dir :system)

;; Unfortunately, there are some conflicts between arithmetic-5 and this library
;; (especially the "basic" book) that can severely slow down some proofs.  Much of
;; this can be avoided by disabling the following lemmas:

;; (in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)|
;;                           |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)| mod-cancel-*-const
;; 			  cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)|
;; 			  |(equal x (if a b c))| |(equal (if a b c) x)| |(logior 1 x)|
;; 			  mod-theorem-one-b |(mod (- x) y)|))




