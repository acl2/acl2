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

(in-package "RTL")

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "../../../misc/rtl-untranslate")
; to inhibit expansion of macros in proof output.

;; The books included here are useful for most floating-point applications:

(include-book "basic") ;basic arithmetic functions: floor, ceiling, and remainder

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "round") ;floating-point rounding

(include-book "util") ;misc helpful stuff including a few macros

;; These are relevant to code derived from Verilog:

;;(include-book "rtl") ;semantics of the basic RTL primitives
