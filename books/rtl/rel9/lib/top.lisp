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

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "../../../misc/rtl-untranslate")
; to inhibit expansion of macros in proof output.

;; The books included here are useful for most floating-point applications:

(include-book "basic") ;basic arithmetic functions: floor, ceiling, and remainder

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "reps") ;floating-point formats and representations

(include-book "round") ;floating-point rounding

(include-book "util") ;misc helpful stuff including a few macros

;; Special-purpose theories:

;;(include-book "add") ;support for reasoning about addition

;;(include-book "mult") ;integer multiplication

;;(include-book "sqrt") ;approximation to square root

;;(include-book "srt") ;SRT division and square root

;; This must be included to use GL with this library:

;;(include-book "gl")

;; These are relevant to code derived from Verilog:

;;(include-book "rtl") ;semantics of the basic RTL primitives

;;(include-book "rtlarr") ;semantics of RTL array primitives

;; This is relevant to code derived from SystemC and is inconsistent with the last two above:

;;(include-book "masc")




