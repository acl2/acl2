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
; (include-book "misc/rtl-untranslate" :dir :system)
; to inhibit expansion of macros in proof output.

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "rtl") ;semantics of the basic RTL primitives

(include-book "basic") ;properties of basic arithmetic functions: floor, ceiling,
;                       exponential, and remainder

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "reps") ;floating-point formats and representations

(include-book "round") ;floating-point rounding

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../../arithmetic/top")
(include-book "arith") ;general arithmetic package

(include-book "util") ;misc helpful stuff including a few macros
