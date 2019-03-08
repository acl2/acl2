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

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "../lib2.delta1/rtl") ;semantics of the basic RTL primitives

(include-book "../lib2/basic") ;properties of basic arithmetic functions: floor, ceiling,
;                       exponential, and remainder;;  Wed Feb  4 16:40:37 2009

;(include-book "../lib1/bits") ;bit vectors
(include-book "../lib2.delta2/bits") ;bit vectors ;; Tue Feb 24 09:33:20 2009


(include-book "../lib2.delta2/log") ;logical operations ;; Tue Feb 24 09:33:47 2009

(include-book "../lib2.delta1/float") ;floating-point numbers

(include-book "../lib2.delta1/round") ;floating-point rounding

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../arithmetic/top")

(include-book "../lib2.delta1/arith") ;general arithmetic package

;
; let go Thu Feb 19 09:43:32 2009

(include-book "../lib2.delta1/util") ;misc helpful stuff including a few macros


(include-book "../lib2.delta1/bvecp-raw-helpers")
;; ; better bvecp-raw-helpers.lisp, Fri Jun 29 10:13:32 2007

(include-book "../lib2.delta1/bvecp-helpers")

(include-book "../lib2.delta1/logn")


(include-book "../lib2.delta1/simplify-model-helpers")


(include-book "../lib2.delta1/logn2log")
