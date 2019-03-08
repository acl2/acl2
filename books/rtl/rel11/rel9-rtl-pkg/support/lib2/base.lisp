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

(include-book "../lib1/rtl") ;semantics of the basic RTL primitives

(include-book "../lib1.delta1/basic") ;properties of basic arithmetic functions: floor, ceiling,
;                       exponential, and remainder;;  Mon Mar  5 13:46:31 2007

;(include-book "../lib1/bits") ;bit vectors
(include-book "../lib1.delta1/bits") ;bit vectors ;; Fri Aug  3 12:38:57 2007
; added back the definition of bitvec

(include-book "../lib1/log") ;logical operations

(include-book "../lib1.delta2/float") ;floating-point numbers

(include-book "../lib1.delta1/round") ;floating-point rounding

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../arithmetic/top")

;(include-book "../lib1/arith") ;general arithmetic package

(include-book "../lib1.delta1/arith") ;general arithmetic package;; Mon Mar  5 13:46:39 2007

(include-book "../lib1/util") ;misc helpful stuff including a few macros


(include-book "../lib1.delta1/bvecp-raw-helpers")
; better bvecp-raw-helpers.lisp, Fri Jun 29 10:13:32 2007
