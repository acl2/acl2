(in-package "ACL2")

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "misc/rtl-untranslate" :dir :system)
; to inhibit expansion of macros in proof output.

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "../lib1/rtl") ;semantics of the basic RTL primitives

(include-book "../lib1/rtlarr") ;semantics RTL array primitives

(include-book "../lib1.delta1/basic") ;properties of basic arithmetic functions: floor, ceiling, 
;                       exponential, and remainder;;  Mon Mar  5 13:46:31 2007

(include-book "../lib1/bits") ;bit vectors

(include-book "../lib1/log") ;logical operations

(include-book "../lib1.delta1/float") ;floating-point numbers

(include-book "../lib1/reps") ;floating-point formats and representations

(include-book "../lib1.delta1/round") ;floating-point rounding

(include-book "../lib1/add") ;support for reasoning about floating-point addition
;                      (leading one prediction and sticky bit computation)

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../arithmetic/top")

(include-book "../lib1.delta1/mult")  ; integerp multiplier

;(include-book "../lib1/arith") ;general arithmetic package

(include-book "../lib1.delta1/arith") ;general arithmetic package;; Mon Mar  5 13:46:39 2007

(include-book "../lib1/util") ;misc helpful stuff including a few macros
