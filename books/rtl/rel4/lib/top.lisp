(in-package "ACL2")

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "misc/rtl-untranslate" :dir :system)
; to inhibit expansion of macros in proof output.

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "rtl") ;semantics of the basic RTL primitives

(include-book "rtlarr") ;semantics RTL array primitives

(include-book "basic") ;properties of basic arithmetic functions: floor, ceiling,
;                       exponential, and remainder

(include-book "bits") ;bit vectors and logical operations

(include-book "float") ;floating-point numbers

(include-book "reps") ;floating-point formats and representations

(include-book "round") ;floating-point rounding

(include-book "fadd") ;support for reasoning about floating-point addition
;                      (leading one prediction and sticky bit computation)

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../arithmetic/top")
(include-book "arith") ;general arithmetic package

(include-book "util") ;misc helpful stuff including a few macros
