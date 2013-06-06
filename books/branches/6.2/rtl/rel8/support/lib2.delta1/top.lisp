(in-package "ACL2")

(set-enforce-redundancy t)

; Optionally, one may wish to consider:
; (include-book "../../../misc/rtl-untranslate")
; to inhibit expansion of macros in proof output.

; We deliberately exclude any *-helpers.lisp books that may appear here.

(include-book "rtl") ;semantics of the basic RTL primitives

(include-book "rtlarr") ;semantics RTL array primitives

(include-book "bits") ;bit vectors

(include-book "log") ;logical operations

(include-book "float") ;floating-point numbers

(include-book "reps") ;floating-point formats and representations

(include-book "round") ;floating-point rounding

(include-book "add") ;support for reasoning about floating-point addition
;                      (leading one prediction and sticky bit computation)

; Users may prefer to replace the (include-book "arith") below with:
; (include-book "../arithmetic/top")

(include-book "mult")  ; integerp multiplier

;; (include-book "arith") ;general arithmetic package

(include-book "bvecp-raw-helpers") 


(include-book "simple-loop-helpers") 


(include-book "arith")

(include-book "bvecp-helpers")

(include-book "logn")


(include-book "simplify-model-helpers")


