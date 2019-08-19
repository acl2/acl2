; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; top.lisp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "logand")

(include-book "truncate-rem")

;; Commented out to avoid name clashes:
;; (include-book "mod-expt-fast")

(include-book "more-floor-mod")

(include-book "floor-mod")

(include-book "floor-mod-basic")

;;; We want these to be the first rules seen:

(include-book "if-normalization")

(include-book "forcing-types")
