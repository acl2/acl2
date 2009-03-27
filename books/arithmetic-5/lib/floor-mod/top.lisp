;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; top.lisp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "logand")

(include-book "truncate-rem")

(include-book "mod-expt-fast")

(include-book "more-floor-mod")

(include-book "floor-mod")

(include-book "floor-mod-basic")

;;; We want these to be the first rules seen:

(include-book "if-normalization")

(include-book "forcing-types")
