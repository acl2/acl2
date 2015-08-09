; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; distributivity.lisp
;;;
;;; We load this book first in top.lisp, so that the distributivity
;;; rules are considered last by ACL2.  For a simple example of why
;;; this might be desireable, consider:
;;; (equal (* x (/ (+ 1 y)))
;;;        z)
;;; and prefer-positive-exponents-scatter-exponents-equal.  We attempt
;;; to ``undo'' the division by multiplying both sides by (+ 1 y),
;;; resulting in
;;; (equal (* (+ 1 y) x (/ (+ 1 y)))
;;;        (* (+ 1 y) z))
;;; in the hopes that the (+ 1 y) and the (/ (+ 1 y)) will cancel.
;;; But, this would not occur if we distributed the (+ 1 y) over
;;; (* x (/ (+ 1 y))) before normalize-factors-scatter-exponents
;;; had a chance to fire.
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Two distributivity rules.  Note that we disable the ``built-in''
;;; rule Distributivity in top.lisp.

(defthm |(* (+ x y) z)|
  (equal (* (+ x y) z)
	 (+ (* x z) (* y z))))

(defthm |(* x (+ y z))|
  (equal (* x (+ y z))
         (+ (* x y) (* x z))))
