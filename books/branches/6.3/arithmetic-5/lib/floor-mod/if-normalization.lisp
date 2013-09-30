; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; if-normalization.lisp
;;;
;;; We have found it useful to normalize if expressions involving
;;; arithmetic operators.
;;;
;;; See the comments in ../basic-ops/if-normalization.lisp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../basic-ops/building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(floor (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (floor (if a b c) x)
		  (if a (floor b x) (floor c x)))))

(defthm |(floor y (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (floor y (if a b c))
		  (if a (floor y b) (floor y c)))))

(defthm |(mod (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (mod (if a b c) x)
		  (if a (mod b x) (mod c x)))))

(defthm |(mod y (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (mod y (if a b c))
		  (if a (mod y b) (mod y c)))))

(defthm |(logand (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (logand (if a b c) x)
		  (if a (logand b x) (logand c x)))))

(defthm |(logand y (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (logand y (if a b c))
		  (if a (logand y b) (logand y c)))))

(defthm |(lognot (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (lognot (if a b c))
		  (if a (lognot b) (lognot c)))))
