; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; types.lisp
;;;
;;; The neccesity for these theorems does not arise very often,
;;; but it can be very irritating when they do.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "types-helper"))

(local
 (defthm equal-to-iff-1
   (equal (equal (rationalp x) (rationalp y))
	  (iff (rationalp x) (rationalp y)))))

(local
 (defthm equal-to-iff-1-real-case
   (equal (equal (real/rationalp x) (real/rationalp y))
	  (iff (real/rationalp x) (real/rationalp y)))))

(local
 (defthm equal-to-iff-2
   (equal (equal (integerp x) (integerp y))
	  (iff (integerp x) (integerp y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next two are subsumed by meta-integerp-correct or
;;; meta-rationalp-correct.

;;;(defthm rationalp-+
;;;  (implies (and (rationalp x)
;;;		   (rationalp y))
;;;	      (rationalp (+ x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

;;;(defthm integerp-+
;;;  (implies (and (integerp x)
;;;		   (integerp y))
;;;	      (integerp (+ x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm |(rationalp (- x))|
  (implies (acl2-numberp x)
	   (equal (rationalp (- x))
		  (rationalp x))))

#+non-standard-analysis
(defthm |(real/rationalp (- x))|
  (implies (acl2-numberp x)
	   (equal (real/rationalp (- x))
		  (real/rationalp x))))

(defthm |(integerp (- x))|
  (implies (acl2-numberp x)
	   (equal (integerp (- x))
		  (integerp x))))

;;; These next two are subsumed by meta-integerp-correct or
;;; meta-rationalp-correct.

;;;(defthm rationalp-*
;;;  (implies (and (rationalp x)
;;;		(rationalp y))
;;;	   (rationalp (* x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

;;;(defthm integerp-*
;;;  (implies (and (integerp x)
;;;		   (integerp y))
;;;	      (integerp (* x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm rationalp-/
  (implies (acl2-numberp x)
	   (equal (rationalp (/ x))
		  (rationalp x))))

#+non-standard-analysis
(defthm real/rationalp-/
  (implies (acl2-numberp x)
	   (equal (real/rationalp (/ x))
		  (real/rationalp x))))

(defthm not-integerp-/-1
  (implies (< 1 x)
	   (not (integerp (/ x)))))

(defthm not-integerp-/-2
  (implies (< x -1)
	   (not (integerp (/ x)))))

;;; We do not introduce the case-split unless we are rewriting a goal
;;; literal.

(defthm integerp-/
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(integerp x))
	   (equal (integerp (/ x))
		  (or (equal x -1)
		      (equal x 0)
		      (equal x 1)))))

(defthm rationalp-x
  (implies (integerp x)
	   (rationalp x))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

#+non-standard-analysis
(defthm real/rationalp-x
  (implies (integerp x)
	   (real/rationalp x))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(defthm acl2-numberp-x
  (implies (rationalp x)
	   (acl2-numberp x))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

#+non-standard-analysis
(defthm acl2-number-if-real/rationalp-x
  (implies (real/rationalp x)
	   (acl2-numberp x))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))