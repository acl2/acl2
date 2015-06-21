; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; numerator-and-denominator.lisp
;;;
;;;
;;; Some simple facts about numerator and denominator.
;;;
;;; This book should be expanded some day.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Type-set already knows that (numerator x) and (denominator x)
;;; are integers, and that 0 < (denominator x).

(defthm Rational-implies2               ; Redundant, from axioms.lisp
  (implies (rationalp x)
           (equal (* (/ (denominator x)) (numerator x)) x)))

(local (in-theory (enable rewrite-linear-equalities-to-iff)))

(defthm numerator-positive
  (implies (rationalp x)
	   (equal (< 0 (numerator x))
		  (< 0 x)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(< 0 x))
			   (< 0 (numerator x))))
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(<= 0 x))
			   (<= 0 (numerator x))))))

(defthm numerator-negative
  (implies (rationalp x)
	   (equal (< (numerator x) 0)
		  (< x 0)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(< x 0))
			   (< (numerator x) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(<= x 0))
			   (<= (numerator x) 0)))))

(defthm numerator-minus
   (equal (numerator (- i))
          (- (numerator i))))

(defthm denominator-minus
  (implies (rationalp x)
           (equal (denominator (- x))
                  (denominator x))))

(defthm integerp==>numerator-=-x
  (implies (integerp x)
	   (equal (numerator x)
		  x)))

(defthm integerp==>denominator-=-1
  (implies (integerp x)
           (equal (denominator x)
		  1)))

(defthm equal-denominator-1
  (equal (equal (denominator x) 1)
         (or (integerp x)
             (not (rationalp x)))))

(defthm *-r-denominator-r
  (equal (* r (denominator r))
         (if (rationalp r)
             (numerator r)
           (fix r))))
