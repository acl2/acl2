; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; numerator-and-denominator.lisp
;;;
;;; Some simple facts about numerator and denominator.
;;;
;;; Some of the theorems in this book could be generalized, perhaps by
;;; using bind-free.  Other useful theorems could probably be added.
;;; However, I choose to leave this book as it is.  This book is
;;; sufficient for what I need, and I do not have enough experience to
;;; know what else might be needed.
;;;
;;; If you are reasoning about numerator or denominator, you are
;;; probably going about it the wrong way.  If you truly need to
;;; reason about numerator and denominator and discover some useful
;;; theorems to add, please send them to the ACL2 maintainers.  They
;;; could be added to this book.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../../support/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Type-set already knows that (numerator x) and (denominator x)
;;; are integers, and that 0 < (denominator x).

(defthm Rational-implies2               ; Redundant, from axioms.lisp
  (implies (rationalp x)
           (equal (* (/ (denominator x)) (numerator x)) x)))

(local
 (in-theory (enable rewrite-linear-equalities-to-iff)))

(defthm numerator-zero
  (implies (rationalp x)
           (equal (equal (numerator x) 0)
                  (equal x 0)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (equal x 0)
			   (equal (numerator x) 0)))))

(defthm numerator-positive
  (implies (rationalp x)
	   (equal (< 0 (numerator x))
		  (< 0 x)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(< 0 x))
			   (and (integerp (numerator x))
				(< 0 (numerator x)))))
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(<= 0 x))
			   (and (integerp (numerator x))
				(<= 0 (numerator x)))))))

(defthm numerator-negative
  (implies (rationalp x)
	   (equal (< (numerator x) 0)
		  (< x 0)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(< x 0))
			   (and (integerp (numerator x))
				(< (numerator x) 0))))
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(<= x 0))
			   (and (integerp (numerator x))
				(<= (numerator x) 0))))))

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

(defthm |(* r (denominator r))|
  (implies (rationalp r)
	   (equal (* r (denominator r))
		  (numerator r))))

;;; From arithmetic/equalities.lisp

;;; This next rule is too general.  I disable it right away.
;;; I do, however, include a couple of rules similar to this
;;; below.

(defthm /r-when-abs-numerator=1
  (and
   (implies
    (equal (numerator r) 1)
    (equal (/ r)
	   (denominator r)))
   (implies
    (equal (numerator r) -1)
    (equal (/ r)
	   (- (denominator r)))))
  :hints (("Goal" :use ((:instance rational-implies2 (x r)))
           :in-theory (disable rational-implies2))))

(in-theory (disable /r-when-abs-numerator=1))

(defthm |(equal (/ r) (denominator r))|
  (implies (rationalp r)
	   (equal (equal (/ r) (denominator r))
		  (equal (numerator r) 1))))

(defthm |(equal (/ r) (- (denominator r)))|
  (implies (rationalp r)
	   (equal (equal (/ r) (- (denominator r)))
		  (equal (numerator r) -1))))

;;; From arithmetic/rationals.lisp

; We name this Numerator-goes-down-by-integer-division-linear rather than
; Numerator-goes-down-by-integer-division to avoid a conflict with system books
; arithmetic/rationals.lisp.
(defthm
  Numerator-goes-down-by-integer-division-linear
  (implies (and (integerp x)
		(< 0 x)
		(rationalp r))
	   (<= (abs (numerator (* (/ x) r)))
	       (abs (numerator r))))
  :hints (("Goal" :use numerator-goes-down-by-integer-division-pass1))
  :rule-classes ((:linear
		  :corollary
		  (implies (and (integerp x)
				(< 0 x)
				(rationalp r)
				(<= 0 r))
			   (<= (numerator (* (/ x) r))
			       (numerator r))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(< 0 x)
				(rationalp r)
				(<= 0 r))
			   (<= (numerator (* r (/ x)))
			       (numerator r))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(< 0 x)
				(rationalp r)
				(<= r 0))
			   (<= (numerator r)
			       (numerator (* (/ x) r)))))
		 (:linear
		  :corollary
		  (implies (and (integerp x)
				(< 0 x)
				(rationalp r)
				(<= r 0))
			   (<= (numerator r)
			       (numerator (* r (/ x))))))))

;;; From rtl/rel5/denominator.lisp

 (defthm denominator-bound
   (implies (and (integerp x)
                 (integerp y)
                 (< 0 y))
            (<= (denominator (* x (/ y)))
		y))
   :rule-classes ((:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< 0 y))
			   (<= (denominator (* x (/ y)))
			       y)))
		  (:linear
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(< 0 y))
			   (<= (denominator (* (/ y) x))
			       y)))))

(defthm |(denominator (+ x r))|
  (and
   (implies (and (rationalp r)
		 (integerp x))
	    (equal (denominator (+ x r))
		   (denominator r)))
   (implies (and (rationalp r)
		 (integerp x))
	    (equal (denominator (+ r x))
		   (denominator r)))))

