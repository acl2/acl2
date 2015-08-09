;;; Contributed by Ruben A. Gamboa

; Copyright (C) 2014, University of Wyoming
; All rights reserved.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

#|

This file contains some obvious theorems about the integer division and
related functions.  This should be developed into a significant library,
but for now, we're just keeping the theorems that we need.

|#

(in-package "ACL2")

(include-book "top")

(defthm quotient-cancellation
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y)
		(integerp z) (< 0 z))
	   (equal (nonnegative-integer-quotient (* z x) (* z y))
		  (nonnegative-integer-quotient x y))))

(defthm quotient-numer-denom-lemma
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (equal (nonnegative-integer-quotient (* (numerator (/ x y))
						   (denominator (/ x y))
						   x)
						(* (numerator (/ x y))
						   (denominator (/ x y))
						   y))
		  (nonnegative-integer-quotient x y)))
  :hints (("Goal"
	   :use (:instance quotient-cancellation
			   (z (* (numerator (/ x y)) (denominator (/ x y)))))
	   :in-theory (disable quotient-cancellation))))

(defthm numer-denom-lemma-silly
  (implies (and (acl2-numberp x) (acl2-numberp y) (not (equal 0 y)))
	   (equal (* x d)
		  (* y x (/ y) d)))
  :rule-classes nil)

(defthm numer-denom-lemma
  (implies (and (integerp x) (integerp y) (not (equal 0 y)))
	   (and (equal (* (denominator (/ x y)) x)
		       (* (numerator (/ x y)) y))))
  :hints (("Goal" :use (:instance Rational-implies2 (x (/ x y)))
	   :in-theory (disable Rational-implies2 equal-*-/-2))
	  ("Goal'4'" :use (:instance numer-denom-lemma-silly
				     (d (denominator (* x (/ y))))))))

(defthm quotient-numer-denom-lemma2-silly
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y)
		(acl2-numberp d) (acl2-numberp n) (not (= 0 d))
		(equal (* d x) (* n y)))
	   (equal (* X d d)
		  (* Y d n)))
  :rule-classes nil)

(defthm quotient-numer-denom-lemma2
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (equal (* X (DENOMINATOR (* X (/ Y)))
		     (DENOMINATOR (* X (/ Y))))
		  (* Y (DENOMINATOR (* X (/ Y)))
		     (NUMERATOR (* X (/ Y))))))
  :hints (("Goal" :use (:instance quotient-numer-denom-lemma2-silly
				  (d (DENOMINATOR (* X (/ Y))))
				  (n (NUMERATOR (* X (/ Y))))))))

(defthm quotient-numer-denom-lemma3
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (equal (nonnegative-integer-quotient (* (numerator (/ x y))
						   (denominator (/ x y))
						   x)
						(* (numerator (/ x y))
						   (denominator (/ x y))
						   y))
		  (nonnegative-integer-quotient (numerator (/ x y))
						(denominator (/ x y)))))
  :hints (("Goal"
	   :use ((:instance quotient-cancellation
			    (x (numerator (/ x y)))
			    (y (denominator (/ x y)))
			    (z (* (denominator (/ x y)) x)))
		 (:instance numer-denom-lemma))
	   :in-theory (disable quotient-cancellation numer-denom-lemma))))

(defthm quotient-numer-denom
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (equal (nonnegative-integer-quotient (numerator (/ x y))
						(denominator (/ x y)))
		  (nonnegative-integer-quotient x y)))
  :hints (("Goal" :use ((:instance quotient-numer-denom-lemma)
			(:instance quotient-numer-denom-lemma3))
	   :in-theory (disable quotient-numer-denom-lemma
			       quotient-numer-denom-lemma3))))

(defthm remainder-theorem-1
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (equal (+ (* (truncate x y) y) (rem x y)) x)))

(defthm remainder-lemma
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (< (- x (* y (nonnegative-integer-quotient x y))) y))
  :rule-classes (:rewrite :linear))

(defthm remainder-theorem-2
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (< (rem x y) y)))

(defthm quotient-lower-bound
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (<= (nonnegative-integer-quotient x y)
	       (/ x y)))
  :rule-classes (:linear :rewrite))

(defthm quotient-upper-bound
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (< (/ x y)
	      (1+ (nonnegative-integer-quotient x y))))
  :hints (("Goal" :use (:instance remainder-lemma)
	   :in-theory (disable remainder-lemma)))
  :rule-classes (:rewrite :linear))

(defthm truncate-lower-bound
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (<= (truncate x y) (/ x y)))
  :rule-classes (:linear :rewrite))

(defthm truncate-upper-bound
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (< (/ x y) (1+ (truncate x y))))
  :rule-classes (:linear :rewrite))

(defthm rem-lower-bound
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (<= 0 (rem x y)))
  :rule-classes (:linear :rewrite))

(defthm rem-upper-bound
  (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
	   (< (rem x y) y))
  :rule-classes (:linear :rewrite))

