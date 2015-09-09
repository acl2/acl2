; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

;This book introduces the function cg (for "ceiling"), which is in many ways analogous to fl and which is used
;in the definition of the "away" rounding mode.

;todo: prove more thms about cg analogous to those about fl (maybe not worth doing since only fl is used to
;define, for example, bits).

(local (include-book "fl"))
(local (include-book "fp2"))
(local (include-book "integerp"))
(local (include-book "integerp"))
(local (include-book "arith2"))
(local (include-book "common-factor"))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defthm cg-def-linear
  (implies (case-split (rationalp x))
           (and (>= (cg x) x)
                (> (1+ x) (cg x))))
  :hints (("Goal" :in-theory (enable cg)))
  :rule-classes :linear)

(defthm cg-monotone-linear
  (implies (and (rationalp x)
                (rationalp y)
                (<= x y))
           (<= (cg x) (cg y)))
  :rule-classes :linear)

(defthm n>=cg-linear
  (implies (and (>= n x)
                (rationalp x)
                (integerp n))
           (>= n (cg x)))
  :rule-classes :linear)

(defthm cg+int-rewrite
  (implies (and (integerp n)
                (rationalp x))
           (equal (cg (+ x n)) (+ (cg x) n))))

(local
 (defthm cg/int-1
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (cg (/ (cg x) n))
		 (cg (/ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cg-def-linear)
			(:instance cg-monotone-linear (x (/ x n)) (y (/ (cg x) n))))))))

(local
 (defthm cg/int-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (cg (/ (cg x) n))
		 (cg (/ x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance n>=cg-linear (n (* n (cg (/ x n)))))
			(:instance n>=cg-linear (n (cg (/ x n))) (x (/ (cg x) n)))
			(:instance cg-def-linear (x (/ x n))))))))

(defthm cg/int-rewrite
  (implies (and (integerp n)
                (> n 0)
                (rationalp x))
           (equal (cg (* (cg x) (/ n)))
                  (cg (/ x n))))
  :hints (("Goal" :use ((:instance cg/int-1)
			(:instance cg/int-2)))))

(defthm cg/int-rewrite-alt
  (implies (and (integerp n)
                (> n 0)
                (rationalp x))
           (equal (cg (* (/ n) (cg x)))
                  (cg (/ x n))))
  :hints (("Goal" :use ((:instance cg/int-1)
			(:instance cg/int-2)))))

(defthm int-cg-rules
  (implies (rationalp x)
           (integerp (cg x)))
  :rule-classes (:rewrite :type-prescription))

(defthm cg-int
    (implies (integerp x)
	     (equal (cg x) x)))

(defthm cg-integerp
    (implies (rationalp x)
	     (equal (equal (cg x) x)
                    (integerp x))))

(defthm cg-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (>= n x)
		  (> (1+ x) n))
	     (equal (cg x) n))
  :rule-classes ())



(defthm fl-cg
  (implies (rationalp x)
           (equal (cg x)
                  (if (integerp x)
                      (fl x)
                    (1+ (fl x)))))
  :rule-classes ())

(defthm cg-integer-type
  (integerp (cg x))
  :rule-classes ( :type-prescription))

(defthmd cg-def
  (and (integerp (cg x))
       (implies (case-split (rationalp x))
                (and (>= (cg x) x)
                     (> (1+ x) (cg x)))))
  :rule-classes ((:linear :corollary
                          (implies (case-split (rationalp x))
                                   (and (>= (cg x) x)
                                        (> (1+ x) (cg x)))))
                 (:type-prescription :corollary
                                     (integerp (cg x)))))

(defthm cg-positive
  (implies (case-split (not (complex-rationalp x)))
           (equal (< 0 (cg x))
                  (< 0 x)))
  :hints (("Goal" :in-theory (enable cg)))
  )
