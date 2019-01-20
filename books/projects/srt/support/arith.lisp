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

(in-package "RTL")
(include-book "rtl/rel11/lib/util" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(defthm *-weakly-monotonic
  (implies (and (<= y y+)
                (<= 0 x)
                (case-split (rationalp x)) ; This does not hold if x, y, and z are complex!
                )
           (<= (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (<= y y+)
                  (<= 0 x)
                  (case-split (rationalp x))
                  )
             (<= (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and (<= y y+)
                  (<= 0 x)
                  (case-split (rationalp x))
                  )
             (<= (* y x) (* y+ x))))))

#| Here is the complex counterexample to which we alluded above.

(let ((y  #c(1 -1))
      (y+ #c(1 1))
      (x  #c(1 1)))
    (implies (and (<= y y+)
                  (<= 0 x))
             (<= (* x y) (* x y+))))
|#

(defthm *-strongly-monotonic
  (implies (and (< y y+)
                (< 0 x)
                (case-split (rationalp x))
                )
           (< (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (< y y+)
                  (< 0 x)
                  (case-split (rationalp x))
                  )
             (< (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and (< y y+)
                  (< 0 x)
                  (case-split (rationalp x))
                  )
             (< (* y x) (* y+ x))))))

(defthm *-weakly-monotonic-negative-multiplier
  (implies (and (<= y y+)
               (< x 0)
               (case-split (rationalp x))
               )
           (<= (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (<= y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (<= (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and (<= y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (<= (* y+ x) (* y x))))))

(defthm rearrange-fractional-coefs-<
  (and
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (< 0 c))
            (equal (< (* (/ c) x) z)
                   (< x (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y))
                 (< 0 c))
            (equal (< (+ (* (/ c) x) y) z)
                   (< (+ x (* c y)) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y))
                 (< 0 c))
            (equal (< (+ y (* (/ c) x)) z)
                   (< (+ (* c y) x) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y1))
                 (case-split (rationalp y2))
                 (< 0 c))
            (equal (< (+ y1 y2 (* (/ c) x)) z)
                   (< (+ (* c y1) (* c y2) x) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y1))
                 (case-split (rationalp y2))
                 (case-split (rationalp y3))
                 (< 0 c))
            (equal (< (+ y1 y2 y3 (* (/ c) x)) z)
                   (< (+ (* c y1) (* c y2) (* c y3) x) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (< 0 c))
            (equal (< z (* (/ c) x))
                   (< (* c z) x)))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y))
                 (< 0 c))
            (equal (< z (+ (* (/ c) x) y))
                   (< (* c z) (+ x (* c y)))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y))
                 (< 0 c))
            (equal (< z (+ y (* (/ c) x)))
                   (< (* c z) (+ (* c y) x))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y1))
                 (case-split (rationalp y2))
                 (< 0 c))
            (equal (< z (+ y1 y2 (* (/ c) x)))
                   (< (* c z) (+ (* c y1) (* c y2) x))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y1))
                 (case-split (rationalp y2))
                 (case-split (rationalp y3))
                 (< 0 c))
            (equal (< z (+ y1 y2 y3 (* (/ c) x)))
                   (< (* c z) (+ (* c y1) (* c y2) (* c y3) x)))))
  :hints (("goal" :nonlinearp t)))

;;;**********************************************************************
;;;                       EXPONENTIATION
;;;**********************************************************************

(defthm expt-positive-integer-type
    (implies (and (integerp a)
		  (integerp i)
		  (>= i 0))
	     (integerp (expt a i)))
  :rule-classes (:type-prescription))


(defthm expt-2-positive-rational-type
  (and (rationalp (expt 2 i))
       (< 0 (expt 2 i)))
  :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))
