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

; This file is based on the old "fp book", which was initially created by J
; Moore and Matt Kaufmann in 1995 in support of their proof of the AMD-K5
; division code.    Here, we have moved
; non-local in-theory events to the end.  All events should be redundant, so we
; have deleted all local in-theory events and added (local (in-theory nil)) to
; the beginning.

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../../arithmetic/fp"))
(local (include-book "../../arithmetic/fp2"))
(local (include-book "../../arithmetic/fl"))
(local (include-book "../../arithmetic/expt"))
(local (include-book "../../arithmetic/expo"))
(local (include-book "../../arithmetic/extra-rules"))
(local (include-book "../support/ash"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)

(defthm a1 (equal (+ x (+ y z)) (+ y (+ x z))))
(defthm a2 (equal (- x) (* -1 x)))

(defthm a3
  (and
   (implies
    (syntaxp (and (quotep c1) (quotep c2)))
    (and (equal (+ (* c1 x) (* c2 x)) (* (+ c1 c2) x))
         (equal (+ (* c1 x) (+ (* c2 x) y)) (+ (* (+ c1 c2) x) y))))
   (implies
    (syntaxp (quotep c2))
    (and (equal (+ x (* c2 x)) (* (+ 1 c2) x))
         (equal (+ x (+ (* c2 x) y1)) (+ (* (+ 1 c2) x) y1))
         (equal (+ x (+ y1 (* c2 x))) (+ (* (+ 1 c2) x) y1))
         (equal (+ x (+ y1 (+ (* c2 x) y2))) (+ (* (+ 1 c2) x) y1 y2))
         (equal (+ x (+ y1 (+ y2 (* c2 x)))) (+ (* (+ 1 c2) x) y1 y2))
         (equal (+ x (+ y1 (+ y2 (+ y3 (* c2 x)))))
                (+ (* (+ 1 c2) x) y1 y2 y3))
         (equal (+ x (+ y1 (+ y2 (+ (* c2 x) y3))))
                (+ (* (+ 1 c2) x) y1 y2 y3))))
   (and (equal (+ x x) (* 2 x))
        (equal (+ x (+ x y1)) (+ (* 2 x) y1)))))
(defthm a4
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (+ c1 (+ c2 y1)) (+ (+ c1 c2) y1))))
(defthm a5
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (* c1 (* c2 y1)) (* (* c1 c2) y1))))





(defthm a6
  (equal (/ (/ x)) (fix x)))
(defthm a7
  (equal (/ (* x y)) (* (/ x) (/ y))))

;replaced force with case-split
(defthm a8
  (implies (and (case-split (acl2-numberp x))
                (case-split (not (equal x 0))))
           (and (equal (* x (* (/ x) y)) (fix y))
                (equal (* x (/ x)) 1))))

(defthm a9
  (and (equal (* 0 x) 0)
       (equal (* x (* y z)) (* y (* x z)))
       (equal (* x (+ y z)) (+ (* x y) (* x z)))
       (equal (* (+ y z) x) (+ (* y x) (* z x)))))

(defun fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))



(defthm a10
  (and (implies (integerp i) (equal (fl i) i))
       (implies (and (integerp i)
                     (case-split (rationalp x1)) ;can actually drop this
                     )
                (and (equal (fl (+ i x1)) (+ i (fl x1)))
                     (equal (fl (+ x1 i)) (+ i (fl x1)))))
       (implies (and (integerp i)
                     (case-split (rationalp x1))
                     (case-split (rationalp x2)))
                (and (equal (fl (+ x1 (+ i x2))) (+ i (fl (+ x1 x2))))
                     (equal (fl (+ x1 (+ x2 i))) (+ i (fl (+ x1 x2))))))
       (implies (and (integerp i)
                     (case-split (rationalp x1))
                     (case-split (rationalp x2))
                     (case-split (rationalp x3)))
                (and (equal (fl (+ x1 (+ x2 (+ i x3))))
                            (+ i (fl (+ x1 x2 x3))))
                     (equal (fl (+ x1 (+ x2 (+ x3 i))))
                            (+ i (fl (+ x1 x2 x3))))))
       (implies (and (integerp i)
                     (case-split (rationalp x1))
                     (case-split (rationalp x2))
                     (case-split (rationalp x3))
                     (case-split (rationalp x4)))
                (and (equal (fl (+ x1 (+ x2 (+ x3 (+ i x4)))))
                            (+ i (fl (+ x1 x2 x3 x4))))
                     (equal (fl (+ x1 (+ x2 (+ x3 (+ x4 i)))))
                            (+ i (fl (+ x1 x2 x3 x4))))))))

(defthm a12
  (implies (and (integerp i)
                (integerp j)
                (< 1 j)
                (< j i))
           (and (< (acl2-count (fl (/ i j))) (acl2-count i))
                (< (acl2-count (fl (* (/ j) i))) (acl2-count i))))
  :rule-classes :linear)


;replaced force with case-split
;later, drop the hyp completely
(defthm a13
  (implies (case-split (rationalp x)) ;drop!
           (and (< (1- x) (fl x))
                (<= (fl x) x)))
  :rule-classes :linear)

(defthm a14
  (and
   (implies (and (integerp i)
                 (<= 0 i)
                 (<= 0 j))
            (and (integerp (expt i j))
                 (<= 0 (expt i j))))
   (implies (and (rationalp i)
                 (not (equal i 0)))
            (not (equal (expt i j) 0))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (and (integerp i)
                  (<= 0 i)
                  (<= 0 j))
             (and (integerp (expt i j))
                  (<= 0 (expt i j)))))
   (:type-prescription
    :corollary
    (implies (and (rationalp i)
                  (not (equal i 0)))
             (not (equal (expt i j) 0))))))

(defthm a15
  (implies (and (rationalp i)
                (not (equal i 0))
                (integerp j1)
                (integerp j2))
           (and (equal (* (expt i j1) (expt i j2))
                       (expt i (+ j1 j2)))
                (equal (* (expt i j1) (* (expt i j2) x))
                       (* (expt i (+ j1 j2)) x)))))
(defthm a16
  (equal (expt (* a b) i)
         (* (expt a i) (expt b i))))

(defthm /-weakly-monotonic
  (implies (and (<= y y+)
                (< 0 y)
                (case-split (rationalp y))
                (case-split (rationalp y+))
                )
           (<= (/ y+) (/ y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

(defthm /-strongly-monotonic
  (implies (and (< y y+)
                (< 0 y)
                (case-split (rationalp y))
                (case-split (rationalp y+))
                )
           (< (/ y+) (/ y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

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

(defthm *-strongly-monotonic-negative-multiplier
  (implies (and (< y y+)
                (< x 0)
                (case-split (rationalp x))
                )
           (< (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (< y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (< (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and (< y y+)
                  (< x 0)
                  (case-split (rationalp x))
                  )
             (< (* y+ x) (* y x))))))

(defthm fl-weakly-monotonic
  (implies (and (<= y y+)
                (case-split (rationalp y)) ;drop?
                (case-split (rationalp y+)) ;drop?
                )
           (<= (fl y) (fl y+)))
  :rule-classes ((:forward-chaining :trigger-terms ((fl y) (fl y+)))
                 (:linear)
                 (:forward-chaining
                  :trigger-terms ((fl y) (fl y+))
                  :corollary (implies (and (< y y+)
                                           (case-split (rationalp y))
                                           (case-split (rationalp y+)))
                                      (<= (fl y) (fl y+))))
                 (:linear
                  :corollary (implies (and (< y y+)
                                           (case-split (rationalp y))
                                           (case-split (rationalp y+)))
                                      (<= (fl y) (fl y+))))))

 (deftheory arith-fc-monotonicity
   '((:forward-chaining /-weakly-monotonic)
     (:forward-chaining /-strongly-monotonic)
     (:forward-chaining *-weakly-monotonic . 1)
     (:forward-chaining *-weakly-monotonic . 2)
     (:forward-chaining *-strongly-monotonic . 1)
     (:forward-chaining *-strongly-monotonic . 2)
     (:forward-chaining *-weakly-monotonic-negative-multiplier . 1)
     (:forward-chaining *-weakly-monotonic-negative-multiplier . 2)
     (:forward-chaining *-strongly-monotonic-negative-multiplier . 1)
     (:forward-chaining *-strongly-monotonic-negative-multiplier . 2)
     (:forward-chaining fl-weakly-monotonic . 1)
     (:forward-chaining fl-weakly-monotonic . 2)
     ))

; We now prove a bunch of bounds theorems for *.  We are concerned with bounding the
; product of a and b given intervals for a and b.  We consider three kinds of intervals.
; We discuss only the a case.

; abs intervals mean (abs a) < amax or -amax < a < amax, where amax is positive.

; nonneg-open intervals mean 0<=a<amax.

; nonneg-closed intervals mean 0<=a<=amax, where amax is positive.

; We now prove theorems with names like abs*nonneg-open, etc. characterizing
; the product of two elements from two such intervals.  All of these theorems
; are made with :rule-classes nil because I don't know how to control their
; use.

; This lemma is for lookup * d and lookup * away.  We don't need to consider 0
; < b for the d case because we have 0 < 1 <= d and the conclusion of the new
; lemma would be no different.

(defthm abs*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (<= a amax) ; (< a amax) is all we'll ever use, I bet.
                (< 0 amax)
                (<= 0 b)
                (< b bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :rule-classes nil)



(defthm abs*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :rule-classes nil)

(defthm nonneg-closed*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* b a))
                (< (* b a) (* amax bmax))))
  :rule-classes nil)

(defthm nonneg-open*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (<= a amax) ; (< a amax) is all we'll ever use, I bet.
                (< 0 amax)
                (<= 0 b)
                (< b bmax))
           (and (< (- (* bmax amax)) (* a b))
                (< (* a b) (* bmax amax))))
  :rule-classes nil)

; The next three, which handle nonnegative open intervals in the first argument,
; can actually be seen as uses of the abs intervals above.  Simply observe that
; if 0<=a<amax then -amax<a<amax.

(defthm nonneg-open*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* a b))
                (< (* a b) (* amax bmax))))
  :rule-classes nil)

(defthm nonneg-open*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (< b bmax))
           (and (<= 0 (* a b))
                (< (* a b) (* amax bmax))))
  :rule-classes nil)

; and the commuted version
(defthm nonneg-closed*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* b a))
                (< (* b a) (* amax bmax))))
  :rule-classes nil)

(defthm nonneg-closed*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (<= a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* a b))
                (<= (* a b) (* amax bmax))))
  :rule-classes nil)

(defthm abs*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (< (- bmax) b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :rule-classes nil)

(defthm rearrange-negative-coefs-<
  (and (equal (< (* (- c) x) z)
              (< 0 (+ (* c x) z)))
       (equal (< (+ (* (- c) x) y) z)
              (< y (+ (* c x) z)))
       (equal (< (+ y (* (- c) x)) z)
              (< y (+ (* c x) z)))
       (equal (< (+ y1 y2 (* (- c) x)) z)
              (< (+ y1 y2) (+ (* c x) z)))
       (equal (< (+ y1 y2 y3 (* (- c) x)) z)
              (< (+ y1 y2 y3) (+ (* c x) z)))
       (equal (< z (+ (* (- c) x) y))
              (< (+ (* c x) z) y))
       (equal (< z (+ y (* (- c) x)))
              (< (+ (* c x) z) y))
       (equal (< z (+ y1 y2 (* (- c) x)))
              (< (+ (* c x) z) (+ y1 y2)))
       (equal (< z (+ y1 y2 y3 (* (- c) x)))
              (< (+ (* c x) z) (+ y1 y2 y3)))))

(defthm rearrange-negative-coefs-equal
  (and (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp z)))
                (equal (equal (* (- c) x) z)
                       (equal 0 (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal (+ (* (- c) x) y) z)
                       (equal y (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal (+ y (* (- c) x)) z)
                       (equal y (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp z)))
                (equal (equal (+ y1 y2 (* (- c) x)) z)
                       (equal (+ y1 y2) (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp y3))
                     (case-split (rationalp z)))
                (equal (equal (+ y1 y2 y3 (* (- c) x)) z)
                       (equal (+ y1 y2 y3) (+ (* c x) z))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal z (+ (* (- c) x) y))
                       (equal (+ (* c x) z) y)))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y))
                     (case-split (rationalp z)))
                (equal (equal z (+ y (* (- c) x)))
                       (equal (+ (* c x) z) y)))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp z)))
                (equal (equal z (+ y1 y2 (* (- c) x)))
                       (equal (+ (* c x) z) (+ y1 y2))))
       (implies (and (case-split (rationalp c))
                     (case-split (rationalp x))
                     (case-split (rationalp y1))
                     (case-split (rationalp y2))
                     (case-split (rationalp y3))
                     (case-split (rationalp z)))
                (equal (equal z (+ y1 y2 y3 (* (- c) x)))
                       (equal (+ (* c x) z) (+ y1 y2 y3))))))

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
                   (< (* c z) (+ (* c y1) (* c y2) (* c y3) x))))))

(defthm rearrange-fractional-coefs-equal
  (and
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (< 0 c))
            (equal (equal (* (/ c) x) z)
                   (equal x (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y))
                 (< 0 c))
            (equal (equal (+ (* (/ c) x) y) z)
                   (equal (+ x (* c y)) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y))
                 (< 0 c))
            (equal (equal (+ y (* (/ c) x)) z)
                   (equal (+ (* c y) x) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y1))
                 (case-split (rationalp y2))
                 (< 0 c))
            (equal (equal (+ y1 y2 (* (/ c) x)) z)
                   (equal (+ (* c y1) (* c y2) x) (* c z))))
   (implies (and (case-split (rationalp c))
                 (case-split (rationalp z))
                 (case-split (rationalp x))
                 (case-split (rationalp y1))
                 (case-split (rationalp y2))
                 (case-split (rationalp y3))
                 (< 0 c))
            (equal (equal (+ y1 y2 y3 (* (/ c) x)) z)
                   (equal (+ (* c y1) (* c y2) (* c y3) x) (* c z))))))

(defthm x*/y=1->x=y
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal x 0))
                (not (equal y 0)))
           (equal (equal (* x (/ y)) 1)
                  (equal x y)))
  :rule-classes nil)

(defun point-right-measure (x)
  (floor (if (and (rationalp x) (< 0 x)) (/ x) 0) 1))

(defun point-left-measure (x)
  (floor (if (and (rationalp x) (> x 0)) x 0) 1))

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defthm recursion-by-point-right
  (and (e0-ordinalp (point-right-measure x))
       (implies (and (rationalp x)
                     (< 0 x)
                     (< x 1))
                (e0-ord-< (point-right-measure (* 2 x))
                          (point-right-measure x)))))

(defthm recursion-by-point-left
  (and (e0-ordinalp (point-left-measure x))
       (implies (and (rationalp x)
                     (>= x 2))
                (e0-ord-< (point-left-measure (* 1/2 x))
                          (point-left-measure x)))))

(defthm x<x*y<->1<y
  (implies (and (rationalp x)
                (< 0 x)
                (rationalp y))
           (equal (< x (* x y)) (< 1 y)))
  :rule-classes nil)

(defthm cancel-equal-*
  (implies (and (rationalp r)
                (rationalp s)
                (rationalp a)
                (not (equal a 0)))
           (equal (equal (* a r) (* a s))
                  (equal r s)))
  :rule-classes nil)

(defthmd expt-split
  (implies (and (integerp i)
                (integerp j)
                (case-split (acl2-numberp r)) ;(integerp r)
                (case-split (not (equal r 0)))
                )
           (equal (expt r (+ i j))
                  (* (expt r i) (expt r j)))))

(defthm cancel-<-*
  (implies (and (rationalp r)
                (rationalp s)
                (rationalp a)
                (< 0 a))
           (equal (< (* a r) (* a s))
                  (< r s)))
  :rule-classes nil)

(in-theory (disable fl
                    inverse-of-*
                    point-right-measure point-left-measure))


;;;**********************************************************************
;;;                       EXPONENTIATION
;;;**********************************************************************

(defthm expt-2-positive-rational-type
  (and (rationalp (expt 2 i))
       (< 0 (expt 2 i)))
  :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))

(defthm expt-2-positive-integer-type
  (implies (<= 0 i)
           (and (integerp (expt 2 i))
                (< 0 (expt 2 i))))
  :rule-classes (:type-prescription))

(defthm expt-2-type-linear
  (implies (<= 0 i)
           (<= 1 (expt 2 i)))
  :rule-classes ((:linear :trigger-terms ((expt 2 i)))))

(defthmd expt-weak-monotone
  (implies (and (integerp n)
                (integerp m))
           (equal (<= (expt 2 n) (expt 2 m))
		  (<= n m))))

(defthmd expt-strong-monotone
  (implies (and (integerp n)
                (integerp m))
           (equal (< (expt 2 n) (expt 2 m))
		  (< n m))))

(defthmd expt-inverse
  (equal (/ (expt 2 i))
         (expt 2 (* -1 i))))

(defthm ash-rewrite
    (implies (integerp n)
	     (equal (ash n i)
		    (fl (* n (expt 2 i))))))

(defthm exp+1
    (implies (and (integerp m)
		  (integerp n)
		  (<= n m))
	     (> (* (- 1 (expt 2 m)) (- 1 (expt 2 n)))
		(- 1 (expt 2 (1+ m)))))
  :rule-classes ())

(defthm exp+2
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (< (* (1+ (expt 2 m)) (1+ (expt 2 n)))
		(1+ (expt 2 (+ m 2)))))
  :rule-classes ())

(defthm exp-invert
    (implies (and (integerp n)
		  (<= n -1))
	     (<= (/ (- 1 (expt 2 n)))
		 (1+ (expt 2 (1+ n)))))
  :rule-classes ())
