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

;Rename this book, since the guts have been ripped out?
;BOZO clean up this book?
;BOZO move these lemmas to extra?
#|

This book contains a few lemmas which are exported in lib/arith but which aren't needed in support/ or
arithmetic/.

|#

(local (include-book "fp2"))

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



; We now prove a bunch of bounds theorems for *.  We are concerned with bounding the
; product of a and b given intervals for a and b.  We consider three kinds of intervals.
; We discuss only the a case.

; abs intervals mean (abs a) < amax or -amax < a < amax, where amax is positive.

; nonneg-open intervals mean 0<=a<amax.

; nonneg-closed intervals mean 0<=a<=amax, where amax is positive.

; We now prove theorems with names like abs*nonneg-open, etc. characterizing
; the product of two elements from two such interals.  All of these theorems
; are made with :rule-classes nil because I don't know how to control their
; use.

(encapsulate nil
  (local
   (defthm renaming
    (implies (and (rationalp a)
                  (rationalp xmax)
                  (rationalp b)
                  (rationalp bmax)
                  (< (- xmax) a)
                  (<= a xmax)
                  (< 0 xmax)
                  (<= 0 b)
                  (< b bmax))
             (and (< (- (* xmax bmax)) (* a b))
                  (< (* a b) (* xmax bmax))))
    :hints (("Goal" :cases ((equal b 0))))))

; This lemma is for lookup * d and lookup * away.  We don't need to consider 0
; < b for the d case because we have 0 < 1 <= d and the conclusion of the new
; lemma would be no different.

  (defthm abs*nonneg-open
    (implies (and (rationalp a)
                  (rationalp amax)
                  (rationalp b)
                  (rationalp bmax)
                  (< (- amax) a)
                  (<= a amax)       ; (< a amax) is all we'll ever use, I bet.
                  (< 0 amax)
                  (<= 0 b)
                  (< b bmax))
             (and (< (- (* amax bmax)) (* a b))
                  (< (* a b) (* amax bmax))))
    :hints (("Goal" :by renaming))
    :rule-classes nil))

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
  :hints (("Goal" :cases ((equal b 0))))
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
  :hints (("Goal" :use abs*nonneg-closed))
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
    :hints (("Goal" :use abs*nonneg-open))
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
  :hints (("Goal" :use abs*nonneg-closed))
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
  :hints (("Goal" :use abs*nonneg-open))
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
  :hints (("Goal" :use nonneg-open*nonneg-closed))
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
  :hints (("Goal" :cases ((< b 0) (> b 0))))
  :rule-classes nil)
