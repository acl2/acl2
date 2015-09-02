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

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(include-book "ground-zero")
(local (include-book "../../arithmetic/top"))

(defthm lognot-of-non-integer
  (implies (not (integerp i))
           (equal (lognot i)
                  -1))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-lognot
  (implies (case-split (integerp i))
           (equal (lognot (lognot i))
                  i))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-integerp
  (integerp (lognot i))
    :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-equal-minus-one
  (implies (case-split (integerp i))
           (equal (EQUAL (LOGNOT i) -1)
                  (equal i 0)))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-equal-0
  (implies (case-split (integerp i))
           (equal (EQUAL (LOGNOT i) 0)
                  (equal i -1)))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-<-0
  (implies (case-split (integerp i))
           (equal (< (lognot i) 0)
                  (<= 0 i)))
    :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot->-0
  (implies (case-split (integerp i))
           (equal (< 0 (lognot i))
                  (< i -1)))
    :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-even
  (implies (case-split (integerp i))
           (equal (integerp (* 1/2 (lognot i)))
                  (not (integerp (* 1/2 i)))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of-double
  (implies (case-split (integerp i))
           (EQUAL (LOGNOT (* 2 i))
                  (+ 1 (* 2 (LOGNOT i)))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-of-double-minus-1
  (implies (case-split (integerp i))
           (EQUAL (LOGNOT (1- (* 2 i)))
                  (* 2 (LOGNOT (1- i)))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-simp
  (implies (case-split (integerp i))
           (equal (LOGNOT (+ 1 (* 2 i)))
                  (* 2 (LOGNOT i))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-bound-1
  (implies (case-split (integerp i))
           (equal (< (LOGNOT I) -1)
                  (< 0 i)))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-bound-2
  (implies (case-split (integerp i))
           (equal (< -1 (LOGNOT I))
                  (< i 0)))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-bound-gen
  (implies (and (case-split (integerp i))
                (case-split (rationalp k)))
           (equal (< (LOGNOT I) k)
                  (< (1- (- k)) i)))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm lognot-bound-gen-2
  (implies (and (case-split (integerp i))
                (case-split (rationalp k)))
           (equal (< k (LOGNOT I))
                  (< i (1- (- k)))))
  :hints (("Goal" :in-theory (enable lognot))))


;from ihs
(defthm cancel-equal-lognot
  (equal (equal (lognot i) (lognot j))
         (equal (ifix i) (ifix j)))
  :hints (("Goal" :in-theory (enable lognot))))



(defthm fl-lognot
  (implies (case-split (integerp i))
           (= (fl (* 1/2 (lognot i)))
              (lognot (fl (* 1/2 i)))))
  :hints (("Goal" :in-theory (enable lognot))))

(defthm floor-lognot
  (implies (case-split (integerp i))
           (equal (floor (lognot i) 2)
                  (lognot (floor i 2)))))

(defthm mod-lognot-by-2
  (implies (case-split (integerp i))
           (equal (mod (lognot i) 2)
                  (+ 2 (lognot (mod i 2)))))
  :hints (("Goal" :in-theory (enable lognot mod-mult-of-n mod-by-2-rewrite-to-even)))
  )
