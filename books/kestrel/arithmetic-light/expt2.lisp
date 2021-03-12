; A lightweight book about expt where the base is 2.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Many of these theorems could be generalized to support bases other
;; than 2.

;We make this non-local because it is (currently) needed to have a full theory
;about expt when the base is 2:
(include-book "expt")

(local (include-book "../../arithmetic-3/top"))

(defthm integerp-of-*-of-expt2-and-/-of-expt2
  (implies (and (integerp i1)
                (integerp i2))
           (equal (integerp (* (expt 2 i1) (/ (expt 2 i2))))
                  (<= i2 i1)))
  :hints (("Goal" :use (:instance integerp-of-expt-when-natp (r 2) (i (- i1 i2)))
           :in-theory (disable integerp-of-expt-when-natp))))

(defthm integerp-of-*-of-expt2-and-/-of-expt2-type
  (implies (and (<= i2 i1)
                (integerp i1)
                (integerp i2))
           (integerp (* (expt 2 i1) (/ (expt 2 i2)))))
  :rule-classes :type-prescription)

(defthm integerp-of-*-of-/-of-expt2-and-expt2
  (implies (and (integerp i1)
                (integerp i2))
           (equal (integerp (* (/ (expt 2 i1)) (expt 2 i2)))
                  (<= i1 i2)))
  :hints (("Goal" :use (:instance integerp-of-*-of-expt2-and-/-of-expt2
                                  (i1 i2)
                                  (i2 i1))
           :in-theory (disable  integerp-of-*-of-expt2-and-/-of-expt2))))

(defthm integerp-of-*-of-/-of-expt2-and-expt2-type
  (implies (and (<= i1 i2)
                (integerp i1)
                (integerp i2))
           (integerp (* (/ (expt 2 i1)) (expt 2 i2))))
  :rule-classes :type-prescription)

(defthm expt-bound-linear-weak
  (implies (and (<= size free)
                (integerp free)
                (integerp size))
           (<= (expt 2 size) (expt 2 free)))
  :rule-classes :linear)

(defthm *-of-/-of-expt-and-*-of-expt-of-+
  (implies (and (integerp low)
                (integerp  diff))
           (equal (* (/ (EXPT 2 LOW)) (* (EXPT 2 (+ DIFF LOW)) x))
                  (* (expt 2 diff) x)))
  :hints (("Goal" :in-theory (e/d (expt-of-+)
                                  (normalize-factors-gather-exponents ;looped
                                   )))))

(defthm expt-combine-hack-2
  (implies (and (integerp low)
                (integerp n))
           (equal (* (EXPT 2 LOW) (EXPT 2 (+ (- LOW) N)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (e/d (expt-of-+)
                                  (normalize-factors-gather-exponents ;looped
                                   )))))

(defthm expt-combine-hack
  (implies (and (integerp a)
                (integerp m)
                (integerp n))
           (equal (* (/ (expt 2 m)) (expt 2 (+ a m n)))
                  (expt 2 (+ a n)))))

;todo: can this loop with the definition of expt?
(defthmd expt-hack
  (implies (integerp n)
           (equal (* 2 (expt 2 (+ -1 n)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable expt))))

(theory-invariant (incompatible (:rewrite expt-hack)
                                (:definition expt)))

(defthmd expt-bound-when-negative
  (implies (and (< i 0)
                (integerp i))
           (< (expt 2 i) 1))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (expt 2 i)
           :in-theory (e/d (expt
                            expt-of-+)
                           ()))))

(defthm equal-of-1-and-expt
  (equal (equal 1 (expt 2 n))
         (equal 0 (ifix n)))
  :hints (("Goal" :induct (expt 2 n)
           :in-theory (e/d (expt
                            expt-of-+
                            zip
                            expt-bound-when-negative
                            )
                           (normalize-factors-gather-exponents)))))

(defthmd even-not-equal-odd-hack
  (implies (and (evenp y)
                (not (evenp x)))
           (equal (equal x y)
                  nil)))

(defthm even-odd-expt-hack
  (implies (and (integerp x)
                (posp n))
           (equal (equal (+ -1 (expt 2 n))
                         (* 2 x))
                  nil))
  :hints (("Goal" :in-theory (e/d (expt even-not-equal-odd-hack)
                                  ()))))

(defthm expt-bound-linear
  (implies (and (< i1 i2)
                (integerp i1)
                (integerp i2))
           (< (expt 2 i1) (expt 2 i2)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (expt)
                                  ()))))

;strengthen?
(defthm expt-integer-hack
  (implies (posp n)
           (integerp (* 1/2 (expt 2 n))))
  :hints (("Goal" :in-theory (e/d (expt)
                                  ()))))

(defthmd expt-diff-collect
  (Implies (and (integerp m)
                (integerp n))
           (equal (* (/ (EXPT 2 N)) (EXPT 2 m))
                  (expt 2 (- m n))))
  :hints (("Goal" :in-theory (e/d (expt-of-+)
                                  (NORMALIZE-FACTORS-GATHER-EXPONENTS)))))

;;move and gen
(defthm equal-of-expt-same
  (equal (equal (expt 2 n) 2)
         (equal 1 n))
  :hints (("Goal" :in-theory (e/d (expt zip expt-of-+) ()))))
