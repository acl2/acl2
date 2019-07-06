; A lightweight book about the built-in functions floor and expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "floor"))
(local (include-book "expt"))
(local (include-book "expt2"))
(local (include-book "times"))
(local (include-book "divides"))
(local (include-book "times-and-divides"))
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "plus"))
(local (include-book "minus"))
(local (include-book "nonnegative-integer-quotient"))

(defthm floor-of-expt-and-2
  (implies (posp n)
           (equal (floor (expt 2 n) 2)
                  (expt 2 (+ -1 n))))
  :hints (("Goal" :in-theory (e/d (expt-of-+
                                   floor-normalize-denominator)
                                  (floor-of-times-1/2
                                   floor-of-*-of-/-and-1)))))

(defthm floor-of-times-2-expt
  (implies (integerp n)
           (equal (floor (* 2 i) (expt 2 n))
                  (floor i (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (e/d (floor-normalize-denominator
                                   expt-of-+)
                                  (;divisibility-in-terms-of-floor ;looped
                                   floor-of-*-of-/-and-1
                                   )))))

; we shift right, chop, then shift back.  then doing it again with a smaller
; shift amount has no effect.
(defthm floor-shifting-lemma
  (implies (and (<= low n)
                (natp n)
                (natp low))
           (equal (* (expt 2 low)
                     (floor (* (expt 2 n) (floor i (expt 2 n)))
                            (expt 2 low)))
                  (* (expt 2 n) (floor i (expt 2 n)))))
  :hints (("Goal" :in-theory (enable floor-when-multiple
                                     integerp-of-*-three))))

(defthm floor-of--1-and-expt
  (implies (natp n)
           (equal (floor -1 (expt 2 n))
                  -1))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-of-floor-special
  (implies (and (integerp i)
                (posp n))
           (equal (floor (floor i 2) (* 1/2 (expt 2 n)))
                  (floor i (expt 2 n))))
  :hints (("Goal" :in-theory (enable floor-of-floor))))

(defthm floor-of-*-of-expt-and-expt
  (implies  (and (< size size2)
                 (natp size)
                 (integerp size2)
                 (integerp i))
            (equal (floor (* i (expt 2 size))
                          (expt 2 size2))
                   (floor i (expt 2 (- size2 size)))))
  :hints (("Goal" :in-theory (e/d (floor-normalize-denominator expt-of-+)
                                  (FLOOR-OF-*-OF-/-AND-1)))))
