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
(local (include-book "times-and-divides"))

(defthm floor-of-expt-and-2
  (implies (posp n)
           (equal (floor (expt 2 n) 2)
                  (expt 2 (+ -1 n))))
  :hints (("Goal" :in-theory (e/d (expt-of-+
                                   floor-normalize-denominator)
                                  ()))))

(defthm floor-of-times-2-expt
  (implies (integerp n)
           (equal (floor (* 2 i) (expt 2 n))
                  (floor i (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (e/d (floor-normalize-denominator
                                   expt-of-+)
                                  (;divisibility-in-terms-of-floor ;looped
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
