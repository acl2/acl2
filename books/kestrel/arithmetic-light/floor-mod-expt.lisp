; A lightweight book about floor, mod, and expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
; For mod-sum-cases, see the copyright on the RTL library.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Theorem rationalp-of-mod below may not hold in ACL2(r), so for now we
;; disable certification of this book in ACL2(r):
; cert_param: (non-acl2r)

(local (include-book "times"))
(local (include-book "plus"))
(local (include-book "floor"))
(local (include-book "mod"))
(local (include-book "floor-and-expt"))
(local (include-book "mod-and-expt"))
(local (include-book "../../arithmetic-3/floor-mod/floor-mod"))

;not clear which is better
(defthm floor-of-mod-of-expt-and-expt
  (implies (and (<= low n)
                (natp low)
                (natp n)
                (integerp x))
           (equal (floor (mod x (expt 2 n)) (expt 2 low))
                  (mod (floor x (expt 2 low))
                       (expt 2 (+ (- low) n)))))
  :hints (("Goal"
           :in-theory (e/d (integerp-of-*-three
                            mod
                            floor-of-sum
                            floor-of---arg1)
                           (equal-of-*-2-of-floor-of-2-same)))))

;special case
;not clear which is better
(defthm mod-floor-2-expt-2
  (implies (and (integerp x)
                (posp n))
           (equal (floor (mod x (expt 2 n)) 2)
                  (mod (floor x 2) (expt 2 (+ -1 n)))))
  :hints (("Goal" :use (:instance floor-of-mod-of-expt-and-expt (low 1))
           :in-theory (disable floor-of-mod-of-expt-and-expt))))

(defthmd mod-of-floor-of-2-and-expt-of-one-less
  (implies (and (natp n)
                (integerp j))
           (equal (mod (floor j 2) (* 1/2 (expt 2 n)))
                  (floor (mod j (expt 2 n)) 2)))
  :hints (("Goal" :use (:instance floor-of-mod-of-expt-and-expt
                                  (x j)
                                  (n n)
                                  (low 1))
           :in-theory (disable floor-of-mod-of-expt-and-expt))))

(defthmd mod-of-floor-of-2-and-expt-of-one-less-alt
  (implies (and (natp n)
                (integerp j))
           (equal (mod (floor j 2) (expt 2 (+ -1 n)))
                  (floor (mod j (expt 2 n)) 2)))
  :hints (("Goal" :use (:instance mod-of-floor-of-2-and-expt-of-one-less)
           :in-theory (disable mod-of-floor-of-2-and-expt-of-one-less))))

(local
 (defthm not-equal-when-even-and-odd
   (implies (and (integerp (* 1/2 x))
                 (not (integerp (* 1/2 y))))
            (not (equal x y)))))

;move
(defthm floor-of-+-1-and-*-2-and-expt
  (implies (and (posp n)
                (integerp i))
           (equal (floor (+ 1 (* 2 i)) (expt 2 n))
                  (floor i (expt 2 (+ -1 n)))))
  :hints (("Goal"
           :in-theory (enable not-equal-when-even-and-odd))))
