; A lightweight book about mod and expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; For mod-sum-cases, see the copyright on the RTL library.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "floor"))
(local (include-book "floor-and-expt"))
(local (include-book "mod"))
(local (include-book "expt2"))
(local (include-book "times"))
(local (include-book "times-and-divides"))

(defthmd mod-expt-split ;looped
  (implies (and (integerp x)
                (integerp n) ;new
                )
           (equal (mod x (expt 2 (+ -1 n)))
                  (* 1/2 (mod (* 2 x) (expt 2 n)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;           :cases ((integerp n))
           :in-theory (e/d (expt mod-cancel ;expt-of-+
                                 )
                           (expt-hack)))))

(defthmd mod-expt-split2
  (implies (and (integerp x)
                (integerp n))
           (equal (mod (* 2 x) (expt 2 n))
                  (* 2 (mod x (expt 2 (+ -1 n))))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;           :cases ((integerp n))
           :in-theory (e/d (expt mod-cancel expt-of-+
                                 )
                           (expt-hack)))))
(defthm mod-of-expt-twice
  (implies (and (natp i1)
                (natp i2))
           (equal (mod (mod x (expt 2 i1)) (expt 2 i2))
                  (mod x (expt 2 (min i1 i2)))))
  :hints (("Goal" :in-theory (e/d (mod-of-mod-when-mult)
                                  (mod-when-<))
           :use ((:instance mod-bound-linear-arg2
                            (x x)
                            (y (EXPT 2 I1))
                            )
                 (:instance mod-when-<
                           (x (mod x (expt 2 i1)))
                           (y (expt 2 i2))))
           :cases ((rationalp x)))))

(defthm mod-of-expt-and-expt
  (implies (and (natp i1)
                (natp i2))
           (equal (mod (expt 2 i1) (expt 2 i2))
                  (if (< i1 i2)
                      (expt 2 i1)
                    0)))
  :hints (("Goal" :in-theory (enable))))

;; Special case of mod-of-expt-twice
(defthm mod-of-mod-of-expt-and-2
  (implies (natp i)
           (equal (mod (mod x (expt 2 i)) 2)
                  (if (equal 0 i)
                      (mod x 1)
                  (mod x 2))))
  :hints (("Goal" :use (:instance mod-of-expt-twice (i1 i) (i2 1))
           :cases ((equal i 0))
           :in-theory (disable mod-of-expt-twice))))

;gen the (expt 2 n) to anything even?
(defthm integerp-of-half-of-mod-of-expt
  (implies (and (integerp i)
                (posp n))
           (equal (integerp (* 1/2 (mod i (expt 2 n))))
                  (integerp (* 1/2 i))))
  :hints (("Goal" :in-theory (enable integerp-of-*-of-/-becomes-equal-of-0-and-mod))))

(defthm mod-of-half-and-expt-of-one-less
  (implies (and (equal 0 (mod i (expt 2 n)))
                (integerp i)
                (integerp n))
           (equal (mod (* 1/2 i) (expt 2 (+ -1 n)))
                  0))
  :hints (("Goal" :in-theory (e/d (expt mod-cancel)
                                  (expt-hack)))))

(defthm mod-of-half-and-expt-of-one-less-alt
  (implies (and (equal 0 (mod i (expt 2 n)))
                (integerp i)
                (integerp n))
           (equal (mod (* 1/2 i) (* 1/2 (expt 2 n)))
                  0))
  :hints (("Goal" :in-theory (e/d (expt mod-cancel)
                                  (expt-hack)))))

(defthm integerp-of-half-when-mult-of-expt
  (implies (and (equal 0 (mod i (expt 2 n)))
                (integerp i)
                (posp n))
           (integerp (* 1/2 i)))
  :hints (("Goal"
           :use (:instance integerp-of-*
                           (x (* i (/ (expt 2 n))))
                           (y (expt 2 (+ -1 n))))
           :in-theory (e/d (equal-of-0-and-mod expt-of-+)
                           (integerp-of-*)))))

(defthm mod-of-expt-of-mod
  (implies (and (natp i)
                (integerp x)
                (integerp y))
           (equal (mod (expt (mod x y) i) y)
                  (mod (expt x i) y)))
  :hints (("Goal" :in-theory (enable expt mod-of-*-subst-arg1))))

(defthm mod-of-*-of-expt-of-mod
  (implies (and (natp i)
                (integerp x1)
                (integerp x2)
                (integerp y))
           (equal (mod (* x1 (expt (mod x2 y) i)) y)
                  (mod (* x1 (expt x2 i)) y)))
  :hints (("Goal" :in-theory (e/d (mod-of-*-subst-arg2) (mod-of-expt-of-mod))
           :use (:instance mod-of-expt-of-mod (x x2)))))

(local (include-book "../../arithmetic-3/floor-mod/floor-mod"))

(local
 (defthm mod-of-*-of-expt-and-expt-bound-helper
   (implies (and (< size size2)
                 (natp size)
                 (integerp size2)
                 (integerp i)
                 (<= 0 i) ;dropped below
                 )
            (<= (mod (* i (expt 2 size))
                     (expt 2 size2))
                (- (expt 2 size2)
                   (expt 2 size))))
   :hints (("Goal" :in-theory (enable mod my-floor-lower-bound-2)
            :use (:instance my-floor-lower-bound-2
                            (i i)
                            (j (expt 2 (+ (- size) size2))))))))

(defthm mod-of-*-of-expt-and-expt-bound
  (implies (and (< size size2)
                (natp size)
                (integerp size2)
                (integerp i))
           (<= (mod (* i (expt 2 size))
                    (expt 2 size2))
               (- (expt 2 size2)
                  (expt 2 size))))
  :hints (("Goal" :use (:instance mod-of-*-of-expt-and-expt-bound-helper
                                  (i (mod i (expt 2 size2))))
           :in-theory (disable mod-of-*-of-expt-and-expt-bound-helper))))
