; A lightweight book about mod and expt.
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
