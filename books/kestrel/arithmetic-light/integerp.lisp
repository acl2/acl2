; A lightweight book about the built-in function integerp.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthmd integerp-squeeze
  (implies (and (< 0 x)
                (< x 1))
           (not (integerp x))))

;; It's not clear where this material should go.

(defthm integerp-of-+-of--1/2
  (implies (rationalp x)
           (equal (integerp (+ -1/2 x))
                  (integerp (+ 1/2 x))))
  :hints (("Goal" :cases ((integerp (+ 1/2 x))))))

(local
 (defthm integerp-of--
  (equal (integerp (- x))
         (integerp (fix x)))
  :hints (("Goal" :cases ((integerp x))))))

(defthm integerp-of-+-of-1/2-and-*-of--1/2
  (implies (integerp x)
           (equal (integerp (+ 1/2 (- (* 1/2 x))))
                  (integerp (+ 1/2 (* 1/2 x)))))
  :hints (("Goal" :use (:instance integerp-of--
                                  (x (+ 1/2 (* 1/2 x))))
           :in-theory (disable integerp-of--))))

(defthm integerp-of-+-of---and--
  (equal (integerp (+ (- x) (- y)))
         (integerp (+ x y)))
  :hints (("Goal" :use (:instance integerp-of--
                                  (x (+ x y)))
           :in-theory (disable integerp-of--))))

(defthm integerp-of-+-of---and--
  (equal (integerp (+ (- x) (- y)))
         (integerp (+ x y)))
  :hints (("Goal" :use (:instance integerp-of-- (x (+ x y)))
           :in-theory (disable integerp-of--))))

(local (include-book "mod"))

;; two different ways of say an integer is odd
(defthm integerp-of-+-of-1/2-and-*-of-1/2
  (implies (integerp x)
           (equal (integerp (+ 1/2 (* 1/2 x)))
                  (not (integerp (* 1/2 x)))))
  :hints (("Goal" :use (:instance integerp-of-*-of-/-becomes-equal-of-0-and-mod
                                  (x (- x 1))
                                  (y 2)))))
