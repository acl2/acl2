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

(local (in-theory (disable floor mod)))

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
  :hints (("Goal" :use (:instance integerp-of-- (x (+ 1/2 (* 1/2 x))))
           :in-theory (disable integerp-of--))))

(defthm integerp-of-+-of---and--
  (equal (integerp (+ (- x) (- y)))
         (integerp (+ x y)))
  :hints (("Goal" :use (:instance integerp-of-- (x (+ x y)))
           :in-theory (disable integerp-of--))))

(encapsulate ()
  (local (include-book "times-and-divide"))
  (local (include-book "times"))
  (local (include-book "minus"))
  (local (include-book "plus"))
  (local (include-book "nonnegative-integer-quotient"))

  (defthm helper-0-aux
    (implies (and (equal 0 (mod x 2))
                  (rationalp x))
             (equal (/ x 2) (floor x 2)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable mod))))

  (defthm helper-0
    (implies (and (equal 0 (mod x 2))
                  (rationalp x))
             (integerp (/ x 2)))
    :hints (("Goal" :use helper-0-aux)))

  (defthm helper-1-aux
    (implies (and (equal 1 (mod x 2))
                  (rationalp x))
             (equal (/ (+ -1 x) 2) (floor x 2)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable mod))))

  (defthm helper-1-aux2
    (implies (and (equal 1 (mod x 2))
                  (rationalp x))
             (integerp (/ (+ -1 x) 2)))
    :hints (("Goal" :use helper-1-aux)))

  (defthm helper-1
    (implies (and (equal 1 (mod x 2))
                  (rationalp x))
             (integerp (/ (+ 1 x) 2)))
    :hints (("Goal" :use helper-1-aux2)))

  ;; (defthm nonnegative-integer-quotient-upper-bound
  ;;   (implies (and (natp i)
  ;;                 (natp j))
  ;;            (<= (nonnegative-integer-quotient i j)
  ;;                (/ i j))))

  ;; (defthm nonnegative-integer-quotient-of-1
  ;;   (implies (natp i)
  ;;            (equal (nonnegative-integer-quotient i 1)
  ;;                   i)))

  ;; (defthm <=-of-numerator
  ;;   (implies (and (<= 0 x)
  ;;                 (rationalp x))
  ;;            (<= 0 (numerator x))))

  (defthm numerator-when-denominator-is-1
    (implies (and (rationalp x)
                  (equal 1 (denominator x)))
             (equal (numerator x)
                    x))
    :hints (("Goal" :use rational-implies2
             :in-theory (disable rational-implies2))))

  (defthm mod-of-2-upper-bound
    (implies (integerp x)
             (< (mod x 2) 2))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable mod floor))))

  (defthm integerp-of-mod-of-2
    (implies (integerp x)
             (integerp (mod x 2)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable mod))))

  (defthm mod-of-2-lower-bound
    (implies (integerp x)
             (<= 0 (mod x 2)))
    :hints (("Goal" :in-theory (enable mod floor))))

  (defthm integerp-choice
    (implies (integerp x)
             (or (integerp (/ x 2))
                 (integerp (/ (+ 1 x) 2))))
    :rule-classes nil
    :hints (("Goal" :use (helper-0
                           helper-1
                           mod-of-2-lower-bound)
             :in-theory (disable helper-0
                                 helper-1
                                 mod
                                 mod-of-2-lower-bound)))))

;; two different ways to say an integer is odd
(defthm integerp-of-+-of-1/2-and-*-of-1/2
  (implies (integerp x)
           (equal (integerp (+ 1/2 (* 1/2 x)))
                  (not (integerp (* 1/2 x)))))
  :hints (("Goal" :use integerp-choice)))
