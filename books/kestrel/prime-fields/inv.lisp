; Prime fields library: Multiplicative inverse
;
; Copyright (C) 2019-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "pow")
(include-book "minus1")
(include-book "fep-fix")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Compute the multiplicative inverse of x modulo the prime.
;; See theorem inv-correct below.
(defund inv (x p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (not (equal x 0)))
                  :guard-hints (("Goal" :in-theory (enable minus1)))))
  (if (equal 0 (fep-fix x p))
      ;; Special case (disallowed by the guard): inverse of 0 is 0, regardless
      ;; of p (otherwise, (inv 0 2) would be 1):
      0
    (pow x (+ -1 (minus1 p)) p)))

(defthm natp-of-inv
  (natp (inv x p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inv))))

(defthm fep-of-inv
  (implies (and (< 1 p)
                (integerp p))
           (fep (inv x p) p))
  :hints (("Goal" :in-theory (enable inv minus1))))

(defthm <-of-inv
  (implies (and (< 1 p) ;so that 1 is a fep
                (integerp p))
           (< (inv x p) p))
  :hints (("Goal" :use (:instance fep-of-inv)
           :in-theory (disable fep-of-inv))))

;; a bit odd, but we should not usually be calling inv on 0
(defthm inv-of-0
  (equal (inv 0 p)
         0)
  :hints (("Goal" :in-theory (enable inv))))

;was called inv-correct
(defthm mul-of-inv-arg2
  (implies (primep p)
           (equal (mul x (inv x p) p)
                  (if (equal 0 (fep-fix x p))
                      0
                    ;; usual case:
                    1)))
  :hints (("Goal" :in-theory (e/d (inv minus1) (pow-of-+ my-fermat-little))
           :expand (pow x (+ -1 p) p)
           :use (:instance my-fermat-little (a (mod (ifix x) p))))))

;; todo: consider enabling
(defthmd inv-of-mul
  (implies (and (integerp p)
                (< 1 p))
           (equal (inv (mul x y p) p)
                  (mul (inv x p) (inv y p) p)))
  :hints (("Goal" :in-theory (enable inv mul-of-pow-and-pow;pow-of-mul-arg1
                                     minus1
                                     ))))

(defthm inv-of-+-same-arg1
  (implies (integerp p)
           (equal (inv (+ p x) p)
                  (inv x p)))
  :hints (("Goal" :in-theory (enable inv minus1))))

(defthm inv-of-+-same-arg2
  (implies (integerp p)
           (equal (inv (+ x p) p)
                  (inv x p)))
  :hints (("Goal" :in-theory (enable inv))))

(defthm inv-of--1
  (implies (primep p)
           (equal (inv -1 p)
                  (+ -1 p)))
  :hints (("Goal" :in-theory (enable inv minus1 primep))))

(defthm not-equal-of-inv-and-0
  (implies (and (fep a p)
                (not (equal 0 a))
                (primep p))
           (not (equal 0 (inv a p))))
  :hints (("Goal" :use (:instance mul-of-inv-arg2
                                  (x (mod a p))
                                  (p p))
           :in-theory (e/d (fep inv)
                           (mul-of-inv-arg2)))))

(defthm mul-of-mul-of-inv
  (implies (and (fep a p)
                (fep x p)
                (primep p))
           (equal (mul a (mul (inv a p) x p) p)
                  (if (equal 0 a)
                      0
                    x)))
  :hints (("Goal" :use (:instance mul-associative (x a) (y (inv a p)) (z x))
           :in-theory (disable mul-associative
                               MUL-COMMUTATIVE
                               MUL-COMMUTATIVE-2))))

;; commutes the args to MUL in the lhs
(defthm mul-of-inv-arg1
  (implies (primep p)
           (equal (mul (inv x p) x p)
                  (if (equal 0 (mod (ifix x) p))
                      0
                    ;; usual case:
                    1)))
  :hints (("Goal" :use ((:instance mul-of-inv-arg2)
                        (:instance mul-commutative
                                   (x x)
                                   (y (inv x p))))
           :in-theory (disable mul-of-inv-arg2))))

;todo: swap mul args if one is the inv of the other... as a tiebreaker
(defthm mul-of-inv-mul-of-inv
  (implies (and (fep a p)
                (not (equal 0 a))
                (fep x p)
                (primep p))
           (equal (mul (inv a p) (mul a x p) p)
                  x))
  :hints (("Goal" :use (:instance mul-associative (y a) (x (inv a p)) (z x))
           :in-theory (disable mul-associative))))

;; Turns 1/a=b into 1=a*b.
(defthm equal-of-inv
  (implies (and (not (equal 0 a))
                (fep a p)
                (primep p))
           (equal (equal (inv a p) b)
                  (and (equal 1 (mul a b p))
                       (fep b p))))
  :hints (("Goal" :use (:instance mul-of-inv-mul-of-inv
                                  (a a)
                                  (x b)
                                  (p p))
           :in-theory (disable mul-of-inv-mul-of-inv))))

(defthm inv-of-inv
  (implies (and (fep a p)
                (primep p))
           (equal (inv (inv a p) p)
                  a))
  :hints (("Goal" :cases ((equal 0 a)))))
