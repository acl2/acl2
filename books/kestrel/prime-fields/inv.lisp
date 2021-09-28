; Prime fields library: Multiplicative inverse
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "pow")
(include-book "minus1")
(include-book "fep-fix")

;; Compute the multiplicative inverse of x modulo the prime.
;; See theorem inv-correct below.
(defund inv (x p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (not (equal x 0)))
                  :guard-hints (("Goal" :in-theory (enable minus1)))))
  (pow x (+ -1 (minus1 p)) p))

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

;was called inv-correct
(defthm mul-of-inv-arg2
  (implies (rtl::primep p)
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
  :hints (("Goal" :in-theory (enable inv pow-of-mul-arg1))))

(defthm inv-of-+-same-arg1
  (equal (inv (+ p x) p)
         (inv x p))
  :hints (("Goal" :in-theory (enable inv))))

(defthm inv-of-+-same-arg2
  (equal (inv (+ x p) p)
         (inv x p))
  :hints (("Goal" :in-theory (enable inv))))

(defthm inv-of--1
  (implies (rtl::primep p)
           (equal (inv -1 p)
                  (+ -1 p)))
  :hints (("Goal" :in-theory (enable inv minus1
                                     rtl::primep))))
