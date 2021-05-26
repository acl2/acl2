; Prime fields library: Exponentiation
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "mul")
(include-book "../../arithmetic-3/floor-mod/mod-expt-fast") ;just provides mod-expt-fast
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/expt"))

;; Compute x to the nth power (x^n) modulo the prime. Note that n can be any natural.
(defund pow (x n p)
  (declare (xargs :guard (and (integerp p)
                              (< 1 p)
                              (fep x p)
                              (natp n))
                  :verify-guards nil ;done below
                  ))
  (mbe :logic (if (or (not (mbt (natp n)))
                      (equal 0 n))
                  1
                (mul x (pow x (+ -1 n) p) p))
       :exec (mod-expt-fast x n p)))

(defthm natp-of-pow
  (natp (pow x n p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pow))))

(defthm fep-of-pow
  (implies (and ;(fep x p)
                (< 1 p) ;so that 1 is a fep
                (integerp p))
           (fep (pow x n p) p))
  :hints (("Goal" :in-theory (enable pow))))

(defthm <-of-pow
  (implies (and (< 1 p) ;so that 1 is a fep
                (integerp p))
           (< (pow x n p) p))
  :hints (("Goal" :use (:instance fep-of-pow)
           :in-theory (disable fep-of-pow))))

(defthm pow-of-+
  (implies (and (fep a p)
                (natp b)
                (natp c)
                (< 1 p)
                (integerp p))
           (equal (pow a (+ b c) p)
                  (mul (pow a b p)
                       (pow a c p)
                       p)))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-0-arg1
  (equal (pow 0 n p)
         (if (posp n)
             0
           1))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-0-arg2
  (equal (pow a 0 p)
         1)
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-1-arg1
  (implies (and (< 1 p)
                (integerp p))
           (equal (pow 1 n p)
                  1))
  :hints (("Goal" :in-theory (enable pow))))

(defthm pow-of-1-arg2
  (implies (and (fep a p)
                (integerp p))
           (equal (pow a 1 p)
                  a))
  :hints (("Goal" :in-theory (enable pow))))

;; express pow in terms of expt and do the entire mod at the end
(defthmd pow-rewrite
  (implies (and (integerp a)
                (natp b)
                (integerp p)
                (< 1 p))
           (equal (pow a b p)
                  (mod (expt a b) p)))
  :hints (("Goal" :in-theory (enable pow mul expt))))

(verify-guards pow :hints (("Goal" :expand (EXPT X N)
                            :in-theory (enable pow-rewrite mul))))

(defthmd pow-opener
  (implies (posp n)
           (equal (pow x n p)
                  (mul x
                       (pow x (+ -1 n) p)
                       p)))
  :hints (("Goal" :in-theory (enable pow))))
