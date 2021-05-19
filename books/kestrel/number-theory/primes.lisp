; Rules about primes
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primep-def")
(local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))

;; For now, we use the version of primep from the RTL library.

(defthm not-equal-of-least-divisor-same-when-divides
  (implies (and (integerp (/ n factor)) ; factor is a free var
                (natp n)
                (natp k)
                (natp factor)
                (<= k factor)
                (< factor n))
           (not (equal (rtl::least-divisor k n) n)))
  :hints (("Goal" :in-theory (enable rtl::least-divisor rtl::divides))))

(defthm not-primep-when-divides
  (implies (and (integerp (/ n factor)) ; factor is a free var
                (natp n)
                (natp factor)
                (<= 2 factor)
                (< factor n))
           (not (rtl::primep n)))
  :hints (("Goal" :use (:instance not-equal-of-least-divisor-same-when-divides
                                  (k 2))
           :in-theory (e/d (rtl::primep) (not-equal-of-least-divisor-same-when-divides)))))

(defthm oddp-when-primep-cheap
  (implies (rtl::primep n)
           (equal (oddp n)
                  (not (equal n 2))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (disable not-primep-when-divides)
           :use (:instance not-primep-when-divides
                           (factor 2)))))
