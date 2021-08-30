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
                ;; (natp n)
                ;; (natp k)
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

;; Since the rules below target oddp.
(in-theory (disable oddp))

;; Disabled by default, but see oddp-when-primep-cheap below.
(defthmd oddp-when-primep
  (implies (rtl::primep n)
           (equal (oddp n)
                  (not (equal n 2))))
  :hints (("Goal" :in-theory (e/d (oddp) (not-primep-when-divides))
           :use (:instance not-primep-when-divides
                           (factor 2)))))

(defthm oddp-when-primep-cheap
  (implies (rtl::primep n)
           (equal (oddp n)
                  (not (equal n 2))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by oddp-when-primep)))

(defthmd evenp-when-primep
  (implies (rtl::primep n)
           (equal (evenp n)
                  (equal n 2)))
  :hints (("Goal" :use (:instance oddp-when-primep)
           :in-theory (e/d (oddp)
                           (oddp-when-primep-cheap)))))

(defthm evenp-when-primep-cheap
  (implies (rtl::primep n)
           (equal (evenp n)
                  (equal n 2)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (evenp-when-primep) (evenp)))))

;;todo: combine these 2 rules:

(defthm primep-forward-to-posp
  (implies (rtl::primep x)
           (posp x))
  :rule-classes :forward-chaining)

(defthm primep-forward-to-bound
  (implies (rtl::primep x)
           (<= 2 x))
  :rule-classes :forward-chaining)

(defthm primep-of-3
  (rtl::primep 3))
