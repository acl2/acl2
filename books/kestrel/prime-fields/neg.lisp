; Prime fields library: Negation
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fep")
(include-book "kestrel/utilities/pos-fix" :dir :system)
(local (include-book "../arithmetic-light/mod"))

;; Compute the (unary) negation of x modulo the prime.
(defund neg (x p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p))))
  (mbe :exec (mod (- x) p)
       :logic (mod (- (ifix x)) (pos-fix p))))

(defthm natp-of-neg
  (natp (neg x p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep neg))))

(defthm neg-when-constant-arg1
  (implies (syntaxp (quotep x))
           (equal (neg x p)
                  ;; the negation here gets computed:
                  (mod (- (ifix x)) (pos-fix p))))
  :hints (("Goal" :in-theory (enable neg))))

(defthm fep-of-neg
  (implies (posp p)
           (fep (neg x p) p))
  :hints (("Goal" :in-theory (enable neg fep))))

(defthm neg-of-0
  (equal (neg 0 p)
         0)
  :hints (("Goal" :in-theory (enable neg))))

(defthm equal-of-neg-solve
  (implies (and (syntaxp (and (quotep k1)
                              ;; prevent loops when both are constants:
                              (not (quotep x))))
                (fep x p)
                (fep k1 p)
                (integerp p))
           (equal (equal k1 (neg x p))
                  (equal x (neg k1 p))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable neg))))

;; only needed for axe
(defthmd equal-of-neg-solve-alt
  (implies (and (syntaxp (and (quotep k1)
                              ;; prevent loops when both are constants:
                              (not (quotep x))))
                (fep x p)
                (fep k1 p)
                (integerp p))
           (equal (equal (neg x p) k1)
                  (equal x (neg k1 p))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable neg))))

(defthm equal-of-neg-and-one-less-than-prime
  (implies (and (fep x p)
                (< 1 p)
                (integerp p))
           (equal (equal (neg x p) (+ -1 p))
                  (equal x 1)))
  :hints (("Goal" :in-theory (enable neg))))

(defthm neg-of-neg
  (implies (and (fep x p)
                (integerp p))
           (equal (neg (neg x p) p)
                  x))
  :hints (("Goal" :in-theory (enable neg))))

(defthm neg-of-neg-gen
  (equal (neg (neg x p) p)
         (mod (ifix x) (pos-fix p)))
  :hints (("Goal" :in-theory (enable neg))))

(defthm mod-of-neg
  (equal (mod (neg x p) p)
         (neg x p))
  :hints (("Goal" :in-theory (enable neg acl2::mod-sum-cases))))

(defthm neg-when-not-integerp-cheap
  (implies (not (integerp x))
           (equal (neg x p)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable neg))))

(defthm neg-of-mod
  (equal (neg (mod x p) p)
         (neg x p))
  :hints (("Goal" :in-theory (enable neg))))

(defthm neg-when-not-posp-arg2-cheap
  (implies (not (posp p))
           (equal (neg x p)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable neg))))
