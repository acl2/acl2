; Prime fields library: Field element predicate
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/number-theory/primes" :dir :system)
(local (include-book "../arithmetic-light/mod"))

(in-theory (disable mod)) ;since some rules in this file introduce mod

;; Recognize an element of the field. "fep" = "field element predicate"
(defund fep (x p)
  (declare (xargs :guard (integerp p)))
  (and (natp x)
       (< x p)))

(defthm fep-fw-to-natp
  (implies (fep x p)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-fw-to-bound
  (implies (fep x p)
           (< x p))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fep))))

(defthmd <-when-fep
  (implies (fep x p)
           (< x p)))

;; 0 is in the field
(defthm fep-of-0
  (implies (posp p)
           (fep 0 p))
  :hints (("Goal" :in-theory (enable fep))))

;; 1 is in the field
(defthm fep-of-1
  (implies (and (integerp p)
                (< 1 p))
           (fep 1 p))
  :hints (("Goal" :in-theory (enable fep))))

;; For when X is constant but P is not.  P may often be a constrained function
;; (e.g., a large prime) about which we have a strong :linear rule.
(defthm fep-when-constant
  (implies (and (syntaxp (quotep x))
                (< x p))
           (equal (fep x p)
                  ;; Gets evaluated:
                  (natp x)))
  :hints (("Goal" :in-theory (enable fep))))

;; This breaks the abstraction a bit, but mod can appear when add, sub, or neg
;; is applied to constant arguments, or when we don't know that things are
;; field elements.
(defthm fep-of-mod
  (implies (and (integerp x)
                (posp p))
           (fep (mod x p) p))
  :hints (("Goal" :in-theory (enable fep))))

;; combines 2 steps, dropping the mod and dropping the ifix.
(defthmd mod-of-ifix-when-fep
  (implies (fep x p)
           (equal (mod (ifix x) p)
                  x))
  :hints (("Goal" :in-theory (enable fep))))

;; Keep disabled by default, even though the free var makes it pretty cheap
(defthmd rationalp-when-fep
  (implies (fep x p)
           (rationalp x)))
