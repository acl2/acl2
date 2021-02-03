; Axe rules about prime-fields
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions" :dir :system)
(include-book "kestrel/axe/known-booleans" :dir :system)

(acl2::def-constant-opener mul)
(acl2::def-constant-opener add)
(acl2::def-constant-opener fep)

;; only needed by axe
(defthmd pfield::integerp-of-add
  (integerp (add x y p)))

;; only needed by axe
(defthmd pfield::rationalp-of-add
  (rationalp (add x y p)))

;; only needed by axe
(defthmd pfield::integerp-of-sub
  (integerp (sub x y p)))

;; only needed by axe
(defthmd pfield::rationalp-of-sub
  (rationalp (sub x y p)))

;; only needed by axe
(defthmd pfield::integerp-of-neg
  (integerp (neg x p)))

;; only needed by axe
(defthmd pfield::rationalp-of-neg
  (rationalp (neg x p)))

;; only needed by axe
(defthmd pfield::integerp-of-mul
  (integerp (mul x y p)))

;; only needed by axe
(defthmd pfield::rationalp-of-mul
  (rationalp (mul x y p)))

;; only needed by axe
(defthmd pfield::integerp-of-pow
  (integerp (pow x n p)))

;; only needed by axe
(defthmd pfield::rationalp-of-pow
  (rationalp (pow x n p)))

;; only needed by axe
(defthmd pfield::integerp-of-inv
  (integerp (inv x p)))

;; only needed by axe
(defthmd pfield::rationalp-of-inv
  (rationalp (inv x p)))

;; only needed by axe
(defthmd pfield::integerp-of-div
  (integerp (div x y p)))

;; only needed by axe
(defthmd pfield::rationalp-of-div
  (rationalp (div x y p)))

;; only for use by Axe
(defthmd pfield::add-commutative-axe
  (implies (acl2::axe-syntaxp (acl2::should-commute-args-dag 'add x y acl2::dag-array))
           (equal (add x y p)
                  (add y x p)))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; only for use by Axe
(defthmd pfield::add-commutative-2-axe
  (implies (acl2::axe-syntaxp (acl2::should-commute-args-dag 'add x y acl2::dag-array))
           (equal (add x (add y z p) p)
                  (add y (add x z p) p)))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; only for use by Axe
(defthmd pfield::mul-commutative-axe
  (implies (acl2::axe-syntaxp (acl2::should-commute-args-dag 'mul x y acl2::dag-array))
           (equal (mul x y p)
                  (mul y x p)))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; only for use by Axe
(defthmd pfield::mul-commutative-2-axe
  (implies (acl2::axe-syntaxp (acl2::should-commute-args-dag 'mul x y acl2::dag-array))
           (equal (mul x (mul y z p) p)
                  (mul y (mul x z p) p)))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; only needed by Axe
(defthmd acl2::equal-self
  (equal (equal x x)
         t))

(acl2::add-known-boolean rtl::primep)
(acl2::add-known-boolean fep)
