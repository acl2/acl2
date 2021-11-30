; A proof of the A.3.3.3 gadget
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

;; STATUS: COMPLETE (forward direction)

(include-book "kestrel/utilities/defconst-from-file" :dir :system)
(include-book "a-3-3-3-spec")
(include-book "kestrel/zcash/jubjub" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/zcash/lift-zcash-r1cs" :dir :system)
(include-book "kestrel/zcash/verify-zcash-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules-axe" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
(include-book "kestrel/axe/r1cs/axe-rules-r1cs" :dir :system)
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "proof-support"))

;; Read in the r1cs:
(acl2::defconst-from-file *a-3-3-3-r1cs* "a-3-3-3-r1cs.txt" :package "ZCASH")

;;;
;;; Lift the R1CS
;;;

(local
 (lift-zcash-r1cs *a-3-3-3-simp-lifted*
                  (r1cs::r1cs->vars *a-3-3-3-r1cs*)
                  (r1cs::r1cs->constraints *a-3-3-3-r1cs*)))

(defthm equal-of-add-of-negative-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep p)))
                ;; todo: gen to any "negative" constant:
                (equal (mod k p)
                       (mod -1 p))
                (fep x p)
                (posp p))
           (equal (equal (add k x p) y)
                  (and (fep y p)
                       (equal x (add (neg k p) y p))))))

(defthm mul-of-+-arg2 ;why needed?
  (implies (and (integerp y)
                (integerp z))
           (equal (mul x (+ y z) p)
                  (mul x (add y z p) p)))
  :hints (("Goal" :in-theory (enable add acl2::pos-fix))))

;; x = 1 + v + x*v becomes x = (1 + v) / (1 - v)
(defthmd solve-for-x
  (implies (and (fep x p)
                (fep v p)
                (not (equal v 1))
                (rtl::primep p))
           (equal (equal x (add '1 (add v (mul x v p) p) p))
                  (equal x (div (add 1 v p)
                                (sub 1 v p)
                                p))))
  :hints (("Goal" :in-theory (enable pfield::equal-of-div))))

;; u + -(v * u) becomes u * (1 -v)
(defthmd add-of-neg-of-mul-same-undistribute
  (implies (posp p)
           (equal (add u (neg (mul v u p) p) p)
                  (mul u (add 1 (neg v p) p) p))))

(defthmd equal-of-mul-of-mul-of-inv-arg1-arg2
  (implies (and (fep x p)
                (fep y p)
                (fep w p)
                (fep z p)
                (not (equal w 0))
                (rtl::primep p))
           (equal (equal x (mul y (mul z (inv w p) p) p))
                  (equal (mul x w p) (mul y z p)))))

;; TODO: Can the proof be done by opening up less?
(verify-zcash-r1cs
 *a-3-3-3-simp-lifted*
 (implies (and (not (equal '1 v/num))
               (not (equal '0 u/num)))
          (edwards-montgomery-spec u/num v/num x/num y/num))
 :monitor '(equal-of-mul-of-mul-of-inv-arg1-arg2)
 :global-rules '(pfield::fep-of-sub
                 pfield::fep-of-add
                 pfield::fep-of-neg
                 pfield::fep-of-mul
                 pfield::fep-when-fe-listp-and-memberp
                 acl2::memberp-of-append-with-key-second-half-axe
                 acl2::memberp-of-append-with-key-first-half-axe
                 acl2::memberp-of-cons
                 acl2::equal-same
                 acl2::turn-equal-around-axe4
                 acl2::nfix-does-nothing
                 pfield::natp-of-div
                 pfield::natp-of-mul
                 pfield::equal-of-add-combine-constants
                 pfield::equal-of-neg-solve
                 pfield::equal-of-neg-solve-alt
                 pfield::equal-of-0-and-mul
                 acl2::pos-fix)
 :rule-lists '((edwards-montgomery-spec
                ecurve::twisted-edwards-point-to-montgomery-point
                ;; point-on-jubjub-p
                ;; ecurve::point-on-twisted-edwards-p
                jubjub-curve
                jubjub-q
                jubjub-a
                jubjub-d
                primes::bls12-381-scalar-field-prime
                ecurve::twisted-edwards-curve->p-of-twisted-edwards-curve
                ecurve::point-finite->y-of-point-finite
                ecurve::point-finite->x-of-point-finite
                ECURVE::EQUAL-OF-POINT-FINITE
                ;; ecurve::twisted-edwards-curve->a-of-twisted-edwards-curve
                ;; ecurve::twisted-edwards-curve->d-of-twisted-edwards-curve
                ecurve::pointp-of-point-finite-better
                ecurve::point-kind-of-point-finite
                eq
                r1cs::natp-when-fe-listp-and-memberp
                pfield::<-when-fep
                pfield::mul-of--1-becomes-neg-alt
                pfield::add-commutative-2-axe
                pfield::add-commutative-axe
                pfield::mul-of-add-arg1
                pfield::equal-of-div-alt
                pfield::equal-of-sub-combine-constants
                pfield::mod-of-add
                ;; pfield::mul-of-sub-arg1
                ;; pfield::mul-of-sub-arg2
                pfield::sub
                pfield::mul-of-add-arg2
                pfield::mul-of-1-arg1
                pfield::mul-of-1-arg2
                pfield::mul-of-neg-arg2
                pfield::equal-of-add-of-neg-simple
                equal-of-add-of-negative-constant
                pfield::mul-of-neg-arg1
                pfield::add-of-0-arg1
                pfield::add-of-0-arg2
                pfield::equal-of-mul-same-arg2
                acl2::if-of-t-and-nil-when-booleanp
                acl2::booleanp-of-equal)
               (solve-for-x ;loops with things in first rule set
                sub
                add-of-neg-of-mul-same-undistribute ;loops with things in first rule set
                )
               (div ;expose mul of inv
                equal-of-mul-of-mul-of-inv-arg1-arg2
                pfield::mul-associative)))
