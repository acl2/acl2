; A proof of the A.3.3.4 gadget
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
(include-book "a-3-3-4-spec")
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
(local (include-book "kestrel/utilities/if" :dir :system)) ; for equal-of-if-arg2
(local (include-book "proof-support"))

;; Read in the r1cs:
(acl2::defconst-from-file *a-3-3-4-r1cs* "a-3-3-4-r1cs.txt" :package "ZCASH")

;;;
;;; Lift the R1CS
;;;

(local
 (lift-zcash-r1cs *a-3-3-4-simp-lifted*
                  (r1cs::r1cs->vars *a-3-3-4-r1cs*)
                  (r1cs::r1cs->constraints *a-3-3-4-r1cs*)))

;; (acl2::get-conjuncts-of-term2 (acl2::dag-to-term *A-3-3-4-SIMP-LIFTED*)))

(defthm solve-for-xprime
  (implies (and (rtl::primep p)
                (FEP XPRIME/NUM P)
                (fep x2/num p)
                (fep x1/num p))
           (equal (equal (add '40962 (add xprime/num (add x2/num x1/num p) p) p) (mul lambda/num lambda/num p))
                  (equal xprime/num (add (mul lambda/num lambda/num p)
                                         (add (neg 40962 p)
                                              (add (neg x2/num p)
                                                   (neg x1/num p) p)
                                              p)
                                         p)))))


(defthm solve-for-lambda
  (implies (and (rtl::primep p)
                (fep x2/num p)
                (fep x1/num p)
                (fep lambda/num p)
                (FEP Y1/NUM P)
                (FEP Y2/NUM P)
                (not (equal x1/num x2/num)))
           (equal (equal y1/num (add y2/num (add (mul x1/num lambda/num p) (neg (mul x2/num lambda/num p) p) p) p))
                  (equal lambda/num (div (sub y2/num y1/num p)
                                         (sub x2/num x1/num p)
                                         p))))
  :hints (("Goal" :in-theory (e/d (pfield::equal-of-div-alt
                                   PFIELD::ADD-SAME
                                   ) (;pfield::equal-of-add-move-negations-bind-free ;looped!
                                      pfield::add-of-add-of-mul-same;looped
                                      )))))

(defthmd solve-for-yprime
  (implies (and (rtl::primep p)
                (fep yprime/num p)
                (fep b p)
                (fep a p))
           (equal (EQUAL (ADD yprime/num a p) b)
                  (equal yprime/num (sub b a p)))))

(verify-zcash-r1cs
 *a-3-3-4-simp-lifted*
 (implies (and ;; (ecurve::point-on-montgomery-p (ecurve::point-finite x1/num y1/num)
               ;;                                (zcash::jubjub-montgomery-curve))
               ;; (ecurve::point-on-montgomery-p (ecurve::point-finite x2/num y2/num)
               ;;                                (zcash::jubjub-montgomery-curve))
               (not (equal x1/num x2/num)) ;todo: handle the other case?
               )
          (zcash::montgomery-add-spec x1/num y1/num x2/num y2/num xprime/num yprime/num))
 :monitor '(add-associative)
 :tactic '(:seq (:rep :rewrite) :subst)
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
                 pfield::natp-of-add
                 pfield::natp-of-neg
                 pfield::natp-of-sub
                 pfield::integerp-of-mul
                 pfield::integerp-of-add
                 pfield::integerp-of-neg
                 pfield::equal-of-add-combine-constants
                 pfield::equal-of-neg-solve
                 pfield::equal-of-neg-solve-alt
                 pfield::equal-of-0-and-mul
                 acl2::pos-fix
                 acl2::ifix-when-integerp
                 ecurve::montgomery-add
                 zcash::jubjub-montgomery-curve
                 zcash::jubjub-montgomery-a
                 zcash::jubjub-montgomery-b
                 ecurve::montgomery-curve->p-of-montgomery-curve
                 ecurve::montgomery-curve->a-of-montgomery-curve
                 ecurve::montgomery-curve->b-of-montgomery-curve
                 zcash::jubjub-curve
                 zcash::jubjub-q
                 zcash::jubjub-a
                 zcash::jubjub-d
                 primes::bls12-381-scalar-field-prime
                 ecurve::twisted-edwards-curve->p-of-twisted-edwards-curve
                 ecurve::point-finite->y-of-point-finite
                 ecurve::point-finite->x-of-point-finite
                 ecurve::equal-of-point-finite
                 ;; ecurve::twisted-edwards-curve->a-of-twisted-edwards-curve
                 ;; ecurve::twisted-edwards-curve->d-of-twisted-edwards-curve
                 ecurve::pointp-of-point-finite-better
                 ecurve::point-kind-of-point-finite
                 eq
                 r1cs::natp-when-fe-listp-and-memberp
                 pfield::mul-of-1-arg1-gen
                 pfield::mod-when-fep
                 pfield::neg-of-neg-gen)
 :rule-lists '(( ;zcash::montgomery-add-spec
                pfield::<-when-fep
                pfield::mul-of--1-becomes-neg-alt
                pfield::add-commutative-2-axe
                pfield::add-commutative-axe
                pfield::mul-of-add-arg1
;pfield::equal-of-div-alt
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
;equal-of-add-of-negative-constant
                pfield::mul-of-neg-arg1
                pfield::add-of-0-arg1
                pfield::add-of-0-arg2
                pfield::equal-of-mul-same-arg2
                acl2::if-of-t-and-nil-when-booleanp
                acl2::booleanp-of-equal
                ecurve::point-kind-of-if
                ecurve::pointp-of-if
                ecurve::point-kind-of-point-infinite
                ecurve::pointp-of-point-infinite-better
                acl2::equal-of-if-arg2
;ECURVE::POINT-ON-MONTGOMERY-P
                solve-for-lambda
                )
               (solve-for-xprime)
               (solve-for-yprime)
               (zcash::montgomery-add-spec
                ecurve::montgomery-add
                sub
                pfield::add-associative
                pfield::add-commutative-axe
                pfield::add-commutative-2-axe
                pfield::neg-of-add
                pfield::equal-of-add-and-add-cancel
                pfield::mul-of-add-arg1
                pfield::mul-of-add-arg2
                pfield::mul-commutative-2-axe
                pfield::mul-commutative-axe
                pfield::mul-of-neg-arg1
                pfield::mul-of-neg-arg2)))
