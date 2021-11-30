; A proof of the gadget in A.3.3.1
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

;; STATUS: COMPLETE

(include-book "kestrel/utilities/defconst-from-file" :dir :system)
(include-book "a-3-3-1-spec")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/zcash/lift-zcash-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules-axe" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
(include-book "kestrel/axe/r1cs/axe-rules-r1cs" :dir :system)
(include-book "kestrel/zcash/verify-zcash-r1cs" :dir :system)
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "proof-support"))

;; Read in the r1cs:
(acl2::defconst-from-file *a-3-3-1-r1cs* "a-3-3-1-r1cs.txt" :package "ZCASH")

;;;
;;; Lift the R1CS
;;;

(local
 (lift-zcash-r1cs *a-3-3-1-lifted*
                  (r1cs::r1cs->vars *a-3-3-1-r1cs*)
                  (r1cs::r1cs->constraints *a-3-3-1-r1cs*)))

;; (acl2::get-conjuncts-of-term2 (acl2::dag-to-term *A-3-3-1-LIFTED*)))

;; Forward direction of the proof:
;; TODO: Can the proof be done by opening up less?
(verify-zcash-r1cs
 *a-3-3-1-lifted*
 (zcash::affine-edwards-spec u/num v/num)
 :rule-lists '((zcash::affine-edwards-spec
                zcash::point-on-jubjub-p
                ecurve::point-on-twisted-edwards-p
                zcash::jubjub-curve
                zcash::jubjub-q
                zcash::jubjub-a
                zcash::jubjub-d
                primes::bls12-381-scalar-field-prime
                ecurve::twisted-edwards-curve->p-of-twisted-edwards-curve
                ecurve::point-finite->y-of-point-finite
                ecurve::point-finite->x-of-point-finite
                ecurve::twisted-edwards-curve->a-of-twisted-edwards-curve
                ecurve::twisted-edwards-curve->d-of-twisted-edwards-curve
                ecurve::pointp-of-point-finite-better
                ecurve::point-kind-of-point-finite
                acl2::nfix-does-nothing
                eq
                r1cs::natp-when-fe-listp-and-memberp
                acl2::memberp-of-append-with-key-second-half-axe
                acl2::memberp-of-append-with-key-first-half-axe
                acl2::memberp-of-cons
                acl2::equal-same
                pfield::<-when-fep
                pfield::fep-when-fe-listp-and-memberp
                pfield::mul-of--1-becomes-neg-alt
                pfield::add-commutative-2-axe
                pfield::add-commutative-axe
                )))

;; ;; These commented out steps allow us to extract the expressions for the
;; ;; intermediate vars, to support the backward direction of the proof:

;; (defstub answer (x) t)

;; (verify-zcash-r1cs
;;  *a-3-3-1-lifted*
;;  (answer (acons 'POINT_INTERPRETATION/U^2/SQUARED_NUM POINT_INTERPRETATION/U^2/SQUARED_NUM
;;                 (acons 'POINT_INTERPRETATION/V^2/SQUARED_NUM POINT_INTERPRETATION/V^2/SQUARED_NUM
;;                        (acons 'POINT_INTERPRETATION/U^2_V^2/PRODUCT_NUM POINT_INTERPRETATION/U^2_V^2/PRODUCT_NUM
;;                               nil))))
;;  :rule-lists '((r1cs::natp-when-fe-listp-and-memberp
;;                 acl2::memberp-of-append-with-key-second-half-axe
;;                 acl2::memberp-of-append-with-key-first-half-axe
;;                 acl2::memberp-of-cons
;;                 acl2::equal-same
;;                 pfield::<-when-fep
;;                 pfield::fep-when-fe-listp-and-memberp
;;                 pfield::mul-of--1-becomes-neg-alt
;;                 pfield::add-commutative-2-axe
;;                 pfield::add-commutative-axe
;;                 )))

;; TODO: Have the prover generate this function (or something like this that uses DAGs) as it runs.
(defund a-3-3-1-valuation (u/num v/num)
  (acons 'u/num u/num
         (acons 'v/num v/num
                ;; this is the argument to the
                ;; answer literal in the failed
                ;; proof attempt just above,
                ;; except with '<p> replaced by
                ;; (zcash::jubjub-q):
                (ACONS 'POINT_INTERPRETATION/U^2/SQUARED_NUM
                       (MUL U/NUM U/NUM (zcash::jubjub-q))
                       (ACONS 'POINT_INTERPRETATION/V^2/SQUARED_NUM
                              (MUL V/NUM V/NUM (zcash::jubjub-q))
                              (ACONS 'POINT_INTERPRETATION/U^2_V^2/PRODUCT_NUM
                                     (MUL (MUL U/NUM U/NUM (zcash::jubjub-q))
                                          (MUL V/NUM V/NUM (zcash::jubjub-q))
                                          (zcash::jubjub-q))
                                     'NIL))))))

;; Backward Direction.  If u/num and v/num satisfy the spec, and are field
;; elements, then there is a valuation, namely the one given explictly below,
;; that gives the right values to u/num and v/num and that satisfies the entire
;; R1CS.
(acl2::prove-implication-with-r1cs-prover
 ;; Assumption:
 `(and (zcash::affine-edwards-spec u/num v/num)
       ;; This formulation is overkill here but is needed for efficient lookup if there are many vars:
       ,(pfield::gen-fe-listp-assumption '(u/num v/num)
                                         '(zcash::jubjub-q)))
 ;; Conclusion:
 '(r1cs::r1cs-holdsp *a-3-3-1-r1cs*
                     (a-3-3-1-valuation u/num v/num))
 :monitor '(pfield::mul-of-1-arg1 pfield::fep-of-mul)
 :rule-lists '((a-3-3-1-valuation
                (r1cs::R1CS-RULES)
                acl2::lookup-equal-of-acons-same
                acl2::lookup-equal-of-acons-diff
                pfield::add-of-0-arg1
                pfield::mul-of-1-arg1
                pfield::mul-of-1-arg2
                pfield::fep-of-mul
                pfield::fep-of-add
                ;; copied from the proof above:
                zcash::affine-edwards-spec
                zcash::point-on-jubjub-p
                ecurve::point-on-twisted-edwards-p
                zcash::jubjub-curve
                zcash::jubjub-q
                zcash::jubjub-a
                zcash::jubjub-d
                primes::bls12-381-scalar-field-prime
                ecurve::twisted-edwards-curve->p-of-twisted-edwards-curve
                ecurve::point-finite->y-of-point-finite
                ecurve::point-finite->x-of-point-finite
                ecurve::twisted-edwards-curve->a-of-twisted-edwards-curve
                ecurve::twisted-edwards-curve->d-of-twisted-edwards-curve
                ecurve::pointp-of-point-finite-better
                ecurve::point-kind-of-point-finite
                acl2::nfix-does-nothing
                eq
                r1cs::natp-when-fe-listp-and-memberp
                acl2::memberp-of-append-with-key-second-half-axe
                acl2::memberp-of-append-with-key-first-half-axe
                acl2::memberp-of-cons
                acl2::equal-same
                pfield::<-when-fep
                pfield::fep-when-fe-listp-and-memberp
                pfield::mul-of--1-becomes-neg-alt
                pfield::add-commutative-2-axe
                pfield::add-commutative-axe
                )))
