; A proof of an alternate form of the gadget in A.3.3.1
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

;; STATUS: COMPLETE

;; This version of the file covers the Non-normative note on A.3.3.1 about combining the last 2 constraints.

(include-book "kestrel/utilities/defconst-from-file" :dir :system)
(include-book "a-3-3-1-spec")
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
(acl2::defconst-from-file *a-3-3-1-r1cs* "a-3-3-1-r1cs.txt" :package "ZCASH")

(defconst *a-3-3-1-alt-constraints*
  (append (acl2::butlast (r1cs::r1cs->constraints *a-3-3-1-r1cs*) 2) ; drop last 2 constraints
          ;; add back one new constraint:
          (list (r1cs::r1cs-constraint
                 ;; a vector: d_j*uu:
                 (list '(19257038036680949359750312669786877991949435402254120286184196891950884077233 POINT_INTERPRETATION/U^2/SQUARED_NUM))
                 ;; b vector: vv:
                 (list '(1 POINT_INTERPRETATION/V^2/SQUARED_NUM))
                 ;; c vector: a_j*uu+vv-1:
                 (list '(52435875175126190479447740508185965837690552500527637822603658699938581184512 POINT_INTERPRETATION/U^2/SQUARED_NUM)
                       '(1 POINT_INTERPRETATION/V^2/SQUARED_NUM)
                       '(-1 1))))))

(defconst *a-3-3-1-alt-r1cs*
  (r1cs::r1cs 52435875175126190479447740508185965837690552500527637822603658699938581184513
              (r1cs::r1cs->vars *a-3-3-1-r1cs*)
              *a-3-3-1-alt-constraints* ; not the usual constraints
              ))

;;;
;;; Lift the R1CS
;;;

(local
 (lift-zcash-r1cs *a-3-3-1-simp-lifted*
                  (r1cs::r1cs->vars *a-3-3-1-alt-r1cs*)
                  *a-3-3-1-alt-constraints* ; not the usual constraints
                  ))

;; (acl2::get-conjuncts-of-term2 (acl2::dag-to-term *A-3-3-1-SIMP-LIFTED*)))

(DEFTHM PFIELD::EQUAL-OF-ADD-OF-NEG-alt
  (IMPLIES
   (POSP PFIELD::P)
   (EQUAL (EQUAL (ADD PFIELD::Y (NEG PFIELD::Z PFIELD::P)
                      PFIELD::P)
                 PFIELD::X)
          (AND (FEP PFIELD::X PFIELD::P)
               (EQUAL (ADD PFIELD::X PFIELD::Z PFIELD::P)
                      (MOD (IFIX PFIELD::Y) PFIELD::P)))))
  :HINTS
  (("Goal" :IN-THEORY (ENABLE ADD NEG ACL2::MOD-SUM-CASES))))

(defthmd equal-of-add-of-neg-move
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (posp p))
           (equal (equal (add (neg x p) y p) z)
                  (equal y (add x z p)))))

(defthm move-add-helper
  (implies (and (fep x p)
                (fep y p)
                (fep z p)
                (fep w p)
                (posp p))
           (equal (EQUAL (ADD x (ADD y (NEG z p) p) p) w)
                  (equal (add x y p) (add w z p)))))

(defthm move-negative-1
  (implies (and (equal p 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                (fep x p)
                (fep y p))
           (equal (EQUAL (ADD 52435875175126190479447740508185965837690552500527637822603658699938581184512 x p) y)
                  (equal x (add 1 y p)))))

(defthm move-negative-1-alt
  (implies (and (equal p 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                (fep x p)
                (fep y p))
           (equal (EQUAL y (ADD 52435875175126190479447740508185965837690552500527637822603658699938581184512 x p))
                  (equal (add 1 y p) x))))

;; TODO: Can the proof be done by opening up less?
(verify-zcash-r1cs
 *a-3-3-1-simp-lifted*
 (zcash::affine-edwards-spec u/num v/num)
 ;; todo: global rules ignored if no rule-lists given
 :monitor '(pfield::ifix-when-fep)
 :global-rules '(pfield::fep-of-add
                 pfield::fep-of-mul
                 pfield::ifix-when-fep)
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
                pfield::add-commutative-2-axe ;todo: allow commuting negs forward?
                pfield::add-commutative-axe ;todo: allow commuting negs forward?
                ;; new rules for non-normative note proof (this file):
                PFIELD::EQUAL-OF-ADD-OF-NEG-alt
                pfield::ifix-when-fep
                PFIELD::MUL-WHEN-CONSTANT-BECOMES-NEG-OF-MUL
                ;PFIELD::ADD-OF-NEG-COMMUTE
                ;PFIELD::ADD-OF-NEG-COMMUTE-2
                equal-of-add-of-neg-move
                move-add-helper
                move-negative-1)))

;; ;; This allows us to extract the values for the intermediate vars:

;; (defstub answer (x) t)

;; (verify-zcash-r1cs
;;  *a-3-3-1-simp-lifted*
;;  (answer (acons 'POINT_INTERPRETATION/U^2/SQUARED_NUM POINT_INTERPRETATION/U^2/SQUARED_NUM
;;                 (acons 'POINT_INTERPRETATION/V^2/SQUARED_NUM POINT_INTERPRETATION/V^2/SQUARED_NUM
;;                        (acons 'POINT_INTERPRETATION/U^2_V^2/PRODUCT_NUM POINT_INTERPRETATION/U^2_V^2/PRODUCT_NUM
;;                               nil))))
;;  ;; todo: global rules ignored if no rule-lists given
;;  :rule-lists '((natp-when-fe-listp-and-memberp
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

(DEFTHM PFIELD::EQUAL-OF-ADD-OF-ADD-OF-NEG-ARG2-ARG2-alt
  (IMPLIES (POSP PFIELD::P)
           (EQUAL (EQUAL (ADD PFIELD::Y
                              (ADD W (NEG PFIELD::Z PFIELD::P)
                                   PFIELD::P)
                              PFIELD::P)
                         PFIELD::X)
                  (AND (EQUAL (ADD (NEG PFIELD::X PFIELD::P)
                                   (ADD PFIELD::Y W PFIELD::P)
                                   PFIELD::P)
                              (MOD (IFIX PFIELD::Z) PFIELD::P))
                       (FEP PFIELD::X PFIELD::P)))))

;; Backward Direction.  If u/num and v/num satisfy the spec, and are field
;; elements, then there is a valuation, namely the one given explictly below,
;; that gives the right values to u/num and v/num and that satisfies the entire
;; R1CS.
(acl2::prove-implication-with-r1cs-prover
 ;; Assumption:
 `(and (zcash::affine-edwards-spec u/num v/num)
       ,(pfield::gen-fe-listp-assumption '(u/num v/num)
                                         '(zcash::jubjub-q)))
 ;; Conclusion:
 '(r1cs::r1cs-holdsp *a-3-3-1-alt-r1cs*
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
 :monitor '(pfield::mul-of-1-arg1 pfield::fep-of-mul)
 :rule-lists '(((r1cs::R1CS-RULES)
                acl2::lookup-eq-becomes-lookup-equal
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
                ;; new rules for non-normative note proof (this file):
                PFIELD::EQUAL-OF-ADD-OF-NEG-alt
                pfield::ifix-when-fep
                PFIELD::MUL-WHEN-CONSTANT-BECOMES-NEG-OF-MUL
                ;PFIELD::ADD-OF-NEG-COMMUTE
                ;PFIELD::ADD-OF-NEG-COMMUTE-2
                equal-of-add-of-neg-move
                move-add-helper
                move-negative-1
                PFIELD::EQUAL-OF-ADD-OF-ADD-OF-NEG-ARG2-ARG2-alt
                move-negative-1-alt
                PFIELD::EQUAL-OF-ADD-OF-NEG
                PFIELD::MUL-ASSOCIATIVE)))
