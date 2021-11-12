; A proof of the A.3.3.5 gadget
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
(include-book "a-3-3-5-spec")
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
(acl2::defconst-from-file *a-3-3-5-r1cs* "a-3-3-5-r1cs.txt" :package "R1CS")

;;;
;;; Lift the R1CS
;;;

(local
 (lift-zcash-r1cs *a-3-3-5-simp-lifted*
                  (r1cs::r1cs->vars *a-3-3-5-r1cs*)
                  (r1cs::r1cs->constraints *a-3-3-5-r1cs*)))

;undistribute
;; x + y*x becomes x * (1 + y)
(defthmd add-of-mul-same-arg1-arg2
  (implies (posp p)
           (equal (add x (mul y x p) p)
                  (mul x (add 1 y p) p)))
  :hints (("Goal" :in-theory (enable pfield::mul-of-add-arg1))))

;undistribute
;; x + x*y becomes x * (1 + y)
(defthmd add-of-mul-same-arg1-arg1
  (implies (posp p)
           (equal (add x (mul x y p) p)
                  (mul x (add 1 y p) p)))
  :hints (("Goal" :in-theory (enable pfield::mul-of-add-arg1))))

;undistribute
;; xy - x becomes x(y-1)
(defthmd add-of-mul-and-neg-same-arg1
  (implies (posp p)
           (equal (add (mul x y p) (neg x p) p)
                  (mul x (add y -1 p) p)))
  :hints (("Goal" :in-theory (enable PFIELD::MUL-OF-ADD-ARG2))))

;undistribute
;; -x + xy becomes x(y-1)
(defthmd add-of-neg-and-mul-same-arg1
  (implies (posp p)
           (equal (add (neg x p) (mul x y p) p)
                  (mul x (add y -1 p) p)))
  :hints (("Goal" :in-theory (enable PFIELD::MUL-OF-ADD-ARG2))))

(defthmd solve-for-u3
  (implies (and (rtl::primep p)
                (fep a p)
                (fep b p)
                (fep u3/num p))
           (equal (equal a (mul b u3/num p))
                  (if (equal b 0)
                      (equal a 0)
                    (equal u3/num (div a b p)))))
  :hints (("Goal" :in-theory (enable PFIELD::EQUAL-OF-DIV))))

;; x = y / z becomes x*z = y
(defthmd pfield::equal-of-div-alt-when-quotep
  (implies (and (syntaxp (quotep y))
                (fep z p)
                (fep y p)
                (rtl::primep p)
                (< 2 p))
           (equal (equal x (div y z p))
                  (if (equal 0 z)
                      (equal x 0)
                    (and (fep x p)
                         (equal (mul x z p)
                                (mod y p))))))
  :hints (("Goal" :in-theory (enable ; pfield::equal-of-div
                              ))))

(defthm product-not-equal-helper
  (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u2/num v2/num))
                (zcash::point-on-jubjub-p (ecurve::point-finite u1/num v1/num))
                (fep u1/num (zcash::jubjub-q))
                (fep v1/num (zcash::jubjub-q))
                (fep u2/num (zcash::jubjub-q))
                (fep v2/num (zcash::jubjub-q))
                )
           (not (equal 31456404414140643370629635736502576966887994532298953041431081581418232833640 ;-1/d
                       (mul (mul u2/num v1/num 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            (mul v2/num u1/num 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            52435875175126190479447740508185965837690552500527637822603658699938581184513))))
  :hints (("Goal" :use (zcash::not-pfield-squarep-of-jubjub-d
                        ZCASH::TWISTED-EDWARDS-CURVE-COMPLETEP-OF-JUBJUB-CURVE
                        (:instance ecurve::d.x1.x2.y1.y2-not-minus-one-on-curve-and-points
                                   (curve (zcash::jubjub-curve))
                                   (point1 (ecurve::point-finite u1/num v1/num))
                                   (point2 (ecurve::point-finite u2/num v2/num))))
           :in-theory (e/d (zcash::point-on-jubjub-p
                            zcash::jubjub-curve
                            (:e ecurve::twisted-edwards-curve-completep)
                            (:e zcash::jubjub-d)
                            (zcash::jubjub-q)
                            (zcash::jubjub-a))
                           (ZCASH::TWISTED-EDWARDS-CURVE-COMPLETEP-OF-JUBJUB-CURVE
                            ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB-D)))))

(defthm product-not-equal-helper-assoc-comm
  (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u2/num v2/num))
                (zcash::point-on-jubjub-p (ecurve::point-finite u1/num v1/num))
                (fep u1/num (zcash::jubjub-q))
                (fep v1/num (zcash::jubjub-q))
                (fep u2/num (zcash::jubjub-q))
                (fep v2/num (zcash::jubjub-q))
                )
           (not (equal 31456404414140643370629635736502576966887994532298953041431081581418232833640 ;-1/d
                       (mul v2/num
                            (mul u2/num
                                 (mul v1/num
                                      u1/num
                                      52435875175126190479447740508185965837690552500527637822603658699938581184513)
                                 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            52435875175126190479447740508185965837690552500527637822603658699938581184513))))
  :hints (("Goal" :use (:instance product-not-equal-helper))))

(defthm product-not-equal-helper-2
  (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u2/num v2/num))
                (zcash::point-on-jubjub-p (ecurve::point-finite u1/num v1/num))
                (fep u1/num (zcash::jubjub-q))
                (fep v1/num (zcash::jubjub-q))
                (fep u2/num (zcash::jubjub-q))
                (fep v2/num (zcash::jubjub-q))
                )
           (not (equal 20979470760985547108818104771683388870802557968228684781172577118520348350873 ;1/d
                       (mul (mul v2/num u1/num 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            (mul u2/num v1/num 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            52435875175126190479447740508185965837690552500527637822603658699938581184513))))
  :hints (("Goal" :use (zcash::not-pfield-squarep-of-jubjub-d
                        ZCASH::TWISTED-EDWARDS-CURVE-COMPLETEP-OF-JUBJUB-CURVE
                        (:instance ecurve::d.x1.x2.y1.y2-not-one-on-curve-and-points
                                   (curve (zcash::jubjub-curve))
                                   (point1 (ecurve::point-finite u1/num v1/num))
                                   (point2 (ecurve::point-finite u2/num v2/num))))
           :in-theory (e/d (zcash::point-on-jubjub-p
                            zcash::jubjub-curve
                            (:e ecurve::twisted-edwards-curve-completep)
                            (:e zcash::jubjub-d)
                            (zcash::jubjub-q)
                            (zcash::jubjub-a))
                           (ZCASH::TWISTED-EDWARDS-CURVE-COMPLETEP-OF-JUBJUB-CURVE
                            ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB-D)))))

(defthm product-not-equal-helper-2-associated
  (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u2/num v2/num))
                (zcash::point-on-jubjub-p (ecurve::point-finite u1/num v1/num))
                (fep u1/num (zcash::jubjub-q))
                (fep v1/num (zcash::jubjub-q))
                (fep u2/num (zcash::jubjub-q))
                (fep v2/num (zcash::jubjub-q))
                )
           (not (equal 20979470760985547108818104771683388870802557968228684781172577118520348350873 ;1/d
                       (mul v2/num
                            (mul u1/num
                                 (mul u2/num
                                      v1/num
                                      52435875175126190479447740508185965837690552500527637822603658699938581184513)
                                 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            52435875175126190479447740508185965837690552500527637822603658699938581184513))))
  :hints (("Goal" :use (:instance product-not-equal-helper-2))))

(defthm product-not-equal-helper-2-associated-commuted
  (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u2/num v2/num))
                (zcash::point-on-jubjub-p (ecurve::point-finite u1/num v1/num))
                (fep u1/num (zcash::jubjub-q))
                (fep v1/num (zcash::jubjub-q))
                (fep u2/num (zcash::jubjub-q))
                (fep v2/num (zcash::jubjub-q))
                )
           (not (equal 20979470760985547108818104771683388870802557968228684781172577118520348350873 ;1/d
                       (mul v2/num
                            (mul u2/num
                                 (mul v1/num
                                      u1/num
                                      52435875175126190479447740508185965837690552500527637822603658699938581184513)
                                 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                            52435875175126190479447740508185965837690552500527637822603658699938581184513))))
  :hints (("Goal" :use (:instance product-not-equal-helper-2))))

;; xy - x becomes x(y-1)
(defthmd add-of-mul-and-neg-same-arg1
  (implies (posp p)
           (equal (add (mul x y p) (neg x p) p)
                  (mul x (add y -1 p) p)))
  :hints (("Goal" :in-theory (enable PFIELD::MUL-OF-ADD-ARG2))))

;; -x + xy becomes x(y-1)
(defthmd add-of-neg-and-mul-same-arg1
  (implies (posp p)
           (equal (add (neg x p) (mul x y p) p)
                  (mul x (add y -1 p) p)))
  :hints (("Goal" :in-theory (enable PFIELD::MUL-OF-ADD-ARG2))))

(defthmd solve-for-v3
  (implies (and (fep a p)
                (fep b p)
                (fep c p)
                (fep v3/num p)
                (not (equal 0 c))
                (RTL::PRIMEP P))
           (equal (equal '0 (add a (add b (mul v3/num c p) p) p))
                  (equal v3/num (div (neg (add a b p) p) c p))))
  :hints (("Goal" :in-theory (enable PFIELD::EQUAL-OF-DIV-ALT))))

(acl2::add-known-boolean zcash::point-on-jubjub-p)

;; x + kxy becomes x(1+ky)
(defthmd collect-mults
  (implies (and (fep x p)
                (fep y p)
                (rtl::primep p))
           (equal (add x (mul k (mul x y p) p) p)
                  (mul x (add 1 (mul k y p) p) p))))

;; a = b / x becomes x = b / a
(defthmd solve-inverted ;gen
  (implies (and (fep x p)
                (fep a p)
                (fep b p)
                (rtl::primep p)
                (< 2 p)
                (not (equal a 0)))
           (equal (equal a (div b x p))
                  (if (equal x 0)
                      (equal a 0)
                    (equal x (div b a p))))))

(verify-zcash-r1cs
 *a-3-3-5-simp-lifted*
 (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u1/num v1/num))
               (zcash::point-on-jubjub-p (ecurve::point-finite u2/num v2/num))
               (not (equal x1/num x2/num)) ;todo: handle the other case?
               )
          (zcash::edwards-add-spec u1/num v1/num u2/num v2/num u3/num v3/num))
 ;; todo: global rules ignored if no rule-lists given
 :NO-SPLITP nil
 :monitor '( solve-for-v3)
 :tactic '(:rep (:seq (:rep :rewrite) :subst))
 :global-rules '(pfield::fep-of-sub
                 pfield::fep-of-add
                 pfield::fep-of-neg
                 pfield::fep-of-mul
                 pfield::fep-of-div
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
                 ecurve::twisted-edwards-add
;zcash::jubjub-edwards-curve
;zcash::jubjub-edwards-a
;zcash::jubjub-edwards-b
                 ;; ecurve::edwards-curve->p-of-edwards-curve
                 ;; ecurve::edwards-curve->a-of-edwards-curve
                 ;; ecurve::edwards-curve->b-of-edwards-curve
                 zcash::jubjub-curve
                 zcash::jubjub-q
                 zcash::jubjub-a
                 zcash::jubjub-d
                 primes::bls12-381-scalar-field-prime
                 ecurve::twisted-edwards-curve->p-of-twisted-edwards-curve
                 ecurve::point-finite->y-of-point-finite
                 ecurve::point-finite->x-of-point-finite
                 ecurve::equal-of-point-finite
                 ECURVE::TWISTED-EDWARDS-CURVE->A-OF-TWISTED-EDWARDS-CURVE
                 ECURVE::TWISTED-EDWARDS-CURVE->D-OF-TWISTED-EDWARDS-CURVE
                 ECURVE::TWISTED-EDWARDS-CURVE->P-OF-TWISTED-EDWARDS-CURVE
                 ecurve::pointp-of-point-finite-better
                 ecurve::point-kind-of-point-finite
                 eq
                 r1cs::natp-when-fe-listp-and-memberp
                 pfield::mul-of-1-arg1-gen
                 pfield::mod-when-fep
                 pfield::neg-of-neg-gen
                 ACL2::INTEGERP-WHEN-NATP-FOR-AXE
                 pfield::add-of-0-arg1
                 pfield::add-of-0-arg2
                 PFIELD::DIV-OF-0-ARG1
                 PFIELD::mul-OF-0-ARG1
                 PFIELD::mul-OF-0-ARG2
                 PFIELD::DIV-OF-1-ARG2
                 pfield::div-of-mul-same-arg1-arg1
                 pfield::div-of-mul-same-arg1-arg2
                 PFIELD::EQUAL-OF-ADD-CANCEL-1
                 ;;PFIELD::MUL-OF--1-BECOMES-NEG-alt
                 zcash::primep-of-jubjub-q-better
                 product-not-equal-helper-2-associated-commuted
                 product-not-equal-helper-assoc-comm
                 )
 :rule-lists '(( ;zcash::edwards-add-spec
                pfield::<-when-fep
                pfield::mul-of--1-becomes-neg-alt
                pfield::add-commutative-2-axe
                pfield::add-commutative-axe
;pfield::mul-of-add-arg1
;pfield::equal-of-div-alt
                pfield::equal-of-sub-combine-constants
                pfield::mod-of-add
                ;; pfield::mul-of-sub-arg1
                ;; pfield::mul-of-sub-arg2
                pfield::sub
;pfield::mul-of-add-arg2
                pfield::mul-of-1-arg1
                pfield::mul-of-1-arg2
                pfield::mul-of-neg-arg2
                pfield::equal-of-add-of-neg-simple
;equal-of-add-of-negative-constant
                pfield::mul-of-neg-arg1
                pfield::equal-of-mul-same-arg2
                acl2::if-of-t-and-nil-when-booleanp
                acl2::booleanp-of-equal
                ecurve::point-kind-of-if
                ecurve::pointp-of-if
                ecurve::point-kind-of-point-infinite
                ecurve::pointp-of-point-infinite-better
                acl2::equal-of-if-arg2
;ECURVE::POINT-ON-EDWARDS-P
;solve-for-lambda
                add-of-mul-same-arg1-arg1
                add-of-mul-same-arg1-arg2
;solve-for-u3
                )
               (solve-for-u3)
               ( ;pfield::equal-of-div-alt
                pfield::equal-of-div-alt-when-quotep
                zcash::edwards-add-spec
                pfield::mul-commutative-axe
                pfield::mul-of-add-arg2
                pfield::add-associative
                pfield::add-of-add-of-neg-same
;pfield::mul-associative
                product-not-equal-helper
                )
               (add-of-mul-and-neg-same-arg1
                add-of-neg-and-mul-same-arg1
                pfield::mul-of--1-becomes-neg-alt
                PFIELD::EQUAL-OF-ADD-OF-NEG-ARG2
                solve-for-v3
                PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS
                PFIELD::ADD-COMMUTATIVE-WHEN-CONSTANT
                r1cs::ADD-OF-CONSTANT-NORMALIZE-TO-FEP
                PFIELD::EQUAL-OF-MUL-CONSTANTS
                product-not-equal-helper-2-associated
                )
               (pfield::mul-associative
                pfield::div-of-neg-arg1-move-to-arg2
                ;
                )
               (pfield::neg-of-add
                pfield::mul-commutative-axe
                pfield::mul-commutative-2-axe
                collect-mults
                solve-inverted
                )
               ;; (solve-for-xprime)
               ;; (solve-for-yprime)
               ;; (zcash::edwards-add-spec
               ;;  ecurve::edwards-add
               ;;  sub
               ;;  pfield::add-associative
               ;;  pfield::add-commutative-axe
               ;;  pfield::add-commutative-2-axe
               ;;  pfield::neg-of-add
               ;;  pfield::equal-of-add-and-add-cancel
               ;;  pfield::mul-of-add-arg1
               ;;  pfield::mul-of-add-arg2
               ;;  pfield::mul-commutative-2-axe
               ;;  pfield::mul-commutative-axe
               ;;  pfield::mul-of-neg-arg1
               ;;  pfield::mul-of-neg-arg2)
               ))
