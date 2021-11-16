; A proof of the A.3.3.6 gadget
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

;; STATUS: COMPLETE (forward direction) but assumes twisted-edwards-add-associativity

(include-book "kestrel/utilities/defconst-from-file" :dir :system)
(include-book "a-3-3-6-spec")
(include-book "kestrel/zcash/jubjub" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/zcash/lift-zcash-r1cs" :dir :system)
(include-book "kestrel/zcash/verify-zcash-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules-axe" :dir :system)
(include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system)
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
(include-book "kestrel/axe/r1cs/axe-rules-r1cs" :dir :system)
(include-book "kestrel/number-theory/quadratic-residue" :dir :system) ; for has-square-root?
(include-book "kestrel/number-theory/tonelli-shanks" :dir :system)
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "proof-support"))
(local (include-book "kestrel/number-theory/tonelli-shanks-proof" :dir :system))
(local (include-book "kestrel/crypto/ecurve/prime-field-squares2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(defthm mod-of-*-arg2-same-extra
  (implies (and (posp y)
                (integerp k)
                (integerp x))
           (equal (mod (* k y x) y)
                  0)))

(defthm mod-of-*-arg2-same-extra-gen
  (implies (and (posp y)
                (rationalp k)
                (rationalp x))
           (equal (mod (* k y x) y)
                  (* y (mod (* k x) 1))))
  :hints (("Goal" :in-theory (enable acl2::mod-cancel))))

(defthm mod-of-+-of---of-*-arg2-same-extra
  (implies (and (rationalp y)
                (integerp x)
                (integerp k)
                (posp p))
           (equal (mod (+ (- (* k p x)) y) p)
                  (mod y p)))
  :hints (("Goal" :in-theory (enable acl2::mod-of-+-when-multiple-arg1)))
  )

;slow?
(defthm mod-of---of-*-of-mod-same
  (implies (and (integerp y) ;gen
                (integerp x)
                (integerp k)
                (posp p))
           (equal (mod (- (* x (mod y p))) p)
                  (mod (- (* x y)) p))))

(local (in-theory (disable PRIMES::TONELLI-SHANKS-SQRT-AUX)))

(defthm mod-of-*-of-tonelli-shanks-sqrt-aux-and-tonelli-shanks-sqrt-aux
  (implies (and (not (primes::has-square-root? z p))
                (< n p)
                (< z p)
                (natp n)
                (natp z)
                (rtl::primep p)
                (< 2 p))
           (equal (mod (* (primes::tonelli-shanks-sqrt-aux n p z)
                          (primes::tonelli-shanks-sqrt-aux n p z))
                       p)
                  (if (primes::has-square-root? n p)
                      n
                    0 ;odd case, since tonelli-shanks-sqrt-aux returns 0
                    )))
  :hints (("Goal" :use (:instance primes::tonelli-shanks-sqrt-aux-is-sqrt-modp
                                  (n n)
                                  (z z)
                                  (p p)
                                  (y (primes::tonelli-shanks-sqrt-aux n p z)))
           :in-theory (e/d ()
                           (primes::tonelli-shanks-sqrt-aux-is-sqrt-modp)))))

(defthm mod-of-*-of-tonelli-shanks-sqrt-and-tonelli-shanks-sqrt
  (implies (and (not (primes::has-square-root? z p))
                (< n p)
                (< z p)
                (natp n)
                (natp z)
                (rtl::primep p)
                (< 2 p))
           (equal (mod (* (primes::tonelli-shanks-sqrt n p z)
                          (primes::tonelli-shanks-sqrt n p z))
                       p)
                  (if (primes::has-square-root? n p)
                      n
                    0 ;odd case, since tonelli-shanks-sqrt returns 0
                    )))
  :hints (("Goal" :use (:instance primes::tonelli-shanks-is-sqrt-modp
                                  (n n)
                                  (z z)
                                  (p p)
                                  (y (primes::tonelli-shanks-sqrt n p z)))
           :in-theory (e/d (primes::tonelli-shanks-sqrt)
                           (primes::tonelli-shanks-is-sqrt-modp)))))

(defthm mod-of-*-of-tonelli-shanks-lesser-sqrt-and-tonelli-shanks-lesser-sqrt
  (implies (and (< n p)
                (< z p)
                (natp n)
                (natp z)
                (not (primes::has-square-root? z p))
                (rtl::primep p)
                (< 2 p))
           (equal (mod (* (primes::tonelli-shanks-lesser-sqrt n p z)
                          (primes::tonelli-shanks-lesser-sqrt n p z))
                       p)
                  (if (primes::has-square-root? n p)
                      n
                    0 ;odd case, since tonelli-shanks-lesser-sqrt returns 0
                    )))
  :hints (("Goal" :use (:instance mod-of-*-of-tonelli-shanks-sqrt-and-tonelli-shanks-sqrt)
           :in-theory (e/d (primes::tonelli-shanks-sqrt)
                           (mod-of-*-of-tonelli-shanks-sqrt-and-tonelli-shanks-sqrt)))))

(defthm mod-of-*-of-tonelli-shanks-greater-sqrt-and-tonelli-shanks-greater-sqrt
  (implies (and (< n p)
                (< z p)
                (natp n)
                (natp z)
                (not (primes::has-square-root? z p))
                (primes::has-square-root? n p)
                (rtl::primep p)
                (< 2 p))
           (equal (mod (* (primes::tonelli-shanks-greater-sqrt n p z)
                          (primes::tonelli-shanks-greater-sqrt n p z))
                       p)
                  (if (primes::has-square-root? n p)
                      n
                    0 ;odd case
                    )))
  :hints (("Goal" :in-theory (e/d (primes::tonelli-shanks-greater-sqrt)
                                  (ACL2::MOD-OF-MINUS-ARG1)))))

(defthm equal-of-mul-same-using-tonelli-shanks-fw
  (implies (and (fep k p)
                (fep x p)
                (fep z p)
                (not (primes::has-square-root? z p)) ; just need any z that's not a square
;               (natp primes::z)
                (rtl::primep p)
                (< 2 p)
                )
           (implies (equal k (mul x x p))
                    (or (equal x (primes::tonelli-shanks-lesser-sqrt k p z))
                        (equal x (primes::tonelli-shanks-greater-sqrt k p z)))))
  :hints (("Goal" :in-theory (e/d (primes::tonelli-shanks-greater-sqrt
                                   primes::tonelli-shanks-lesser-sqrt
                                   mul
                                   )
                                  (primes::tonelli-shanks-sqrt-aux-is-correct))
           :use (:instance primes::tonelli-shanks-sqrt-aux-is-correct
                           (n k)
                           (y x)
                           (p p)
                           (z z)))))

(defthm equal-of-mul-same-using-tonelli-shanks-bk
  (implies (and (primes::has-square-root? k p)
                (fep k p)
                (fep x p)
                (fep z p)
                (not (primes::has-square-root? z p)) ; just need any z that's not a square
;               (natp primes::z)
                (rtl::primep p)
                (< 2 p)
                )
           (implies (or (equal x (primes::tonelli-shanks-lesser-sqrt k p z))
                        (equal x (primes::tonelli-shanks-greater-sqrt k p z)))
                    (equal k (mul x x p))))
  :hints (("Goal" :in-theory (enable mul)))
  :rule-classes nil)

(defthm PRIMES::TONELLI-SHANKS-SQRT-AUX-when-not-HAS-SQUARE-ROOT?-cheap
  (implies (NOT (PRIMES::HAS-SQUARE-ROOT? K P))
           (equal (PRIMES::TONELLI-SHANKS-SQRT-AUX K P Z)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable PRIMES::TONELLI-SHANKS-SQRT-AUX))))

(defthm PRIMES::TONELLI-SHANKS-lesser-SQRT-when-not-HAS-SQUARE-ROOT?-cheap
 (implies (NOT (PRIMES::HAS-SQUARE-ROOT? K P))
          (equal (PRIMES::TONELLI-SHANKS-LESSER-SQRT K P Z)
                 0))
 :rule-classes ((:rewrite :backchain-limit-lst (0)))
 :hints (("Goal" :in-theory (enable PRIMES::TONELLI-SHANKS-LESSER-SQRT))))

(defthm PRIMES::TONELLI-SHANKS-greater-SQRT-when-not-HAS-SQUARE-ROOT?-cheap
  (implies (NOT (PRIMES::HAS-SQUARE-ROOT? K P))
           (equal (PRIMES::TONELLI-SHANKS-GREATER-SQRT K P Z)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable PRIMES::TONELLI-SHANKS-GREATER-SQRT))))

(defthmd equal-of-mul-same-using-tonelli-shanks
  (implies (and (fep k p)
                (fep x p)
                (fep z p)
                (not (primes::has-square-root? z p)) ; just need any z that's not a square
                (rtl::primep p)
                (< 2 p))
           (equal (equal k (mul x x p))
                  (if (primes::has-square-root? k p)
                      (or (equal x (primes::tonelli-shanks-lesser-sqrt k p z))
                          (equal x (primes::tonelli-shanks-greater-sqrt k p z)))
                    nil)))
  :hints (("Goal" :use (equal-of-mul-same-using-tonelli-shanks-fw
                        equal-of-mul-same-using-tonelli-shanks-bk))))

;; This can cause a proof to split into cases
(defthmd equal-of-mul-same-using-tonelli-shanks-when-constant
  (implies (and (syntaxp (quotep k))
                (fep k p)
                (fep x p)
                (fep z p)
                (not (primes::has-square-root? z p)) ; just need any z that's not a square
                (rtl::primep p)
                (< 2 p))
           (equal (equal k (mul x x p))
                  (if (primes::has-square-root? k p)
                      (or (equal x (primes::tonelli-shanks-lesser-sqrt k p z))
                          (equal x (primes::tonelli-shanks-greater-sqrt k p z)))
                    nil)))
  :hints (("Goal" :use (equal-of-mul-same-using-tonelli-shanks-fw
                        equal-of-mul-same-using-tonelli-shanks-bk))))

(defthmd equal-of-mul-same-using-tonelli-shanks-when-constant-special
  (implies (and (syntaxp (quotep k))
                (fep k (zcash::jubjub-q))
                (fep x (zcash::jubjub-q)))
           (equal (equal k (mul x x 52435875175126190479447740508185965837690552500527637822603658699938581184513))
                  (if (primes::has-square-root? k (zcash::jubjub-q))
                      (or (equal x (primes::tonelli-shanks-lesser-sqrt k (zcash::jubjub-q) 5))
                          (equal x (primes::tonelli-shanks-greater-sqrt k (zcash::jubjub-q) 5)))
                    nil)))
  :hints (("Goal" :use (:instance equal-of-mul-same-using-tonelli-shanks
                                  (z 5)
                                  (p (zcash::jubjub-q)))
           :in-theory (enable (ZCASH::JUBJUB-Q)))))

;; Read in the r1cs:
(acl2::defconst-from-file *a-3-3-6-r1cs* "a-3-3-6-r1cs.txt" :package "ZCASH")

;;;
;;; Lift the R1CS
;;;

;;(set-guard-checking nil) ;todo

;; TODO: Invalid r1cs?
(local
 (r1cs::lift-r1cs *a-3-3-6-simp-lifted*
                      (r1cs::r1cs->vars *a-3-3-6-r1cs*)
                      (r1cs::r1cs->constraints *a-3-3-6-r1cs*)
                      52435875175126190479447740508185965837690552500527637822603658699938581184513
                      ;; :extra-rules '(primep-of-baby-jubjub-prime-constant)
                      ;; todo: remove these as default rules
                      ;; :remove-rules '(pfield::add-commutative-axe
                      ;;                 pfield::add-commutative-2-axe)
                      ;; :rules nil
                      ))

;gen?
(defthm solve-1
  (implies (and (acl2::axe-syntaxp (acl2::is-the-variablep 'first_doubling/u3/num var dag-array))
                (fep x p)
                (fep y p)
                (fep var p)
                (rtl::primep p))
           (equal (equal x (mul y var p))
                  (if (equal y 0)
                      (equal x 0)
                    (equal var (div x y p))))))

;todo: a way to specialize a rule for a var
(defthm solve-2
  (implies (and (acl2::axe-syntaxp (acl2::is-the-variablep 'SECOND_DOUBLING/U3/NUM var dag-array))
                (fep x p)
                (fep y p)
                (fep var p)
                (rtl::primep p))
           (equal (equal x (mul y var p))
                  (if (equal y 0)
                      (equal x 0)
                    (equal var (div x y p))))))

(defthm solve-3
  (implies (and (acl2::axe-syntaxp (acl2::is-the-variablep 'THIRD_DOUBLING/U3/NUM var dag-array))
                (fep x p)
                (fep y p)
                (fep var p)
                (rtl::primep p))
           (equal (equal x (mul y var p))
                  (if (equal y 0)
                      (equal x 0)
                    (equal var (div x y p))))))

(defthm equal-of-0-and-add-same
 (implies (and (fep x p)
               (rtl::primep p)
               (< 2 p))
          (equal (equal 0 (add x x p))
                 (equal 0 x)))
 :hints (("Goal" :in-theory (enable pfield::add-same))))

(defthm solve-4
  (implies (and (acl2::axe-syntaxp (acl2::is-the-variablep 'first_DOUBLING/V3/NUM var dag-array))
                (fep x p)
                (fep y p)
                (fep z p)
                (fep w p)
                (fep var p)
                (rtl::primep p))
           (equal (EQUAL x (ADD y (ADD z (MUL w var p) p) p))
                  (if (equal 0 w)
                      (equal x (ADD y z p))
                    (equal var
                           (div (add x
                                     (add (neg y p)
                                          (neg z p) p)
                                     p)
                                w
                                p))))))

(defthm solve-5
  (implies (and (acl2::axe-syntaxp (acl2::is-the-variablep 'second_DOUBLING/V3/NUM var dag-array))
                (fep x p)
                (fep y p)
                (fep z p)
                (fep w p)
                (fep var p)
                (rtl::primep p))
           (equal (EQUAL x (ADD y (ADD z (MUL w var p) p) p))
                  (if (equal 0 w)
                      (equal x (ADD y z p))
                    (equal var
                           (div (add x
                                     (add (neg y p)
                                          (neg z p) p)
                                     p)
                                w
                                p))))))

(defthm solve-6
  (implies (and (acl2::axe-syntaxp (acl2::is-the-variablep 'THIRD_DOUBLING/V3/NUM var dag-array))
                (fep x p)
                (fep y p)
                (fep z p)
                (fep w p)
                (fep var p)
                (rtl::primep p))
           (equal (EQUAL x (ADD y (ADD z (MUL w var p) p) p))
                  (if (equal 0 w)
                      (equal x (ADD y z p))
                    (equal var
                           (div (add x
                                     (add (neg y p)
                                          (neg z p) p)
                                     p)
                                w
                                p))))))

(acl2::add-known-boolean zcash::point-on-jubjub-p)

(acl2::def-constant-opener PRIMES::HAS-SQUARE-ROOT?)

(acl2::def-constant-opener ECURVE::POINT-FINITE)
(acl2::def-constant-opener ECURVE::POINT-kind)
(acl2::def-constant-opener ECURVE::POINTp)
(acl2::def-constant-opener ECURVE::POINT-finite->x)
(acl2::def-constant-opener ECURVE::POINT-finite->y)
(acl2::def-constant-opener ECURVE::POINT-fix)

;; first coordinate of the doubling of point (u,v)
(defun double-u-coord (u v p)
  (DIV (ADD (MUL U V p)
            (MUL U V p)
            p)
       (ADD '1
            (MUL 19257038036680949359750312669786877991949435402254120286184196891950884077233 ;<d>
                 (MUL (MUL U V p) ;normalize?
                      (MUL U V p)
                      p)
                 p)
            p)
       p))

(defthm intro-double-u-coord
  (equal (DIV (ADD (MUL U V p)
                   (MUL U V p)
                   p)
              (ADD '1
                   (MUL 19257038036680949359750312669786877991949435402254120286184196891950884077233 ;<d>
                        (MUL (MUL U V p)
                             (MUL U V p)
                             p)
                        p)
                   p)
              p)
         (double-u-coord u v p)))

(defthm double-u-coord-of-0-arg1
  (equal (double-u-coord 0 v p)
         0))

(defthm equal-of-0-and-double-u-coord
  (implies (and (fep u p)
                (fep v p)
                (rtl::primep p)
                (< 2 p))
           (equal (equal 0 (double-u-coord u v p))
                  (or ; unusual (impossible because -1/d is not a square?):
                   (equal 0
                          (ADD '1
                               (MUL 19257038036680949359750312669786877991949435402254120286184196891950884077233 ;<d>
                                    (MUL (MUL U V p)
                                         (MUL U V p)
                                         p)
                                    p)
                               p))
                   (equal 0 (mul u v p)))))
  :hints (("Goal" :in-theory (enable pfield::equal-of-0-and-div))))

;move!
(DEFTHM ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB--1/D
  (NOT (ECURVE::PFIELD-SQUAREP (neg (inv (ZCASH::JUBJUB-D)
                                         (ZCASH::JUBJUB-Q))
                                    (ZCASH::JUBJUB-Q))
                               (ZCASH::JUBJUB-Q)))
  :hints (("Goal" :in-theory (enable ECURVE::PFIELD-SQUAREP<->HAS-SQUARE-ROOT?
                                     ZCASH::JUBJUB-D
                                     ZCASH::JUBJUB-Q))))



(DEFTHM ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB--1/D-alt
  (NOT (ECURVE::PFIELD-SQUAREP 31456404414140643370629635736502576966887994532298953041431081581418232833640 ; -1/d
                               52435875175126190479447740508185965837690552500527637822603658699938581184513))
  :hints (("Goal" :in-theory (enable ECURVE::PFIELD-SQUAREP<->HAS-SQUARE-ROOT?
                                     ZCASH::JUBJUB-D
                                     ZCASH::JUBJUB-Q))))

(DEFTHM ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB-1/D-alt
  (NOT (ECURVE::PFIELD-SQUAREP 20979470760985547108818104771683388870802557968228684781172577118520348350873 ; 1/d
                               52435875175126190479447740508185965837690552500527637822603658699938581184513))
  :hints (("Goal" :in-theory (enable ECURVE::PFIELD-SQUAREP<->HAS-SQUARE-ROOT?
                                     ZCASH::JUBJUB-D
                                     ZCASH::JUBJUB-Q))))


(defthm equal-of-0-and-double-u-coord-better
  (implies (and (equal p (ZCASH::JUBJUB-q))
                (fep u p)
                (fep v p)
                (rtl::primep p)
                (< 2 p))
           (equal (equal 0 (double-u-coord u v p))
                  (equal 0 (mul u v p))))
  :hints (("Goal" :use ((:instance equal-of-0-and-double-u-coord)
                        (:instance ECURVE::PFIELD-SQUAREP-SUFF
                                   (x (neg (inv (ZCASH::JUBJUB-D)
                                                (ZCASH::JUBJUB-Q))
                                           (ZCASH::JUBJUB-Q)))
                                   (r (MUL U V (ZCASH::JUBJUB-Q)))
                                   (p (ZCASH::JUBJUB-Q))))
           :in-theory (e/d ((ZCASH::JUBJUB-D)
                            (ZCASH::JUBJUB-Q))
                           (equal-of-0-and-double-u-coord)))))


(defun double-v-coord (u v p)
  (DIV (ADD (MUL v v p)
            (MUL U u p)
            p)
       (ADD '1
            (neg (MUL 19257038036680949359750312669786877991949435402254120286184196891950884077233 ;<d>
                      (MUL (MUL U V p) ;normalize?
                           (MUL U V p)
                           p)
                      p)
                 p)
            p)
       p))

(defthm div-of-neg-and-neg
  (implies (RTL::PRIMEP P)
           (EQUAL (DIV (NEG Y1 P) (NEG Y2 P) P)
                  (DIV Y1 Y2 P)))
  :hints (("Goal" :in-theory (enable div))))


(defthmd equal-of-div-and-div-when-negs-equal
  (implies (and (equal x1 (neg y1 p))
                (equal x2 (neg y2 p))
                (FEP Y1 P)
                (RTL::PRIMEP P))
           (equal (equal (div x1 x2 p) (div y1 y2 p))
                  t)))

(defthm intro-double-v-coord
  (implies (and (fep u p)
                (fep v p)
                (equal p 52435875175126190479447740508185965837690552500527637822603658699938581184513) ;gen?
;(rtl::primep p)
;(< 2 p)
                )
           (equal (DIV (ADD (MUL U V p)
                            (ADD (NEG (MUL (ADD V U p)
                                           (ADD V U p)
                                           p)
                                      p)
                                 (MUL U V p)
                                 p)
                            p)
                       (ADD 52435875175126190479447740508185965837690552500527637822603658699938581184512 ;p-1
                            (MUL 19257038036680949359750312669786877991949435402254120286184196891950884077233 ;d
                                 (MUL (MUL U V p)
                                      (MUL U V p)
                                      p)
                                 p)
                            p)
                       p)
                  (double-v-coord u v p)))
  :hints (("Goal" :in-theory (enable equal-of-div-and-div-when-negs-equal))))

(defthm equal-of-add-of-neg-same
  (implies (and (fep x p)
                (fep y p)
                (rtl::primep p))
           (equal (equal x (add y (neg x p) p))
                  (equal (mul 2 x p) y)))
  :hints (("Goal" :in-theory (enable pfield::mul-of-2))))

(theory-invariant (incompatible (:rewrite PFIELD::ADD-OF-ADD-SAME) (:rewrite pfield::mul-of-2)))

;; ;; since 1/d is not a square
;; ;;gen?
;; (thm
;;  (implies (and (fep u p)
;;                (fep v p)
;;                (rtl::primep p)
;;                (ECURVE::POINT-ON-TWISTED-EDWARDS-P (ecurve::point-finite u v) (ZCASH::JUBJUB-CURVE))
;;                (equal p (ZCASH::JUBJUB-q))
;;                )
;;           (not (equal (mul u v p)
;;                       (add (mul (add v u p)
;;                                 (add v u p)
;;                                 p)
;;                            (neg (mul u v p) p)
;;                            p))))
;;  :hints (("Goal" :in-theory (e/d ( ecurve::point-on-twisted-edwards-p
;;                                    pfield::mul-of-2
;;                                    ZCASH::JUBJUB-CURVE
;;                                    ZCASH::JUBJUB-A
;;                                   )
;;                                  (;PFIELD::MUL-OF-ADD-ARG1
;;   ;PFIELD::MUL-OF-ADD-ARG2
;;                                   PFIELD::ADD-OF-ADD-SAME
;;                                   )))))

;; (thm
;;  (not (equal 0 (add '<p-1> (mul '<d> (mul x x p) p) p))))


(defun double-point (point)
  (b* ((x (ecurve::point-finite->x point))
       (y (ecurve::point-finite->y point)))
    (ecurve::point-finite (double-u-coord x y (zcash::jubjub-q))
                          (double-v-coord x y (zcash::jubjub-q)))))

(in-theory (disable DOUBLE-U-COORD DOUBLE-v-COORD double-point))

(acl2::defopeners ECURVE::TWISTED-EDWARDS-MUL-NONNEG)

(defthmd double-correct
  (implies (EQUAL (ECURVE::POINT-KIND POINT) :FINITE)
           (equal (double-point point)
                  (ecurve::twisted-edwards-add point point (zcash::jubjub-curve))))
  :hints (("Goal" :in-theory (enable ECURVE::TWISTED-EDWARDS-ADD
                                     ZCASH::JUBJUB-CURVE
                                     DOUBLE-POINT
                                     DOUBLE-U-COORD
                                     DOUBLE-v-COORD
                                     ZCASH::JUBJUB-D
                                     ZCASH::JUBJUB-q
                                     ZCASH::JUBJUB-a))))

(defthm POINT-KIND-of-TWISTED-EDWARDS-ADD-when-finite
  (Implies (EQUAL (ECURVE::POINT-KIND POINT) :FINITE)
           (EQUAL (ECURVE::POINT-KIND (ECURVE::TWISTED-EDWARDS-ADD POINT POINT (ZCASH::JUBJUB-CURVE)))
                  :FINITE))
  :hints (("Goal" :in-theory (enable ECURVE::TWISTED-EDWARDS-ADD))))

;;gen?
(defthm twisted-edwards-add-of-twisted-edwards-zero
  (implies (and (ecurve::pointp point)
                ;; (ECURVE::POINT-ON-TWISTED-EDWARDS-P point (zcash::jubjub-curve)) ;overkill?
                (equal (ecurve::point-kind point) :finite)
                ;;better way to say this?:
                (< (ECURVE::POINT-FINITE->X POINT)
                   (ECURVE::TWISTED-EDWARDS-CURVE->P (ZCASH::JUBJUB-CURVE)))
                (< (ECURVE::POINT-FINITE->y POINT)
                   (ECURVE::TWISTED-EDWARDS-CURVE->P (ZCASH::JUBJUB-CURVE)))
                )
           (equal (ecurve::twisted-edwards-add point (ecurve::twisted-edwards-zero) (zcash::jubjub-curve))
                  point))
  :hints (("Goal" :in-theory (enable ecurve::twisted-edwards-add
                                     ecurve::twisted-edwards-zero
                                     ecurve::pointp
                                     ECURVE::EQUAL-OF-POINT-FINITE))))


;; (thm
;;  (equal (ECURVE::TWISTED-EDWARDS-ADD (ECURVE::TWISTED-EDWARDS-ADD POINT1 POINT2 (ZCASH::JUBJUB-CURVE)) point3 (ZCASH::JUBJUB-CURVE))
;;         (ECURVE::TWISTED-EDWARDS-ADD point1 (ECURVE::TWISTED-EDWARDS-ADD point2 point3 (ZCASH::JUBJUB-CURVE)) (ZCASH::JUBJUB-CURVE)))
;;  :hints (("Goal" :in-theory (e/d (ECURVE::TWISTED-EDWARDS-ADD
;;                                     ECURVE::EQUAL-OF-POINT-FINITE
;;                                     div
;;                                     PFIELD::MUL-OF-2)
;;                                  (PFIELD::ADD-OF-ADD-SAME
;;                                   PFIELD::ADD-OF-NEG-AND-NEG-SAME ;looped
;;                                   )))))

;; (thm
;;  (equal (ECURVE::TWISTED-EDWARDS-ADD (ECURVE::TWISTED-EDWARDS-ADD POINT POINT (ZCASH::JUBJUB-CURVE)) point2 (ZCASH::JUBJUB-CURVE))
;;         (ECURVE::TWISTED-EDWARDS-ADD point
;;                                      (ECURVE::TWISTED-EDWARDS-ADD point point2 (ZCASH::JUBJUB-CURVE))
;;                                      (ZCASH::JUBJUB-CURVE)))
;;  :hints (("Goal" :in-theory (e/d (ECURVE::TWISTED-EDWARDS-ADD
;;                                     ECURVE::EQUAL-OF-POINT-FINITE
;;                                     div
;;                                     PFIELD::MUL-OF-2)
;;                                  (PFIELD::ADD-OF-ADD-SAME
;;                                   PFIELD::ADD-OF-NEG-AND-NEG-SAME ;looped
;;                                   )))))

(defthmd twisted-edwards-mul-nonneg-of-8-becomes-three-doublings
  (implies (and (ecurve::pointp point)
                (equal (ecurve::point-kind point) :finite)
                (ECURVE::TWISTED-EDWARDS-ADD-ASSOCIATIVITY)
                (ECURVE::TWISTED-EDWARDS-CURVE-COMPLETEP curve)
                (ECURVE::POINT-ON-TWISTED-EDWARDS-P POINT curve)
                ;; (< (ECURVE::POINT-FINITE->X POINT)
                ;;    (ECURVE::TWISTED-EDWARDS-CURVE->P curve))
                ;; (< (ECURVE::POINT-FINITE->y POINT)
                ;;    (ECURVE::TWISTED-EDWARDS-CURVE->P curve))
                (equal curve (ZCASH::JUBJUB-CURVE))
                )
           (equal (ecurve::twisted-edwards-mul-nonneg 8 point curve)
                  (double-point (double-point (double-point point)))))
  :hints (("Goal" :in-theory (enable ecurve::twisted-edwards-mul-nonneg-unroll
                                     double-correct
                                     ZCASH::JUBJUB-POINTP
                                     ZCASH::POINT-FINITE-WHEN-JUBJUB-POINTP
                                     ZCASH::POINT-ON-JUBJUB-P))))

;'move
(acl2::add-known-boolean ECURVE::TWISTED-EDWARDS-CURVE-COMPLETEP)

(defthm fep-of-POINT-FINITE->X-of-DOUBLE-POINT
  (FEP (ECURVE::POINT-FINITE->X (DOUBLE-POINT point)) (zcash::jubjub-q))
  :hints (("Goal" :in-theory (enable DOUBLE-POINT DOUBLE-U-COORD))))

(defthm fep-of-POINT-FINITE->X-of-DOUBLE-POINT-alt
  (FEP (ECURVE::POINT-FINITE->X (DOUBLE-POINT point)) 52435875175126190479447740508185965837690552500527637822603658699938581184513)
  :hints (("Goal" :in-theory (enable DOUBLE-POINT DOUBLE-U-COORD (zcash::jubjub-q)))))

(defthm fep-of-POINT-FINITE->y-of-DOUBLE-POINT-alt
  (FEP (ECURVE::POINT-FINITE->y (DOUBLE-POINT point)) 52435875175126190479447740508185965837690552500527637822603658699938581184513)
  :hints (("Goal" :in-theory (enable DOUBLE-POINT DOUBLE-v-COORD (zcash::jubjub-q)))))


(defthm equal-of-0-and-point-finite->x-of-double-point
  (implies (and (fep (ecurve::point-finite->x point)
                     (zcash::jubjub-q))
                (fep (ecurve::point-finite->y point)
                     (zcash::jubjub-q)))
           (equal (equal 0 (ecurve::point-finite->x (double-point point)))
                  (if (equal 0 (ecurve::point-finite->y point))
                      t
                    (equal 0 (ecurve::point-finite->x point)))))
  :hints (("Goal" :in-theory (enable double-point
                                     zcash::jubjub-q))))

(defthm equal-of-0-and-point-finite->y-of-double-point-of-point-finite-of-0-arg2
  (implies (and (fep u (zcash::jubjub-q)))
           (equal (equal 0 (ecurve::point-finite->y (double-point (ECURVE::POINT-FINITE u '0))))
                  (equal 0 u)))
  :hints (("Goal" :in-theory (enable double-point
                                     double-v-coord
                                     zcash::jubjub-q))))

(defthm equal-of-0-and-point-finite->y-of-double-point-of-point-finite-of-0-arg2-gen
  (implies (and (fep (ecurve::point-finite->x point) (zcash::jubjub-q))
                (equal 0 (ecurve::point-finite->y point)))
           (equal (equal 0 (ecurve::point-finite->y (double-point point)))
                  (equal 0 (ecurve::point-finite->x point))))
  :hints (("Goal" :in-theory (enable double-point
                                     double-v-coord
                                     zcash::jubjub-q))))

(defthm not-equal-of-0-and-point-finite->y-of-double-point-of-point-finite-of-0-arg2-gen-alt
  (implies (and (fep (ecurve::point-finite->x point) (zcash::jubjub-q))
                (equal 0 (ecurve::point-finite->y point))
                (not (equal 0 (ecurve::point-finite->x point))))
           (not (equal 0 (ecurve::point-finite->y (double-point point)))))
  :hints (("Goal" :in-theory (enable double-point
                                     double-v-coord
                                     zcash::jubjub-q))))

(defthm not-equal-of-1/d-and-muls
  (not (EQUAL 20979470760985547108818104771683388870802557968228684781172577118520348350873
              (MUL u (MUL u (MUL v v 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                          52435875175126190479447740508185965837690552500527637822603658699938581184513)
                   52435875175126190479447740508185965837690552500527637822603658699938581184513)))
  :hints (("Goal" :use ((:instance ECURVE::PFIELD-SQUAREP-SUFF
                                   (x (inv (ZCASH::JUBJUB-D)
                                           (ZCASH::JUBJUB-Q)))
                                   (r (MUL U V (ZCASH::JUBJUB-Q)))
                                   (p (ZCASH::JUBJUB-Q))))
           :in-theory (enable ZCASH::JUBJUB-D
                              ZCASH::JUBJUB-q))))

;; (defthm not-equal-of-0-and-point-finite->y-of-double-point-twice
;;   (implies (and (fep (ecurve::point-finite->x point) (zcash::jubjub-q))
;;                 (equal 0 (ecurve::point-finite->y point))
;;                 (not (equal 0 (ecurve::point-finite->x point))))
;;            (not (equal 0 (ecurve::point-finite->y (double-point (double-point point)))))))

;drop some of the above?

(defthm equal-of-0-and-point-finite->y-of-double-point
  (implies (and (fep (ecurve::point-finite->x point)
                     (zcash::jubjub-q))
                (fep (ecurve::point-finite->y point)
                     (zcash::jubjub-q)))
           (equal (equal 0 (ecurve::point-finite->y (double-point point)))
                  (equal 0 (double-v-coord (ecurve::point-finite->x point)
                                           (ecurve::point-finite->y point)
                                           (zcash::jubjub-q)))))
  :hints (("Goal" :in-theory (enable double-point
                                     double-v-coord
                                     zcash::jubjub-q
                                     PFIELD::EQUAL-OF-DIV))))


;(include-book "kestrel/crypto/ecurve/prime-field-extra-rules" :dir :system)

(defthm POINT-FINITE->x-of-double-opoint-of-POINT-FINITE-of-0-arg2
  (equal (ECURVE::POINT-FINITE->X (DOUBLE-POINT (ECURVE::POINT-FINITE U/NUM '0)))
         0)
  :hints (("Goal" :in-theory (enable DOUBLE-POINT DOUBLE-U-COORD))))

;; (thm
;;  (not (ECURVE::POINT-ON-TWISTED-EDWARDS-P (ECURVE::POINT-FINITE U/NUM '0)
;;                                           (ZCASH::JUBJUB-CURVE)))
;;  :hints (("Goal" :in-theory (enable ECURVE::POINT-ON-TWISTED-EDWARDS-P
;;                                     ZCASH::JUBJUB-CURVE
;;                                     ZCASH::JUBJUB-A
;;                                     ZCASH::JUBJUB-q
;;                                     ZCASH::JUBJUB-D))))

(defthm DOUBLE-U-COORD-of-0-arg2
  (equal (DOUBLE-U-COORD U/NUM '0 p) 0) :hints (("Goal" :in-theory (enable DOUBLE-U-COORD))))

(defthm POINT-FINITE->X-of-DOUBLE-POINT
  (equal (ECURVE::POINT-FINITE->X (DOUBLE-POINT point))
         (DOUBLE-u-COORD (ECURVE::POINT-FINITE->X point)
                         (ECURVE::POINT-FINITE->y point)
                         (zcash::jubjub-q)))
  :hints (("Goal" :in-theory (enable double-point))))

(defthm POINT-FINITE->y-of-DOUBLE-POINT
  (equal (ECURVE::POINT-FINITE->y (DOUBLE-POINT point))
         (DOUBLE-v-COORD (ECURVE::POINT-FINITE->X point)
                         (ECURVE::POINT-FINITE->y point)
                         (zcash::jubjub-q)))
  :hints (("Goal" :in-theory (enable double-point))))

(defthm fep-of-double-u-coord
  (implies (and (< 1 p) (integerp p))
           (fep (double-u-coord u v p) p))
  :hints (("Goal" :in-theory (enable double-u-coord))))

(defthm fep-of-double-v-coord
  (implies (and (< 1 p) (integerp p))
           (fep (double-v-coord u v p) p))
  :hints (("Goal" :in-theory (enable double-v-coord))))

(defthm point-kind-of-double-point
  (implies (equal :finite (ecurve::point-kind point))
           (equal (ecurve::point-kind (double-point point)) :finite))
  :hints (("Goal" :in-theory (enable double-point))))

(verify-zcash-r1cs
 *a-3-3-6-simp-lifted*
 (implies (and (zcash::point-on-jubjub-p (ecurve::point-finite u/num v/num))
               (ecurve::twisted-edwards-add-associativity) ; todo: remove
               )
          (zcash::nonsmall-order-spec u/num v/num))
 ;; todo: global rules ignored if no rule-lists given
 :NO-SPLITP nil
 :monitor '( ;solve-1 ;todo: no feedback from free vars not matched?
;not-equal-of-0-and-point-finite->y-of-double-point-of-point-finite-of-0-arg2-gen-alt
            fep-of-POINT-FINITE->y-of-DOUBLE-POINT-alt
            EQUAL-OF-0-AND-DOUBLE-U-COORD-BETTER)
 :tactic
;rewrite
 '(:rep (:seq (:rep :rewrite) :subst))
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
;zcash::jubjub-curve
                 zcash::jubjub-q ;  called <p> in this book
;zcash::jubjub-a
;zcash::jubjub-d
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
                 PFIELD::SUB-OF-0
                 PFIELD::MUL-OF-1-ARG2
                 PFIELD::EQUAL-OF-ADD-CANCEL-1
;PFIELD::MUL-OF--1-BECOMES-NEG-ALT
                 zcash::primep-of-jubjub-q-better
;product-not-equal-helper-2-associated-commuted
;product-not-equal-helper-assoc-comm
                 ;; spec stuff:
                 ECURVE::TWISTED-EDWARDS-MUL
;ECURVE::TWISTED-EDWARDS-MUL-NONNEG ;recursive
                 ECURVE::TWISTED-EDWARDS-ZERO
                 equal-of-0-and-add-same
                 PRIMES::HAS-SQUARE-ROOT?-CONSTANT-OPENER
                 ECURVE::POINT-FINITE-CONSTANT-OPENER ;maybe
                 ECURVE::POINT-KIND-CONSTANT-OPENER
                 ECURVE::POINTP-CONSTANT-OPENER
                 ECURVE::POINT-finite->x-CONSTANT-OPENER
                 ECURVE::POINT-finite->y-CONSTANT-OPENER
                 ECURVE::POINT-fix-CONSTANT-OPENER
                 sub
                 pfield::equal-of-0-and-div-special
                 )
 :rule-lists '((
                ZCASH::AFFINE-EDWARDS-SPEC
                solve-1
                solve-2
                solve-3
                solve-4
                solve-5
                solve-6
                PFIELD::EQUAL-OF-MUL-CONSTANTS
                equal-of-mul-same-using-tonelli-shanks-when-constant
                equal-of-mul-same-using-tonelli-shanks-when-constant-special
                PFIELD::NEG-OF-MUL-WHEN-CONSTANT
                ;; PFIELD::MUL-ASSOCIATIVE
                ;; PFIELD::MUL-COMMUTATIVE-2-AXE
                ;; PFIELD::MUL-COMMUTATIVE-AXE
                )
               (ZCASH::NONSMALL-ORDER-SPEC)
               (intro-double-u-coord
                intro-double-v-coord
                double-u-coord-of-0-arg1
                equal-of-0-and-double-u-coord-better
                equal-of-add-of-neg-same
                twisted-edwards-mul-nonneg-of-8-becomes-three-doublings
;ECURVE::TWISTED-EDWARDS-CURVE-COMPLETEP
                ZCASH::NOT-PFIELD-SQUAREP-OF-JUBJUB-D
                ZCASH::TWISTED-EDWARDS-CURVE-COMPLETEP-OF-JUBJUB-CURVE
                ZCASH::POINT-ON-JUBJUB-P
                equal-of-0-and-point-finite->x-of-double-point
                fep-of-POINT-FINITE->X-of-DOUBLE-POINT-alt
                fep-of-POINT-FINITE->y-of-DOUBLE-POINT-alt
                equal-of-0-and-point-finite->y-of-double-point-of-point-finite-of-0-arg2-gen
;not-equal-of-0-and-point-finite->y-of-double-point-of-point-finite-of-0-arg2-gen-alt
                equal-of-0-and-point-finite->y-of-double-point
                POINT-FINITE->x-of-double-opoint-of-POINT-FINITE-of-0-arg2
                DOUBLE-U-COORD-of-0-arg2
                POINT-FINITE->X-of-DOUBLE-POINT
                POINT-FINITE->y-of-DOUBLE-POINT
                fep-of-DOUBLE-U-COORD
                fep-of-DOUBLE-v-COORD
                POINT-KIND-of-DOUBLE-POINT
                )
;; ( ;zcash::edwards-add-spec
;;                 pfield::<-when-fep
;;                 pfield::mul-of--1-becomes-neg-alt
;;                 pfield::add-commutative-2-axe
;;                 pfield::add-commutative-axe
;; ;pfield::mul-of-add-arg1
;; ;pfield::equal-of-div-alt
;;                 pfield::equal-of-sub-combine-constants
;;                 pfield::mod-of-add
;;                 ;; pfield::mul-of-sub-arg1
;;                 ;; pfield::mul-of-sub-arg2
;;                 pfield::sub
;; ;pfield::mul-of-add-arg2
;;                 pfield::mul-of-1-arg1
;;                 pfield::mul-of-1-arg2
;;                 pfield::mul-of-neg-arg2
;;                 pfield::equal-of-add-of-neg-simple
;; ;equal-of-add-of-negative-constant
;;                 pfield::mul-of-neg-arg1
;;                 pfield::equal-of-mul-same-arg2
;;                 acl2::if-of-t-and-nil-when-booleanp
;;                 acl2::booleanp-of-equal
;;                 ecurve::point-kind-of-if
;;                 ecurve::pointp-of-if
;;                 ecurve::point-kind-of-point-infinite
;;                 ecurve::pointp-of-point-infinite-better
;;                 equal-of-if-arg2
;; ;ECURVE::POINT-ON-EDWARDS-P
;; ;solve-for-lambda
;;                 add-of-mul-same-arg1-arg1
;;                 add-of-mul-same-arg1-arg2
;; ;solve-for-u3
;;                 )
;;                (solve-for-u3)
;;                ( ;pfield::equal-of-div-alt
;;                 pfield::equal-of-div-alt-when-quotep
;;                 zcash::edwards-add-spec
;;                 pfield::mul-commutative-axe
;;                 pfield::mul-of-add-arg2
;;                 pfield::add-associative
;;                 pfield::add-of-add-of-neg-same
;; ;pfield::mul-associative
;;                 product-not-equal-helper
;;                 )
;;                (add-of-mul-and-neg-same-arg1
;;                 add-of-neg-and-mul-same-arg1
;;                 pfield::mul-of--1-becomes-neg-alt
;;                 PFIELD::EQUAL-OF-ADD-OF-NEG-ARG2
;;                 solve-for-v3
;;                 PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS
;;                 PFIELD::ADD-COMMUTATIVE-WHEN-CONSTANT
;;                 ADD-OF-CONSTANT-NORMALIZE-TO-FEP
;;                 PFIELD::EQUAL-OF-MUL-CONSTANTS
;;                 product-not-equal-helper-2-associated
;;                 )
;;                (pfield::mul-associative
;;                 pfield::div-of-neg-arg1-move-to-arg2
;;                 ;
;;                 )
;;                (pfield::neg-of-add
;;                 pfield::mul-commutative-axe
;;                 pfield::mul-commutative-2-axe
;;                 collect-mults
;;                 solve-inverted
;;                 )
;; ;; (solve-for-xprime)
;; ;; (solve-for-yprime)
;; ;; (zcash::edwards-add-spec
;; ;;  ecurve::edwards-add
;; ;;  sub
;; ;;  pfield::add-associative
;; ;;  pfield::add-commutative-axe
;; ;;  pfield::add-commutative-2-axe
;; ;;  pfield::neg-of-add
;; ;;  pfield::equal-of-add-and-add-cancel
;; ;;  pfield::mul-of-add-arg1
;; ;;  pfield::mul-of-add-arg2
;; ;;  pfield::mul-commutative-2-axe
;; ;;  pfield::mul-commutative-axe
;; ;;  pfield::mul-of-neg-arg1
;; ;;  pfield::mul-of-neg-arg2)
))
