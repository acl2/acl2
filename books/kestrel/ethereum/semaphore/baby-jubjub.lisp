; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/crypto/ecurve/twisted-edwards" :dir :system)
(include-book "kestrel/crypto/primes/baby-jubjub-subgroup-prime" :dir :system)
(acl2::merge-io-pairs
 rtl::primep
 (include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This file contains a specification of the BabyJubjub elliptic curve.
;; This curve was defined by Barry Whitehat:
;; https://github.com/barryWhiteHat/baby_jubjub

;; From that repo:
;;   It is the twisted Edwards curve
;;     168700.x^2 + y^2 = 1 + 168696.x^2.y^2
;;   of rational points over
;;   GF(21888242871839275222246405745257275088548364400416034343698204186575808495617)
;; and, that repo also shows it satisfies the SafeCurves criteria.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The prime that defines the field over which BabyJubjub is defined.

; This is primes::bn-254-group-prime,
; but we introduce a BabyJubjub-specific nullary function for it there.

(define baby-jubjub-prime ()
  :returns (prime rtl::primep)
  (primes::bn-254-group-prime)
  ///

  (defrule baby-jubjub-prime-not-two
    (not (equal (baby-jubjub-prime) 2)))

  (in-theory (disable (:e baby-jubjub-prime))))

; This prime is 254 bits long.

(assert-event (equal (integer-length (baby-jubjub-prime)) 254))

; The following fact (i.e. prime mod 4 = 1) is relevant for EdDSA.

(assert-event (equal (mod (baby-jubjub-prime) 4) 1))

; The following fact (i.e. prime mod 8 = 1)
; means there is no simple formula for modular square root.

(assert-event (equal (mod (baby-jubjub-prime) 8) 1))

; However, there are reasonably efficient algorithms
; that require a starting non-residue.
; For a fixed prime we can often get a starting non-residue from the table
; in https://en.wikipedia.org/wiki/Quadratic_residue.
; It is the case that 5 is a quadratic non-residue for this prime.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The coefficient a of the twisted Edwards equation of BabyJubjub.
; This is not zero and is a square.
; We show that it is a square by exhibiting a square root,
; found using Mathematica's PowerMod.

(define baby-jubjub-a ()
  :returns (a (fep a (baby-jubjub-prime))
              :hints (("Goal" :in-theory (enable fep baby-jubjub-prime))))
  168700
  ///

  (defrule baby-jubjub-a-not-zero
    (not (equal (baby-jubjub-a) 0)))

  (defrule pfield-squarep-of-baby-jubjub-a
    (pfield-squarep (baby-jubjub-a) (baby-jubjub-prime))
    :use
    (:instance ecurve::pfield-squarep-suff
     (x (baby-jubjub-a))
     (r
      7214280148105020021932206872019688659210616427216992810330019057549499971851)
     (p (baby-jubjub-prime)))
    :enable baby-jubjub-prime)

  (in-theory (disable (:e baby-jubjub-a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The coefficient d of the twisted Edwards equation of BabyJubjub.
; This is not zero, is different from a, and is not a square.
; We show that it is not a square using Euler's criterion:
; we use the fast modular exponentiation operation
; from the arithmetic-3 library
; to calculate the modular exponentiation of the coefficient,
; which must be different from 1
; in order for the criterion to apply.

(define baby-jubjub-d ()
  :returns (d (fep d (baby-jubjub-prime))
              :hints (("Goal" :in-theory (enable fep baby-jubjub-prime))))
  168696
  ///

  (defrule baby-jubjub-d-not-zero
    (not (equal (baby-jubjub-d) 0)))

  (defrule baby-jubjub-d-not-equal-to-a
    (not (equal (baby-jubjub-d) (baby-jubjub-a)))
    :enable (baby-jubjub-a baby-jubjub-prime))

  (local (include-book "arithmetic-3/top" :dir :system))

  (defruledl mod-expt-fast-lemma
    (not (equal (acl2::mod-expt-fast (baby-jubjub-d)
                                     (/ (1- (baby-jubjub-prime)) 2)
                                     (baby-jubjub-prime))
                1))
    :enable baby-jubjub-prime)

  (defruledl mod-expt-lemma
    (not (equal (mod (expt (baby-jubjub-d)
                           (/ (1- (baby-jubjub-prime)) 2))
                     (baby-jubjub-prime))
                1))
    :use (mod-expt-fast-lemma
          (:instance acl2::mod-expt-fast
           (a (baby-jubjub-d))
           (i (/ (1- (baby-jubjub-prime)) 2))
           (n (baby-jubjub-prime))))
    :enable baby-jubjub-prime
    :disable ((:e expt)))

  (local (include-book "kestrel/crypto/ecurve/prime-field-squares-euler-criterion" :dir :system))

  (defrule not-pfield-squarep-of-baby-jubjub-d
    (not (ecurve::pfield-squarep (baby-jubjub-d) (baby-jubjub-prime)))
    :enable (ecurve::weak-euler-criterion-contrapositive baby-jubjub-prime)
    :use mod-expt-lemma
    :disable ((:e expt)))

  (in-theory (disable (:e baby-jubjub-d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the BabyJubjub curve.
; The fact that a is a square and d is not a square (see above)
; means that BabyJubjub is a complete twisted Edwards curve,
; i.e. the addition formula is complete (works for all points).

(define baby-jubjub-curve ()
  :returns (curve twisted-edwards-curvep)
  (make-twisted-edwards-curve :p (baby-jubjub-prime)
                              :a (baby-jubjub-a)
                              :d (baby-jubjub-d))
  ///

  (defrule twisted-edwards-curve-primep-of-baby-jubjub-curve
    (twisted-edwards-curve-primep (baby-jubjub-curve))
    :enable twisted-edwards-curve-primep
    :disable ((:e twisted-edwards-curve-primep)))

  (defrule twisted-edwards-curve-completep-of-baby-jubjub-curve
    (twisted-edwards-curve-completep (baby-jubjub-curve))
    :enable (twisted-edwards-curve-completep
             baby-jubjub-a
             baby-jubjub-d
             baby-jubjub-prime)
    :disable (pfield-squarep-of-baby-jubjub-a
              not-pfield-squarep-of-baby-jubjub-d)
    :use (pfield-squarep-of-baby-jubjub-a
          not-pfield-squarep-of-baby-jubjub-d))

  (in-theory (disable (:e baby-jubjub-curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BabyJubjub, as the twisted Edwards curve with a = 168700 and d = 168696,
;; is birationally equivalent to
;; the Montgomery curve with
;; A = 2(a+d)/(a-d) = 2*(168700 + 168696)/(168700 - 168696) = 168698
;; B = 4/(a-d) = 1
;; So the Montgomery curve is y^2 = x^3 + 168698x^2 + x
;;
;; Now, represent that in Weierstrass form:
;; [a1,a2,a3,a4,a6] in the Weierstrass equation:
;; y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6
;; a1=0, a3=0, a2=168698, a4=1, a6=0
;; [0,168698,0,1,0]
;;
;; In Sage, which can be used at:
;;   https://sagecell.sagemath.org/
;; Type this Sage code:
;;   P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
;;   E = EllipticCurve(GF(P),[0,168698,0,1,0])
;;   E.cardinality()
;; Clicking the Evaluate button will yield baby-jubjub-order:

(define baby-jubjub-order ()
  :returns (order natp)
  21888242871839275222246405745257275088614511777268538073601725287587578984328
  ///

  (in-theory (disable (:e baby-jubjub-order))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; RFC 8032 (*) says the order of the curve should be 2^c.l where l is a large prime.
;; The prime factorization of this n is:
;;   2^3 * 2736030358979909402780800718157159386076813972158567259200215660948447373041
;; so this looks suitable for EdDSA.
;; (*) https://tools.ietf.org/html/rfc8032
;;     Edwards-Curve Digital Signature Algorithm (EdDSA)
;;
;; Also, SafeCurves requires l to be at least 2^200.
;; (integer-length 2736030358979909402780800718157159386076813972158567259200215660948447373041)
;; => 251

; This is primed::baby-jubjub-subgroup-prime,
; but we introduce a shorter synonym for it here,
; which conveys that it is the order divided by 8.

(define baby-jubjub-order/8 ()
  :returns (order/8 rtl::primep)
  (primes::baby-jubjub-subgroup-prime)
  ///

  (in-theory (disable (:e baby-jubjub-order/8))))

(assert-event (equal (integer-length (baby-jubjub-order/8)) 251))

(assert-event (equal (baby-jubjub-order/8) (/ (baby-jubjub-order) 8)))
