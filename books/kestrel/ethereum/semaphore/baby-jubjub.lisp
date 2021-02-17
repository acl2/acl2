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

(include-book "baby-jubjub-prime")

(include-book "kestrel/crypto/ecurve/twisted-edwards" :dir :system)
(acl2::merge-io-pairs
 rtl::primep
 (include-book "kestrel/crypto/primes/baby-jubjub-subgroup-prime" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ baby-jubjub
  :parents (semaphore)
  :short "The BabyJubjub complete twisted Edwards curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "This curve was defined by Barry Whitehat:")
   (xdoc::p
    (xdoc::ahref "https://github.com/barryWhiteHat/baby_jubjub"
                 "https://github.com/barryWhiteHat/baby_jubjub"))
   (xdoc::p
    "From that repo:")
   (xdoc::codeblock
    "It is the twisted Edwards curve"
    " 168700.x^2 + y^2 = 1 + 168696.x^2.y^2"
    "of rational points over"
    "GF(21888242871839275222246405745257275088548364400416034343698204186575808495617)")
   (xdoc::p
    "That repo also shows that it satisfies the SafeCurves criteria."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define baby-jubjub-a ()
  :returns (a (fep a (baby-jubjub-prime))
              :hints (("Goal" :in-theory (enable fep baby-jubjub-prime))))
  :short "The coefficient @($a$) of the twisted Edwards equation of BabyJubjub."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not zero and is a square.
     We show that it is a square by exhibiting a square root,
     found using Mathematica's PowerMod."))
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

(define baby-jubjub-d ()
  :returns (d (fep d (baby-jubjub-prime))
              :hints (("Goal" :in-theory (enable fep baby-jubjub-prime))))
  :short "The coefficient @($d$) of the twisted Edwards equation of BabyJubjub."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not zero, is different from @($a$), and is not a square.
     We show that it is not a square using Euler's criterion:
     we use the fast modular exponentiation operation
     from the @('arithmetic-3') library
     to calculate the modular exponentiation of the coefficient,
     which must be different from 1
     in order for the criterion to apply."))
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

(define baby-jubjub-curve ()
  :returns (curve twisted-edwards-curvep)
  :short "The BabyJubjub curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fact that a is a square and d is not a square
     (see @(tsee baby-jubjub-a) and @(tsee baby-jubjub-d))
     means that BabyJubjub is a complete twisted Edwards curve,
     i.e. the addition formula is complete (works for all points)."))
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

(define baby-jubjub-order ()
  :returns (order natp)
  :short "Order (i.e. number of points) of the BabyJubjub curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "BabyJubjub, as the twisted Edwards curve with
     @($a = 168700$) and @($d = 168696$),
     is birationally equivalent to
     the Montgomery curve with")
   (xdoc::@[]
    "\\begin{array}{l}
     A = 2(a+d)/(a-d) = 2*(168700 + 168696)/(168700 - 168696) = 168698
     \\\\
     B = 4/(a-d) = 1
     \\end{array}")
   (xdoc::p
    "So the Montgomery curve is")
   (xdoc::@[]
    "y^2 = x^3 + 168698x^2 + x")
   (xdoc::p
    "Now, represent that in Weierstrass form:")
   (xdoc::@[]
    "y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6")
   (xdoc::p
    "We have:")
   (xdoc::@[]
    "[a_1, a_2, a_3, a_4, a_6] = [0, 168698, 0, 1, 0]")
   (xdoc::p
    "In Sage, which can be used at "
    (xdoc::ahref "https://sagecell.sagemath.org"
                 "https://sagecell.sagemath.org")
    ", type this Sage code:")
   (xdoc::codeblock
    "P = 21888242871839275222246405745257275088548364400416034343698204186575808495617"
    "E = EllipticCurve(GF(P),[0,168698,0,1,0])"
    "E.cardinality()")
   (xdoc::p
    "Clicking the `Evaluate' button will yield BabyJubjub order."))
  21888242871839275222246405745257275088614511777268538073601725287587578984328
  ///

  (in-theory (disable (:e baby-jubjub-order))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define baby-jubjub-order/8 ()
  :returns (order/8 rtl::primep)
  :short "The prime that is 1/8th of the order of BabyJubjub."
  :long
  (xdoc::topstring
   (xdoc::p
    (xdoc::ahref "https://tools.ietf.org/html/rfc8032" "RFC 8032")
    " says the order of the curve should be
     @($2^c l$) where @($l$) is a large prime.
     The prime factorization of @(tsee baby-jubjub-order) is")
   (xdoc::@[]
    "2^3 \\times
     2736030358979909402780800718157159386076813972158567259200215660948447373041")
   (xdoc::p
    "so this looks suitable for the
     Edwards-Curve Digital Signature Algorithm (EdDSA).")
   (xdoc::p
    "Also, SafeCurves requires @($l$) to be at least @($2^200$).
     The length of this prime is 251.")
   (xdoc::p
    "This prime is @('primes::baby-jubjub-subgroup-prime'),
     but we introduce a shorter synonym for it here,
     which conveys that it is the BabyJubjub order divided by 8."))
  (primes::baby-jubjub-subgroup-prime)
  ///

  (assert-event (equal (integer-length (baby-jubjub-order/8)) 251))

  (assert-event (equal (baby-jubjub-order/8) (/ (baby-jubjub-order) 8)))

  (in-theory (disable (:e baby-jubjub-order/8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-on-baby-jubjub-p ((point ecurve::pointp))
  :returns (yes/no booleanp)
  :short "Check if a point is on BabyJubjub."
  (ecurve::point-on-twisted-edwards-p point (baby-jubjub-curve))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define baby-jubjub-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize the points on the BabyJubjub curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all finite points."))
  (and (ecurve::pointp x)
       (point-on-baby-jubjub-p x))
  :hooks (:fix)
  ///
  (defruled point-finite-when-baby-jubjub-pointp
    (implies (baby-jubjub-pointp x)
             (equal (ecurve::point-kind x) :finite))
    :enable point-on-baby-jubjub-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define baby-jubjub-mul ((scalar integerp) (point baby-jubjub-pointp))
  :returns (point1 baby-jubjub-pointp
                   :hyp (baby-jubjub-pointp point)
                   :hints (("Goal" :in-theory (enable baby-jubjub-pointp
                                                      point-on-baby-jubjub-p))))
  :short "Scalar multiplication on BabyJubjub."
  (ecurve::twisted-edwards-mul scalar point (baby-jubjub-curve))
  :guard-hints (("Goal" :in-theory (enable baby-jubjub-pointp
                                           point-on-baby-jubjub-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define baby-jubjub-add ((point1 baby-jubjub-pointp)
                         (point2 baby-jubjub-pointp))
  :returns (point baby-jubjub-pointp
                  :hyp (and (baby-jubjub-pointp point1)
                            (baby-jubjub-pointp point2))
                  :hints (("Goal" :in-theory (enable baby-jubjub-pointp
                                                     point-on-baby-jubjub-p))))
  :short "Group addition on BabyJubjub."
  (ecurve::twisted-edwards-add point1 point2 (baby-jubjub-curve))
  :guard-hints (("Goal" :in-theory (enable baby-jubjub-pointp
                                           point-on-baby-jubjub-p))))
