; bls12-377-curves Library
;
; Copyright (C) 2023 Aleo Systems Inc. (https://www.aleo.org)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "std/util/add-io-pairs" :dir :system)

(include-book "kestrel/crypto/ecurve/twisted-edwards" :dir :system)
(include-book "projects/bls12-377-curves/primes/top" :dir :system)

(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ edwards-bls12
  :parents (crypto::bls12-377-curves)
  :short "The Edwards-BLS12 complete twisted Edwards elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the Edwards-BLS12 curve,
     as a constant value of the fixtype @(tsee twisted-edwards-curve)
     of twisted Edwards elliptic curves.
     We show that the curve is complete.")
   (xdoc::p
    "The prime and coefficients of Edwards-BLS12
     are formalized as nullary functions.
     We keep disabled also their executable counterparts because
     we generally want to treat them as algebraic quantities in proofs;
     in particular, we want to avoid their combination into new constants
     by the prime field normalizing rules.")
   (xdoc::p
    "We also define various notions related to Edwards-BLS12,
     such as recognizers of points in the curve's group and subgroup."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-q ()
  :returns (q dm::primep)
  :short "The Edwards-BLS12 base field prime @($F_q$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines the prime field over which Edwards-BLS12 is defined.")
   (xdoc::p
    "It is the same as the scalar field of the BLS12-377 elliptic curve.
     See @(tsee primes::bls12-377-scalar-field-prime) for the exact value.
     The reason this number is called @($q$) here but @($r$) in the
     BLS12-377 domain parameters, is because the letter is relative to
     the curve.  The Edwards-BLS12 curve's base field prime (here @($q$))
     is equal to the BLS12-377 curve's scalar field prime (there @($r$))."))

  (primes::bls12-377-scalar-field-prime)
  ///

  (defrule edwards-bls12-q-not-two
    (not (equal (edwards-bls12-q) 2)))

  (in-theory (disable (:e edwards-bls12-q))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-a ()
  :returns (a (fep a (edwards-bls12-q))
              :hints (("Goal" :in-theory (enable fep edwards-bls12-q))))
  :short "The Edwards-BLS12 coefficient @($a$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that this coefficient is a square
     by exhibiting a square root of it."))
  (neg 1 (edwards-bls12-q))
  ///

  (defrule edwards-bls12-a-not-zero
    (not (equal (edwards-bls12-a) 0)))

  (defrule pfield-squarep-of-edwards-bls12-a
    (pfield-squarep (edwards-bls12-a) (edwards-bls12-q))
    :use (:instance pfield-squarep-suff
                    (x (edwards-bls12-a))
          ;; r is a square root of -1 in (edwards-bls12-q)
          (r 880904806456922042258150504921383618666682042621506879489)
          (p (edwards-bls12-q)))
    :enable edwards-bls12-q)

  (in-theory (disable (:e edwards-bls12-a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-d ()
  :returns (d (fep d (edwards-bls12-q))
              :hints (("Goal" :in-theory (enable fep edwards-bls12-q))))
  :short "The Edwards-BLS12 coefficient @($d$)"
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that this coefficient is not a square
     using Euler's criterion.
     We use the fast modular exponentiation operation
     from the @('arithmetic-3') library
     to calculate the modular exponentiation of the coefficient,
     which must be different from 1
     in order for the criterion to apply."))
  3021
  :guard-hints (("Goal" :in-theory (enable fep edwards-bls12-q)))
  ///

  (defrule edwards-bls12-d-not-zero
    (not (equal (edwards-bls12-d) 0)))

  (defrule edwards-bls12-d-not-equal-to-a
    (not (equal (edwards-bls12-d) (edwards-bls12-a)))
    :enable (edwards-bls12-a edwards-bls12-q))

  (local (include-book "arithmetic-3/top" :dir :system))

  (defruledl mod-expt-fast-lemma
    (not (equal (acl2::mod-expt-fast (edwards-bls12-d)
                                     (/ (1- (edwards-bls12-q)) 2)
                                     (edwards-bls12-q))
                1))
    :enable edwards-bls12-q)

  (defruledl mod-expt-lemma
    (not (equal (mod (expt (edwards-bls12-d)
                           (/ (1- (edwards-bls12-q)) 2))
                     (edwards-bls12-q))
                1))
    :use (mod-expt-fast-lemma
          (:instance acl2::mod-expt-fast
           (a (edwards-bls12-d))
           (i (/ (1- (edwards-bls12-q)) 2))
           (n (edwards-bls12-q))))
    :enable edwards-bls12-q
    :disable ((:e expt)))

  (local (include-book "kestrel/crypto/ecurve/prime-field-squares-euler-criterion" :dir :system))

  (defrule not-pfield-squarep-of-edwards-bls12-d
    (not (pfield-squarep (edwards-bls12-d) (edwards-bls12-q)))
    :enable (weak-euler-criterion-contrapositive edwards-bls12-q)
    :use mod-expt-lemma
    :disable ((:e expt)))

  (in-theory (disable (:e edwards-bls12-d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-curve ()
  :returns (curve twisted-edwards-curvep)
  :short "The Edwards-BLS12 curve"
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that it is complete."))
  (make-twisted-edwards-curve :p (edwards-bls12-q)
                                      :a (edwards-bls12-a)
                                      :d (edwards-bls12-d))
  ///

  (defrule twisted-edwards-curve-completep-of-edwards-bls12-curve
    (twisted-edwards-curve-completep (edwards-bls12-curve))
    :enable (twisted-edwards-curve-completep
             edwards-bls12-a
             edwards-bls12-d
             edwards-bls12-q)
    :disable (pfield-squarep-of-edwards-bls12-a
              not-pfield-squarep-of-edwards-bls12-d)
    :use (pfield-squarep-of-edwards-bls12-a
          not-pfield-squarep-of-edwards-bls12-d))

  (in-theory (disable (:e edwards-bls12-curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize elements of Edwards-BLS12 curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the points on the Edwards-BLS12 curve.")
   (xdoc::p
    "These are all finite points."))
  (and (pointp x)
       (point-on-twisted-edwards-p x (edwards-bls12-curve)))
  ///

  (defruled pointp-when-edwards-bls12-pointp
    (implies (edwards-bls12-pointp x)
             (pointp x)))

  (defruled point-finite-when-edwards-bls12-pointp
    (implies (edwards-bls12-pointp x)
             (equal (point-kind x) :finite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-edwards-bls12-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize Edwards-BLS12 points and @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are optional Edwards-BLS12 points.
     Useful, for instance, as results of functions that may return
     either Edwards-BLS12 points or an error value."))
  (or (edwards-bls12-pointp x)
      (eq x nil))
  ///
  (defrule maybe-edwards-bls12-pointp-when-edwards-bls12-pointp
    (implies (edwards-bls12-pointp x)
             (maybe-edwards-bls12-pointp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: describe this concept in other terms
(define edwards-bls12-point->u ((point edwards-bls12-pointp))
  :returns (u natp :rule-classes :type-prescription)
  :short "The function @($\\mathcal{U}$) in TODO"
  :long
  (xdoc::topstring
   (xdoc::p
    "This function can be defined on any finite point (in fact, on any pair),
     but it is only used on Edwards-BLS12 points.")
   (xdoc::p
    "This is always below the Edwards-BLS12 field prime."))
  (point-finite->x point)
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp)))
  ///
  (defret edwards-bls12-point->u-upper-bound
    (< u (edwards-bls12-q))
    :hyp (edwards-bls12-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable edwards-bls12-pointp
                                       point-on-twisted-edwards-p
                                       edwards-bls12-curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: describe this concept in other terms
(define edwards-bls12-point->v ((point edwards-bls12-pointp))
  :returns (v natp :rule-classes :type-prescription)
  :short "The function @($\\mathcal{V}$) in TODO"
  :long
  (xdoc::topstring
   (xdoc::p
    "This function can be defined on any finite point (in fact, on any pair),
     but it is only used on Edwards-BLS12 points.")
   (xdoc::p
    "This is always below the Edwards-BLS12 field prime."))
  (point-finite->y point)
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp)))
  ///
  (defret edwards-bls12-point->v-upper-bound
    (< v (edwards-bls12-q))
    :hyp (edwards-bls12-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable edwards-bls12-pointp
                                       point-on-twisted-edwards-p
                                       edwards-bls12-curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-mul ((scalar integerp) (point edwards-bls12-pointp))
  :returns (point1 edwards-bls12-pointp
                   :hyp (edwards-bls12-pointp point)
                   :hints (("Goal" :in-theory (enable edwards-bls12-pointp))))
  :short "Scalar multiplication on Edwards-BLS12."
  (twisted-edwards-mul scalar point (edwards-bls12-curve))
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We plan to change edwards-bls12-mul to use twisted-edwards-mul-fast.
(define edwards-bls12-mul-fast ((scalar integerp) (point edwards-bls12-pointp))
  :returns (point1 edwards-bls12-pointp
                   :hyp (edwards-bls12-pointp point)
                   :hints (("Goal" :in-theory (enable edwards-bls12-pointp))))
  :short "Fast scalar multiplication on Edwards-BLS12."
  (twisted-edwards-mul-fast scalar point (edwards-bls12-curve))
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-add ((point1 edwards-bls12-pointp)
                           (point2 edwards-bls12-pointp))
  :returns (point edwards-bls12-pointp
                  :hyp (and (edwards-bls12-pointp point1)
                            (edwards-bls12-pointp point2))
                  :hints (("Goal" :in-theory (enable edwards-bls12-pointp))))
  :short "Group addition on Edwards-BLS12."
  (twisted-edwards-add point1 point2 (edwards-bls12-curve))
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-neg ((point1 edwards-bls12-pointp))
  :returns (point edwards-bls12-pointp
                  :hyp (edwards-bls12-pointp point1)
                  :hints (("Goal" :in-theory (enable edwards-bls12-pointp))))
  :short "Group point negation on Edwards-BLS12."
  (twisted-edwards-neg point1 (edwards-bls12-curve))
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-h ()
  :returns (h natp)
  :short "The elliptic curve cofactor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the number that,
     when multiplied by the large subgroup order @($r$),
     yields the full order of the elliptic curve group."))
  4
  ///
  (in-theory (disable (:e edwards-bls12-h))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-r ()
  :returns (r natp)
  :short "The prime number that is
          the order of the large subgroup of Edwards-BLS12."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the exact value see @(tsee primes::edwards-bls12-subgroup-prime)."))

  (primes::edwards-bls12-subgroup-prime)

  ///

  (defrule primep-of-edwards-bls12-r
    (dm::primep (edwards-bls12-r)))

  (in-theory (disable (:e edwards-bls12-r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-r-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize elements of @($r$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the points of order @($r$)."))
  (or (equal x (twisted-edwards-zero))
      (and (edwards-bls12-pointp x)
           (twisted-edwards-point-orderp x
                                         (edwards-bls12-r)
                                         (edwards-bls12-curve))))
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp)))
  ///

  (defrule edwards-bls12-pointp-when-edwards-bls12-r-pointp
    (implies (edwards-bls12-r-pointp x)
             (edwards-bls12-pointp x))
    :enable twisted-edwards-zero))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edwards-bls12-rstar-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize elements of @($r$) except the zero point."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the points of order @($r$)
     except for the zero point."))
  (and (edwards-bls12-pointp x)
       (twisted-edwards-point-orderp x (edwards-bls12-r) (edwards-bls12-curve)))
  :guard-hints (("Goal" :in-theory (enable edwards-bls12-pointp)))
  ///

  (defrule edwards-bls12-r-pointp-when-edwards-bls12-rstar-pointp
    (implies (edwards-bls12-rstar-pointp x)
             (edwards-bls12-r-pointp x))
    :enable edwards-bls12-r-pointp))
