; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "twisted-edwards")

(include-book "kestrel/crypto/primes/bls12-381-prime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jubjub
  :parents (elliptic-curves)
  :short "The Jubjub twisted Edwards elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "This elliptic curve is defined in Section 5.4.8.3 of the "
    (xdoc::ahref "https://zips.z.cash/protocol/protocol.pdf"
                 "Zcash Protocol Specification (Version 2020.1.15)")
    ". It is a complete twisted Edwards elliptic curve;
     see @(see twisted-edwards) for
     general information about twisted Edwards curves.")
   (xdoc::p
    "Here we define the Jubjub curve,
     as a constant value of the fixtype @(tsee twisted-edwards-curve)
     of twisted Edwards elliptic curves."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-q ()
  :returns (q rtl::primep)
  :short "The Jubjub prime @($q$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines the prime field over which Jubjub is defined.")
   (xdoc::p
    "We introduce this function for readability,
     but leave it enabled,
     so it always expands to the prime defined elsewhere.
     Thus, rules triggered by this abbreviation function
     should be generally avoided."))
  (primes::bls12-381-scalar-field-prime)
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-a ()
  :returns (a (fep a (jubjub-q)))
  :short "The Jubjub coefficient @($a$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that this coefficient is a square,
     by exhibiting a square root of it."))
  (neg 1 (jubjub-q))
  ///

  (defrule pfield-squarep-of-jubjub-a
    (pfield-squarep (jubjub-a) (jubjub-q))
    :use (:instance pfield-squarep-suff
          (x (jubjub-a))
          (r 3465144826073652318776269530687742778270252468765361963008)
          (p (jubjub-q)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-d ()
  :returns (d (fep d (jubjub-q)))
  :short "The Jubjub coefficient @($d$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that this coefficient is not a square,
     using Euler's criterion.
     We use the fast modular exponentiation operation
     from the @('arithmetic-3') library
     to calculate the modular exponentiation of the coefficient,
     which must be different from 1
     in order for the criterion to apply."))
  (neg (div 10240 10241 (jubjub-q)) (jubjub-q))
  ///

  (local (include-book "arithmetic-3/top" :dir :system))

  (defruledl mod-expt-fast-lemma
    (not (equal (acl2::mod-expt-fast (jubjub-d)
                                     (/ (1- (jubjub-q)) 2)
                                     (jubjub-q))
                1)))

  (defruledl mod-expt-lemma
    (not (equal (mod (expt (jubjub-d)
                           (/ (1- (jubjub-q)) 2))
                     (jubjub-q))
                1))
    :use (mod-expt-fast-lemma
          (:instance acl2::mod-expt-fast
           (a (jubjub-d))
           (i (/ (1- (jubjub-q)) 2))
           (n (jubjub-q))))
    :disable ((:e expt)))

  (local (include-book "prime-field-squares-euler-criterion"))

  (defrule not-pfield-squarep-of-jubjub-d
    (not (pfield-squarep (jubjub-d) (jubjub-q)))
    :enable (weak-euler-criterion-contrapositive)
    :use mod-expt-lemma
    :disable ((:e expt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-curve ()
  :returns (curve twisted-edwards-curvep)
  :short "The Jubjub curve."
  (make-twisted-edwards-curve :p (jubjub-q)
                              :a (jubjub-a)
                              :d (jubjub-d))
  ///

  (defrule twisted-edwards-curve-primep-of-jubjub-curve
    (twisted-edwards-curve-primep (jubjub-curve))
    :enable twisted-edwards-curve-primep
    :disable ((:e twisted-edwards-curve-primep)))

  (defrule twisted-edwards-curve-completep-of-jubjub-curve
    (twisted-edwards-curve-completep (jubjub-curve))
    :enable twisted-edwards-curve-completep
    :disable (pfield-squarep-of-jubjub-a
              not-pfield-squarep-of-jubjub-d)
    :use (pfield-squarep-of-jubjub-a
          not-pfield-squarep-of-jubjub-d))

  (in-theory (disable (:e jubjub-curve))))
