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
    (xdoc::seetopic "https://zips.z.cash/protocol/protocol.pdf"
                    "Zcash Protocol Specification (Version 2020.1.15)")
    ". It is a complete twisted Edwards elliptic curve;
     see @(see twisted-edwards-curves) for
     general information about twisted Edwards curves.")
   (xdoc::p
    "Here we define the Jubjub curve,
     as a constant value of the fixtype @(tsee twisted-edwards)
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
  (neg (div 10240 10241 (jubjub-q)) (jubjub-q)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-curve ()
  :returns (curve twisted-edwards-p)
  :short "The Jubjub curve."
  (make-twisted-edwards :p (jubjub-q)
                        :a (jubjub-a)
                        :d (jubjub-d))
  ///

  (defrule twisted-edwards-primep-of-jubjub-curve
    (twisted-edwards-primep (jubjub-curve))
    :enable twisted-edwards-primep
    :disable ((:e twisted-edwards-primep)))

  (in-theory (disable (:e jubjub-curve))))
