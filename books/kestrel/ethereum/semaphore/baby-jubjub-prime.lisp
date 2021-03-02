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

(include-book "kestrel/crypto/primes/bn-254-group-prime" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define baby-jubjub-prime ()
  :returns (prime rtl::primep)
  :parents (zksemaphore::baby-jubjub)
  :short "The prime that defines the field over which BabyJubjub is defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @('primes::bn-254-group-prime'),
     but we introduce a BabyJubjub-specific nullary function for it here.")
   (xdoc::p
    "Decimal value: " (xdoc::tt "21888242871839275222246405745257275088548364400416034343698204186575808495617"))
   (xdoc::p
    "Hex value: " (xdoc::tt "#x30644E72E131A029B85045B68181585D2833E84879B9709143E1F593F0000001"))
   (xdoc::p
    "This prime is 254 bits long.")
   (xdoc::p
    "The fact that this prime mod 4 is 1 is relevant for EdDSA.")
   (xdoc::p
    "The fact that this prime mod 8 is 1
     means there is no simple formula for modular square root.
     However, there are reasonably efficient algorithms
     that require a starting non-residue.
     For a fixed prime we can often get a starting non-residue from the table
     in "
    (xdoc::ahref "https://en.wikipedia.org/wiki/Quadratic_residue"
                 "https://en.wikipedia.org/wiki/Quadratic_residue")
    ". It is the case that 5 is a quadratic non-residue for this prime."))
  (primes::bn-254-group-prime)
  ///

  (assert-event (equal (integer-length (baby-jubjub-prime)) 254))

  (assert-event (equal (mod (baby-jubjub-prime) 4) 1))

  (assert-event (equal (mod (baby-jubjub-prime) 8) 1))

  (defrule baby-jubjub-prime-not-two
    (not (equal (baby-jubjub-prime) 2)))

  (in-theory (disable (:e baby-jubjub-prime))))
