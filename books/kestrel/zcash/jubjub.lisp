; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/crypto/ecurve/jubjub" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ jubjub
  :parents (zcash)
  :short "A formalization of Zcash's Jubjub elliptic curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "This curve is defined in our elliptice curve library
     at @('[books]/kestrel/crypto/ecurve'); @(see ecurve::jubjub).
     We may move that material here at some point.
     In any case, we provide some additional material here.
     We also introduce theorems about the prime and coefficients,
     and we disable all of them, including executable counterparts:
     the reason is that we want to treat them
     as algebraic quantities in the proofs,
     avoiding their combination in prime field expressions
     that are carried out by the prime field library's rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection jubjub-a-d-q
  :short "Theorems about Jubjub's
          @($a_\\mathbb{J}$), @($d_\\mathbb{J}$), and  @($q_\\mathbb{J}$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These three constants are defined in [ZPS:5.4.8.3].")
   (xdoc::p
    "These nullary functions are defined in the elliptic curve library.
     Here we prove some relevant theorems about them
     and we disable them completely (including executable counterparts)."))

  (defrule primep-of-jubjub-q
    (rtl::primep (jubjub-q)))

  (defrule fep-of-jubjub-a
    (fep (jubjub-a) (jubjub-q)))

  (defrule fep-of-jubjub-d
    (fep (jubjub-d) (jubjub-q)))

  (defrule jubjub-a-d-different
    (not (equal (jubjub-a) (jubjub-d))))

  (defrule jubjub-a-not-zero
    (not (equal (jubjub-a) 0)))

  (defrule jubjub-d-not-zero
    (not (equal (jubjub-d) 0)))

  (defrule jubjub-q-not-two
    (not (equal (jubjub-q) 2)))

  (in-theory (disable jubjub-q
                      (:e jubjub-q)
                      (:e jubjub-a)
                      (:e jubjub-d))))
