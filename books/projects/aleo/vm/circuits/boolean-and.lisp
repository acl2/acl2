; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-and
  :parents (circuits)
  :short "Formalization and verification of the circuit
          for boolean conjunction."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(tsee boolean-assert)),
     their conjunction @($z$) is obtained via a multiplication of the form")
   (xdoc::@[]
    "(x) (y) = (z)")
   (xdoc::p
    "which defines @($z$) to be 1 if both @($x$) and @($y$) are, otherwise 0.
     Thus, @($z$) is boolean (0 or 1) if both @($x$ and @($y$) are."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-and-spec ((x (pfield::fep x prime))
                          (y (pfield::fep y prime))
                          (z (pfield::fep z prime))
                          (prime primep))
  :guard (and (bitp x) (bitp y))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use an @(tsee if).
     An alterntive is to use @(tsee logand).")
   (xdoc::p
    ""))
  (equal z (if (and (= x 1) (= y 1)) 1 0))

  ///

  (defruled bitp-z-when-boolean-and-spec
    (implies (and (boolean-and-spec x y z prime)
                  (bitp x)
                  (bitp y))
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-and-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-and)."))
  (pfcs::parse-def
   "boolean_and(x, y, z) := {
      (x) * (y) == (z)
    }")

  ///

  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-and-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-and-circuit)
              :pred boolean-and-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-and-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-and-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-and-pred x y z prime)
                    (boolean-and-spec x y z prime)))
    :enable (boolean-and-pred
             boolean-and-spec))

  (defruled boolean-and-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_and" defs)
                         (boolean-and-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      "boolean_and" defs (list x y z) prime)
                    (boolean-and-spec x y z prime)))
    :in-theory '((:e boolean-and-circuit)
                 definition-satp-to-boolean-and-pred
                 boolean-and-pred-to-spec)))
