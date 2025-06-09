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

(defxdoc+ boolean-assert
  :parents (circuits)
  :short "Formalization and verification of the circuit
          for asserting that a field element is a boolean (i.e. 0 or 1)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Booleans are represented as field elements that are
     either 0 (for `false') or 1 (for `true').
     This circuit constrains a variable to be either 0 or 1,
     via a single constrain of the form")
   (xdoc::@[]
    "(1 - x) (x) = (0)")
   (xdoc::p
    "which is satisfied iff @($x = 0$) or @($x = 1$)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-spec ((x (pfield::fep x prime))
                             (prime primep))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specification is a predicate over a single field element.
     The predicate is defined as the built-in @(tsee bitp),
     i.e. the recognizer of bits."))
  (bitp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-assert)."))
  (pfcs::parse-def
   "boolean_assert(x) := {
        (1 + -1 * x) * (x) == (0)
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

(defsection boolean-assert-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-assert-circuit)
              :pred boolean-assert-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-assert-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-assert-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime))
             (equal (boolean-assert-pred x prime)
                    (boolean-assert-spec x prime)))
    :enable (boolean-assert-pred
             boolean-assert-spec))

  (defruled boolean-assert-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_assert" defs)
                         (boolean-assert-circuit))
                  (primep prime)
                  (pfield::fep x prime))
             (equal (pfcs::definition-satp
                      "boolean_assert" defs (list x) prime)
                    (boolean-assert-spec x prime)))
    :in-theory '((:e boolean-assert-circuit)
                 definition-satp-to-boolean-assert-pred
                 boolean-assert-pred-to-spec)))
