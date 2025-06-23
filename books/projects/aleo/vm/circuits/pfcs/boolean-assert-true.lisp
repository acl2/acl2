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

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-assert-true
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for asserting that a boolean is true."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a field element @($x$) representing a boolean
     (i.e. such that the field element is either 0 or 1;
     see @(see boolean-assert)),
     this circuit constrains it to be `true`, i.e. to be 1,
     via a single constraint of the form")
   (xdoc::@[]
    "(x) (1) = (1)")
   (xdoc::p
    "which defines @($y$) to be 1 if @($x$) is 0, or 0 if @($x$) is 1.
     Thus, @($y$) is boolean (0 or 1) if @($x$) is.")
   (xdoc::p
    "This could be a more general to assert that a field element is 1.
     We may replace this circuit with that one at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-true-spec ((x (pfield::fep x prime))
                                  (prime primep))
  :guard (bitp x)
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (= x 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-true-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-assert-true)."))
  (pfcs::parse-def
   "boolean_assert_true(x) := {
    (x) * (1) == (1)
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

(defsection boolean-assert-true-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-assert-true-circuit)
              :pred boolean-assert-true-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-assert-true-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-assert-true-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (bitp x))
             (equal (boolean-assert-true-pred x prime)
                    (boolean-assert-true-spec x prime)))
    :enable (boolean-assert-true-pred
             boolean-assert-true-spec))

  (defruled boolean-assert-true-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "boolean_assert_true")
                                                  defs)
                         (boolean-assert-true-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (bitp x))
             (equal (pfcs::definition-satp
                      (pfname "boolean_assert_true") defs (list x) prime)
                    (boolean-assert-true-spec x prime)))
    :in-theory '((:e boolean-assert-true-circuit)
                 (:e name-simple)
                 definition-satp-to-boolean-assert-true-pred
                 boolean-assert-true-pred-to-spec)))
