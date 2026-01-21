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

(defxdoc+ boolean-not
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for boolean negation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a field element @($x$) representing a boolean
     (i.e. such that the field element is either 0 or 1;
     see @(see boolean-assert)),
     its negation @($y$) is obtained via a constraint of the form")
   (xdoc::@[]
    "(1 - x) (1) = (y)")
   (xdoc::p
    "which defines @($y$) to be 1 if @($x$) is 0, or 0 if @($x$) is 1.
     Thus, @($y$) is boolean (0 or 1) if @($x$) is."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-not-spec ((x (pfield::fep x prime))
                          (y (pfield::fep y prime))
                          (prime primep))
  :guard (bitp x)
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use an @(tsee if).
     An alternative is to use @(tsee logand)."))
  (equal y (if (= x 0) 1 0))

  ///

  (defruled bitp-y-when-boolean-not-spec
    (implies (and (boolean-not-spec x y prime)
                  (bitp x))
             (bitp y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-not-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-not)."))
  (pfcs::parse-def
   "boolean_not(x, y) := {
    (1 - x) * (1) == (y)
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

(defsection boolean-not-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-not-circuit)
              :pred boolean-not-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-not-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-not-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x))
             (equal (boolean-not-pred x y prime)
                    (boolean-not-spec x y prime)))
    :enable (boolean-not-pred
             boolean-not-spec))

  (defruled boolean-not-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "boolean_not") defs)
                         (boolean-not-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x))
             (equal (pfcs::definition-satp
                      (pfname "boolean_not") defs (list x y) prime)
                    (boolean-not-spec x y prime)))
    :in-theory '((:e boolean-not-circuit)
                 (:e name-simple)
                 definition-satp-to-boolean-not-pred
                 boolean-not-pred-to-spec)))
