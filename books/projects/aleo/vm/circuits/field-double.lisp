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

(defxdoc+ field-double
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field doubling."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a field element @($x$),
     its double @($y$) is obtained via a constraint of the form")
   (xdoc::@[]
    "(x + x) (1) = (y)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-double-spec ((x (pfield::fep x prime))
                           (y (pfield::fep y prime))
                           (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal y (pfield::add x x prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-double-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-double)."))
  (pfcs::parse-def
   "field_double(x, y) := {
    (x + x) * (1) == (y)
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

(defsection field-double-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-double-circuit)
              :pred field-double-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-double-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-double-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (field-double-pred x y prime)
                    (field-double-spec x y prime)))
    :enable (field-double-pred
             field-double-spec))

  (defruled field-double-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "field_double" defs)
                         (field-double-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (pfcs::definition-satp
                      "field_double" defs (list x y) prime)
                    (field-double-spec x y prime)))
    :in-theory '((:e field-double-circuit)
                 definition-satp-to-field-double-pred
                 field-double-pred-to-spec)))
