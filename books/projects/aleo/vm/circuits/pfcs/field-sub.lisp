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

(defxdoc+ field-sub
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field subtraction."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     their difference @($z$) is obtained via a constraint of the form")
   (xdoc::@[]
    "(x - y) (1) = (z)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-sub-spec ((x (pfield::fep x prime))
                        (y (pfield::fep y prime))
                        (z (pfield::fep z prime))
                        (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal z (pfield::sub x y prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-sub-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-sub)."))
  (pfcs::parse-def
   "field_sub(x, y, z) := {
      (x + -1 * y) * (1) == (z)
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

(defsection field-sub-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-sub-circuit)
              :pred field-sub-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-sub-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-sub-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (field-sub-pred x y z prime)
                    (field-sub-spec x y z prime)))
    :enable (field-sub-pred
             field-sub-spec))

  (defruled field-sub-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "field_sub" defs)
                         (field-sub-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (pfcs::definition-satp
                      "field_sub" defs (list x y z) prime)
                    (field-sub-spec x y z prime)))
    :in-theory '((:e field-sub-circuit)
                 definition-satp-to-field-sub-pred
                 field-sub-pred-to-spec)))
