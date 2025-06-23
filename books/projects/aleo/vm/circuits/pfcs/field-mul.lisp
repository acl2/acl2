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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-mul
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field multiplication."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     their multiplication @($z$) is obtained via a constraint of the form")
   (xdoc::@[]
    "(x) (y) = (z)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-mul-spec ((x (pfield::fep x prime))
                        (y (pfield::fep y prime))
                        (z (pfield::fep z prime))
                        (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal z (pfield::mul x y prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-mul-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-mul)."))
  (pfcs::parse-def
   "field_mul(x, y, z) := {
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

(defsection field-mul-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-mul-circuit)
              :pred field-mul-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-mul-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically,
     without even using the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-mul-pred-to-spec
    (implies (and (primep p)
                  (pfield::fep x p)
                  (pfield::fep y p)
                  (pfield::fep z p))
             (equal (field-mul-pred x y z prime)
                    (field-mul-spec x y z prime)))
    :enable (field-mul-pred
             field-mul-spec))

  (defruled field-mul-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (name "field_mul") defs)
                         (field-mul-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (pfcs::definition-satp
                      (name "field_mul") defs (list x y z) prime)
                    (field-mul-spec x y z prime)))
    :in-theory '((:e field-mul-circuit)
                 (:e name)
                 definition-satp-to-field-mul-pred
                 field-mul-pred-to-spec)))
