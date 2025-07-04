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

(include-book "field-mul")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-square
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field squaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a field element @($x$),
     its square @($y$) is obtained via a a multiplication:")
   (xdoc::@[]
    "\\mathit{field\_mul(x,x,y)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-square-spec ((x (pfield::fep x prime))
                           (y (pfield::fep y prime))
                           (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal y (pfield::mul x x prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-square-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-square)."))
  (pfcs::parse-def
   "field_square(x, y) := {
    field_mul(x, x, y)
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

(defsection field-square-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-square-circuit)
              :pred field-square-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-square-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically,
     using the correctness theorem for the @(see field-mul).")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-square-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (field-square-pred x y prime)
                    (field-square-spec x y prime)))
    :enable (field-square-pred
             field-mul-pred-to-spec
             field-square-spec
             field-mul-spec))

  (defruled field-square-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "field_square") defs)
                         (field-square-circuit))
                  (equal (pfcs::lookup-definition (pfname "field_mul") defs)
                         (field-mul-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (pfcs::definition-satp
                      (pfname "field_square") defs (list x y) prime)
                    (field-square-spec x y prime)))
    :in-theory '((:e field-square-circuit)
                 (:e field-mul-circuit)
                 (:e name-simple)
                 definition-satp-to-field-square-pred
                 field-square-pred-to-spec)))
