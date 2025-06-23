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

(include-book "boolean-assert-true")
(include-book "field-neq")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-assert-neq
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for asserting that two field elements are equal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     we combine the @(see field-neq) and @(see boolean-assert-true)
     to constrain @($x$) and @($y$) to be equal:")
   (xdoc::@[]
    "\\begin{array}{l}
     \\mathit{field\_eq}(x,y,z) \\\\
     \\mathit{boolean\_assert\_true}(z)
     \\end{array}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-assert-neq-spec ((x (pfield::fep x prime))
                               (y (pfield::fep y prime))
                               (prime primep))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (/= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-assert-neq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a two relation constraint
     that call the @(see field-neq) and @(see boolean-assert-true) circuits.
     This circuit has an internal variable,
     which is the result of @(see field-neq)
     and the operand of @(see boolean-assert-true)."))
  (pfcs::parse-def
   "field_assert_neq(x, y) := {
    field_neq(x, y, z),
    boolean_assert_true(z)
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

(defsection field-assert-neq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-assert-neq-circuit)
              :pred field-assert-neq-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-assert-neq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding
     the existentially quantified field equality assertion predicate
     to the field equality and truth assertion predicates,
     using the correcness theorems of the latter two,
     and expanding all three specifications.")
   (xdoc::p
    "Completeness is proved also by expanding
     the field equality and truth assertion predicates
     and all the specifications,
     but we we use the @('suff') theorem for
     the field equality assertion predicate.
     The witness for the existential quantification is
     the result of comparing the two operands for equality.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-assert-neq-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (implies (field-assert-neq-pred x y prime)
                      (field-assert-neq-spec x y prime)))
    :enable (field-assert-neq-pred
             field-neq-pred-to-spec
             boolean-assert-true-pred-to-spec
             field-assert-neq-spec
             field-neq-spec
             boolean-assert-true-spec))

  (defruled field-assert-neq-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (implies (field-assert-neq-spec x y prime)
                      (field-assert-neq-pred x y prime)))
    :enable (field-assert-neq-spec
             field-neq-spec
             boolean-assert-true-spec
             field-neq-pred-to-spec
             boolean-assert-true-pred-to-spec)
    :use (:instance field-assert-neq-pred-suff
                    (z (if (equal x y) 0 1))))

  (defruled field-assert-neq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (field-assert-neq-pred x y prime)
                    (field-assert-neq-spec x y prime)))
    :use (field-assert-neq-pred-soundness
          field-assert-neq-pred-completeness))

  (defruled field-assert-neq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (name "field_assert_neq") defs)
                         (field-assert-neq-circuit))
                  (equal (pfcs::lookup-definition (name "boolean_assert_true") defs)
                         (boolean-assert-true-circuit))
                  (equal (pfcs::lookup-definition (name "field_neq") defs)
                         (field-neq-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (pfcs::definition-satp
                      (name "field_assert_neq") defs (list x y) prime)
                    (field-assert-neq-spec x y prime)))
    :in-theory '((:e field-assert-neq-circuit)
                 (:e boolean-assert-true-circuit)
                 (:e field-neq-circuit)
                 (:e name)
                 definition-satp-to-field-assert-neq-pred
                 field-assert-neq-pred-to-spec)))
