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

(include-book "field-neq")
(include-book "boolean-not")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-eq
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field non-equality."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     their equality can be checked, and put into a boolean result @($z$),
     by negating the non-equality of @($x$) and @($y$):")
   (xdoc::@[]
    "\\begin{array}{l}
     \\mathit{field\_neq(x,y,w) \\\\
     \\mathit{boolean\_not(w,z)
     \\end{array}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-eq-spec ((x (pfield::fep x prime))
                       (y (pfield::fep y prime))
                       (z (pfield::fep z prime))
                       (prime primep))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal z (if (= x y) 1 0))

  ///

  (defruled bitp-z-when-field-eq-spec
    (implies (field-eq-spec x y z prime)
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-eq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a two relation constraint
     that call the @(see field-neq) and @(see boolean-not) circuits.
     This circuit has an internal variable,
     which is the result of @(see field-neq)
     and the operand of @(see boolean-not)."))
  (pfcs::parse-def
   "field_eq(x, y, z) := {
    field_neq(x, y, w),
    boolean_not(w, z)
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

(defsection field-eq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-eq-circuit)
              :pred field-eq-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-eq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding
     the existentially quantified field equality predicate
     to the boolean negation and non-equality predicates,
     using the correcness theorems of the latter two,
     and expanding all three specifications.")
   (xdoc::p
    "Completeness is proved also by expanding
     the boolean negation and non-equality predicates
     and all the specifications,
     but we we use the @('suff') theorem for the field equality predicate.
     The witness for the existential quantification is
     the result of comparing the two operands for non-equality.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-eq-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (implies (field-eq-pred x y z prime)
                      (field-eq-spec x y z prime)))
    :enable (field-eq-pred
             field-neq-pred-to-spec
             boolean-not-pred-to-spec
             field-eq-spec
             field-neq-spec
             boolean-not-spec))

  (defruled field-eq-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (implies (field-eq-spec x y z prime)
                      (field-eq-pred x y z prime)))
    :enable (field-eq-spec
             field-neq-spec
             boolean-not-spec
             field-neq-pred-to-spec
             boolean-not-pred-to-spec)
    :use (:instance field-eq-pred-suff
                    (w (if (equal x y) 0 1))))

  (defruled field-eq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (field-eq-pred x y z prime)
                    (field-eq-spec x y z prime)))
    :use (field-eq-pred-soundness
          field-eq-pred-completeness))

  (defruled field-eq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "field_eq" defs)
                         (field-eq-circuit))
                  (equal (pfcs::lookup-definition "field_neq" defs)
                         (field-neq-circuit))
                  (equal (pfcs::lookup-definition "boolean_not" defs)
                         (boolean-not-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (pfcs::definition-satp
                      "field_eq" defs (list x y z) prime)
                    (field-eq-spec x y z prime)))
    :in-theory '((:e field-eq-circuit)
                 (:e field-neq-circuit)
                 (:e boolean-not-circuit)
                 definition-satp-to-field-eq-pred
                 field-eq-pred-to-spec)))
