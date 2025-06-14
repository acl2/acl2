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
(include-book "boolean-neq")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-assert-neq
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for asserting that two booleans are not equal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(see boolean-assert)),
     we combine the @(see boolean-neq) and @(see boolean-assert-true)
     to constrain @($x$) and @($y$) to be non-equal:")
   (xdoc::@[]
    "\\begin{array}{l}
     \\mathit{boolean\_neq}(x,y,z) \\\\
     \\mathit{boolean\_assert\_true}(z)
     \\end{array}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-neq-spec ((x (pfield::fep x prime))
                                 (y (pfield::fep y prime))
                                 (prime primep))
  :guard (and (bitp x)
              (bitp y))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (/= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-neq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a two relation constraint
     that call the @(see boolean-neq) and @(see boolean-assert-true) circuits.
     This circuit has an internal variable,
     which is the result of @(see boolean-neq)
     and the operand of @(see boolean-assert-true)."))
  (pfcs::parse-def
   "boolean_assert_neq(x, y) := {
    boolean_neq(x, y, z),
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

(defsection boolean-assert-neq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-assert-neq-circuit)
              :pred boolean-assert-neq-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-assert-neq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding
     the existentially quantified boolean non-equality assertion predicate
     to the boolean non-equality and truth assertion predicates,
     using the correcness theorems of the latter two,
     and expanding all three specifications.")
   (xdoc::p
    "Completeness is proved also by expanding
     the boolean non-equality and truth assertion predicates
     and all the specifications,
     but we we use the @('suff') theorem for
     the boolean non-equality assertion predicate.
     The witness for the existential quantification is
     the result of comparing the two operands for non-equality.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-assert-neq-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (implies (boolean-assert-neq-pred x y prime)
                      (boolean-assert-neq-spec x y prime)))
    :enable (boolean-assert-neq-pred
             boolean-neq-pred-to-spec
             boolean-assert-true-pred-to-spec
             boolean-assert-neq-spec
             boolean-neq-spec
             boolean-assert-true-spec))

  (defruled boolean-assert-neq-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (implies (boolean-assert-neq-spec x y prime)
                      (boolean-assert-neq-pred x y prime)))
    :enable (boolean-assert-neq-spec
             boolean-neq-spec
             boolean-assert-true-spec
             boolean-neq-pred-to-spec
             boolean-assert-true-pred-to-spec)
    :use (:instance boolean-assert-neq-pred-suff
                    (z (if (equal x y) 0 1))))

  (defruled boolean-assert-neq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-assert-neq-pred x y prime)
                    (boolean-assert-neq-spec x y prime)))
    :use (boolean-assert-neq-pred-soundness
          boolean-assert-neq-pred-completeness))

  (defruled boolean-assert-neq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_assert_neq" defs)
                         (boolean-assert-neq-circuit))
                  (equal (pfcs::lookup-definition "boolean_assert_true" defs)
                         (boolean-assert-true-circuit))
                  (equal (pfcs::lookup-definition "boolean_neq" defs)
                         (boolean-neq-circuit))
                  (equal (pfcs::lookup-definition "boolean_xor" defs)
                         (boolean-xor-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      "boolean_assert_neq" defs (list x y) prime)
                    (boolean-assert-neq-spec x y prime)))
    :in-theory '((:e boolean-assert-neq-circuit)
                 (:e boolean-assert-true-circuit)
                 (:e boolean-neq-circuit)
                 (:e boolean-xor-circuit)
                 definition-satp-to-boolean-assert-neq-pred
                 boolean-assert-neq-pred-to-spec)))
