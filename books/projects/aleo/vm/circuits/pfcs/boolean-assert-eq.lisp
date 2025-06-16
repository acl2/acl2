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
(include-book "boolean-eq")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-assert-eq
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for asserting that two booleans are equal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(see boolean-assert)),
     we combine the @(see boolean-eq) and @(see boolean-assert-true)
     to constrain @($x$) and @($y$) to be equal:")
   (xdoc::@[]
    "\\begin{array}{l}
     \\mathit{boolean\_eq(x,y,z) \\\\
     \\mathit{boolean\_assert\_true}(z)
     \\end{array}"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-eq-spec ((x (pfield::fep x prime))
                                (y (pfield::fep y prime))
                                (prime primep))
  :guard (and (bitp x)
              (bitp y))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (= x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-eq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a two relation constraint
     that call the @(see boolean-eq) and @(see boolean-assert-true) circuits.
     This circuit has an internal variable,
     which is the result of @(see boolean-eq)
     and the operand of @(see boolean-assert-true)."))
  (pfcs::parse-def
   "boolean_assert_eq(x, y) := {
    boolean_eq(x, y, z),
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

(defsection boolean-assert-eq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-assert-eq-circuit)
              :pred boolean-assert-eq-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-assert-eq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding
     the existentially quantified boolean equality assertion predicate
     to the boolean equality and truth assertion predicates,
     using the correcness theorems of the latter two,
     and expanding all three specifications.")
   (xdoc::p
    "Completeness is proved also by expanding
     the boolean equality and truth assertion predicates
     and all the specifications,
     but we we use the @('suff') theorem for
     the boolean equality assertion predicate.
     The witness for the existential quantification is
     the result of comparing the two operands for equality.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-assert-eq-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (implies (boolean-assert-eq-pred x y prime)
                      (boolean-assert-eq-spec x y prime)))
    :enable (boolean-assert-eq-pred
             boolean-eq-pred-to-spec
             boolean-assert-true-pred-to-spec
             boolean-assert-eq-spec
             boolean-eq-spec
             boolean-assert-true-spec))

  (defruled boolean-assert-eq-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (implies (boolean-assert-eq-spec x y prime)
                      (boolean-assert-eq-pred x y prime)))
    :enable (boolean-assert-eq-spec
             boolean-eq-spec
             boolean-assert-true-spec
             boolean-eq-pred-to-spec
             boolean-assert-true-pred-to-spec)
    :use (:instance boolean-assert-eq-pred-suff
                    (z (if (equal x y) 1 0))))

  (defruled boolean-assert-eq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-assert-eq-pred x y prime)
                    (boolean-assert-eq-spec x y prime)))
    :use (boolean-assert-eq-pred-soundness
          boolean-assert-eq-pred-completeness))

  (defruled boolean-assert-eq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_assert_eq" defs)
                         (boolean-assert-eq-circuit))
                  (equal (pfcs::lookup-definition "boolean_assert_true" defs)
                         (boolean-assert-true-circuit))
                  (equal (pfcs::lookup-definition "boolean_eq" defs)
                         (boolean-eq-circuit))
                  (equal (pfcs::lookup-definition "boolean_neq" defs)
                         (boolean-neq-circuit))
                  (equal (pfcs::lookup-definition "boolean_not" defs)
                         (boolean-not-circuit))
                  (equal (pfcs::lookup-definition "boolean_xor" defs)
                         (boolean-xor-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      "boolean_assert_eq" defs (list x y) prime)
                    (boolean-assert-eq-spec x y prime)))
    :in-theory '((:e boolean-assert-eq-circuit)
                 (:e boolean-assert-true-circuit)
                 (:e boolean-eq-circuit)
                 (:e boolean-neq-circuit)
                 (:e boolean-not-circuit)
                 (:e boolean-xor-circuit)
                 definition-satp-to-boolean-assert-eq-pred
                 boolean-assert-eq-pred-to-spec)))
