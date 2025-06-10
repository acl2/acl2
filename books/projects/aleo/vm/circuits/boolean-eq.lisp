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

(include-book "boolean-neq")
(include-book "boolean-not")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-eq
  :parents (circuits)
  :short "Formalization and verification of the circuit
          for boolean non-equality."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(see boolean-assert)),
     their equality can be checked, and put into a boolean result @($z$),
     by negating the non-equality of @($x$) and @($y$)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-eq-spec ((x (pfield::fep x prime))
                         (y (pfield::fep y prime))
                         (z (pfield::fep z prime))
                         (prime primep))
  :guard (and (bitp x) (bitp y))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal z (if (= x y) 1 0))

  ///

  (defruled bitp-z-when-boolean-eq-spec
    (implies (and (boolean-eq-spec x y z prime)
                  (bitp x)
                  (bitp y))
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-eq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a two relation constraint
     that call the @(see boolean-neq) and @(see boolean-not) circuits.
     This circuit has an internal variable,
     which is the result of @(see boolean-neq)
     and the operand of @(see boolean-not)."))
  (pfcs::parse-def
   "boolean_eq(x, y, z) := {
      boolean_neq(x, y, w),
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

(defsection boolean-eq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-eq-circuit)
              :pred boolean-eq-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-eq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding
     the existentially quantified boolean equality predicate
     to the boolean negation and non-equality predicates,
     using the correcness theorems of the latter two,
     and expanding all three specifications.")
   (xdoc::p
    "Completeness is proved also by expanding
     the boolean equality predicate and all the specifications,
     but we we use the @('suff') theorem for the boolean equality predicate.
     The witness for the existential quantification is
     the result of comparing the two operands for non-equality.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-eq-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (implies (boolean-eq-pred x y z prime)
                      (boolean-eq-spec x y z prime)))
    :enable (boolean-eq-pred
             boolean-neq-pred-to-spec
             boolean-not-pred-to-spec
             boolean-eq-spec
             boolean-neq-spec
             boolean-not-spec))

  (defruled boolean-eq-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (implies (boolean-eq-spec x y z prime)
                      (boolean-eq-pred x y z prime)))
    :enable (boolean-eq-spec
             boolean-neq-spec
             boolean-not-spec
             boolean-neq-pred-to-spec
             boolean-not-pred-to-spec)
    :use (:instance boolean-eq-pred-suff
                    (w (if (equal x y) 0 1))))

  (defruled boolean-eq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-eq-pred x y z prime)
                    (boolean-eq-spec x y z prime)))
    :use (boolean-eq-pred-soundness
          boolean-eq-pred-completeness))

  (defruled boolean-eq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_eq" defs)
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
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      "boolean_eq" defs (list x y z) prime)
                    (boolean-eq-spec x y z prime)))
    :in-theory '((:e boolean-eq-circuit)
                 (:e boolean-neq-circuit)
                 (:e boolean-not-circuit)
                 (:e boolean-xor-circuit)
                 definition-satp-to-boolean-eq-pred
                 boolean-eq-pred-to-spec)))
