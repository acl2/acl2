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

(include-book "boolean-xor")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-neq
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for boolean non-equality."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(see boolean-assert)),
     the @(see boolean-xor) circuit can be also used
     to set @($z$) to 0 or 1 depending on
     whether @($x$) and @($y$) are equal or not:")
   (xdoc::@[]
    "\\mathit{boolean\_xor}(x,y,z)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-neq-spec ((x (pfield::fep x prime))
                          (y (pfield::fep y prime))
                          (z (pfield::fep z prime))
                          (prime primep))
  :guard (and (bitp x) (bitp y))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal z (if (= x y) 0 1))

  ///

  (defruled bitp-z-when-boolean-neq-spec
    (implies (and (boolean-neq-spec x y z prime)
                  (bitp x)
                  (bitp y))
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-neq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single relation constraint
     that calls the @(see boolean-xor) circuit."))
  (pfcs::parse-def
   "boolean_neq(x, y, z) := {
      boolean_xor(x, y, z)
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

(defsection boolean-neq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-neq-circuit)
              :pred boolean-neq-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-neq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We expand the boolean non-equality predicate
     to the boolean exclusive disjunction predicate,
     and we use its correctness theorem to rewrite it to its specification.
     We expand both specifications, which are equal.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-neq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-neq-pred x y z prime)
                    (boolean-neq-spec x y z prime)))
    :enable (boolean-neq-pred
             boolean-xor-pred-to-spec
             boolean-neq-spec
             boolean-xor-spec))

  (defruled boolean-neq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (name "boolean_neq") defs)
                         (boolean-neq-circuit))
                  (equal (pfcs::lookup-definition (name "boolean_xor") defs)
                         (boolean-xor-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      (name "boolean_neq") defs (list x y z) prime)
                    (boolean-neq-spec x y z prime)))
    :in-theory '((:e boolean-neq-circuit)
                 (:e boolean-xor-circuit)
                 (:e name)
                 definition-satp-to-boolean-neq-pred
                 boolean-neq-pred-to-spec)))
