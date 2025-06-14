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

(include-book "field-inv-checked")
(include-book "field-mul")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-div-checked
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for checked field division."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     their quotient @($z$) is obtained
     by combining @(see field-inv-checked) and @(see field-mul)
     to obtain the inverse of @($y$) and multiply it by @($x$):")
   (xdoc::@[]
    "\\begin{array}{l}
     \\mathit{field\_inv\_checked}(y,w) \\\\
     \\mathit{field\_mul}(x,w,z)
     \\end{array}")
   (xdoc::p
    "If @($y$) is 0, the circuit has no solution,
     because @(see field-inv-checked) has no solution:
     this is why this is `checked' field division."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-div-checked-spec ((x (pfield::fep x prime))
                                (y (pfield::fep y prime))
                                (z (pfield::fep z prime))
                                (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specificaton includes the fact that @('y') is not 0.
     This is consistent with a functional specification of this operation
     that returns an error if @('y') is 0:
     saying that @('z') is equal to that function
     involves saying that the function does not return an error
     (imagine that @('pfield::div') below is such a function,
     even though it does not return an error,
     but has a guard instead."))
  (and (not (equal y 0))
       (equal z (pfield::div x y prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-div-checked-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with two relation constraint
     that call the @(see field-inv-checked) and @(see field-mul) circuits.
     This circuit has an internal variable,
     which is the inverse of the divisor."))
  (pfcs::parse-def
   "field_div_checked(x, y, z) := {
    field_inv_checked(y, w),
    field_mul(x, w, z)
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

(defsection field-div-checked-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-div-checked-circuit)
              :pred field-div-checked-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-div-checked-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding the predicate to
     the predicates for the called circuits,
     rewriting those to their specifications,
     and then expand all the specifications to show that they match.
     For that, we need to open @('pfield::div') to expose @('pfield::inv'),
     which is used by the specification for field inversion;
     but we also need to disable a prime fields library rule that interferes.")
   (xdoc::p
    "Completeness is proved by expanding all the specifications,
     the correctness theorems for the called circuits,
     and using the @('suff') theorem to obtain the conclusion.
     We also need to enable @('pfield::div');
     but here there is no need to disable the rule
     disabled in the soundness theorem (see above).")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-div-checked-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (implies (field-div-checked-pred x y z prime)
                      (field-div-checked-spec x y z prime)))
    :enable (field-div-checked-pred
             field-inv-checked-pred-to-spec
             field-mul-pred-to-spec
             field-div-checked-spec
             field-inv-checked-spec
             field-mul-spec
             pfield::div)
    :disable pfield::equal-of-inv)

  (defruled field-div-checked-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (implies (field-div-checked-spec x y z prime)
                      (field-div-checked-pred x y z prime)))
    :use (:instance field-div-checked-pred-suff
                    (w (pfield::inv y prime)))
    :enable (field-div-checked-spec
             field-inv-checked-spec
             field-mul-spec
             field-inv-checked-pred-to-spec
             field-mul-pred-to-spec
             pfield::div))

  (defruled field-div-checked-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (field-div-checked-pred x y z prime)
                    (field-div-checked-spec x y z prime)))
    :use (field-div-checked-soundness
          field-div-checked-completeness))

  (defruled field-div-checked-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "field_div_checked" defs)
                         (field-div-checked-circuit))
                  (equal (pfcs::lookup-definition "field_inv_checked" defs)
                         (field-inv-checked-circuit))
                  (equal (pfcs::lookup-definition "field_mul" defs)
                         (field-mul-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (pfcs::definition-satp
                      "field_div_checked" defs (list x y z) prime)
                    (field-div-checked-spec x y z prime)))
    :in-theory '((:e field-div-checked-circuit)
                 (:e field-inv-checked-circuit)
                 (:e field-mul-circuit)
                 definition-satp-to-field-div-checked-pred
                 field-div-checked-pred-to-spec)))
