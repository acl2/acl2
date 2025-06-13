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

(defxdoc+ field-inv-checked
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for checked field inversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a field element @($x$) different from 0,
     its inverse @($y$) is obtained via a constraint of the form")
   (xdoc::@[]
    "(x) (y) = (1)")
   (xdoc::p
    "which is equivalent to @($y = 1 / x$) if @($x \\neq 0$).")
   (xdoc::p
    "If @($x$) is 0, the constraint has no solution:
     this is why this is `checked' field inversion."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-inv-checked-spec ((x (pfield::fep x prime))
                                (y (pfield::fep y prime))
                                (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specificaton includes the fact that @('x') is not 0.
     This is consistent with a functional specification of this operation
     that returns an error if @('x') is 0:
     saying that @('y') is equal to that function
     involves saying that the function does not return an error
     (imagine that @(tsee pfield::inv) below is such a function,
     even though it does not return an error,
     but has a guard instead."))
  (and (not (equal x 0))
       (equal y (pfield::inv x prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-inv-checked-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-inv-checked)."))
  (pfcs::parse-def
   "field_inv_checked(x, y) := {
    (x) * (y) == (1)
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

(defsection field-inv-checked-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-inv-checked-circuit)
              :pred field-inv-checked-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-double-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-inv-checked-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (field-inv-checked-pred x y prime)
                    (field-inv-checked-spec x y prime)))
    :enable (field-inv-checked-pred
             field-inv-checked-spec))

  (defruled field-inv-checked-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "field_inv_checked" defs)
                         (field-inv-checked-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime))
             (equal (pfcs::definition-satp
                      "field_inv_checked" defs (list x y) prime)
                    (field-inv-checked-spec x y prime)))
    :in-theory '((:e field-inv-checked-circuit)
                 definition-satp-to-field-inv-checked-pred
                 field-inv-checked-pred-to-spec)))
