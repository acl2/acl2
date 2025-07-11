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

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ field-div-unchecked
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for unchecked field division."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     such that @($y$) is not 0,
     their quotient @($z$) is obtained via a constraint")
   (xdoc::@[]
    "(z) (y) = (x)")
   (xdoc::p
    "This assumes @($y \\neq 0$),
     in which case the constraint is equivalent to @($z = x / y$).
     If @($y = 0$) and @($x \\neq 0$),
     the constraint has no solution;
     but if @($y = x = 0$), the constraint is satisfied
     and the result @($z$) is unconstrained.
     Thus, this circuit must be used only if @($y$) is knownn to be non-zero
     (e.g. as a postcondition for some previous operation);
     this is why this is `unchecked' field division.
     Because of the indeterminacy of @($z$) when @($x = y = 0$),
     this circuit cannot represent a deterministic computation
     of @($z$) from @($x$) and @($y$), unless @($y \\neq 0$)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-div-unchecked-spec ((x (pfield::fep x prime))
                                  (y (pfield::fep y prime))
                                  (z (pfield::fep z prime))
                                  (prime primep))
  :guard (not (equal y 0))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specificaton assumes the fact that @('y') is not 0;
     this is in the guard.
     This is consistent with the division being `unchecked'."))
  (equal z (pfield::div x y prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-div-unchecked-circuit ()
  :returns (pdef pfcs::definitionp)
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-div-unchecked)."))
  (pfcs::parse-def
   "field_div_unchecked(x, y, z) := {
    (z) * (y) == (x)
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

(defsection field-div-unchecked-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-div-unchecked-circuit)
              :pred field-div-unchecked-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-div-unchecked-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-div-unchecked-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (not (equal y 0)))
             (equal (field-div-unchecked-pred x y z prime)
                    (field-div-unchecked-spec x y z prime)))
    :enable (field-div-unchecked-pred
             field-div-unchecked-spec))

  (defruled field-div-unchecked-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "field_div_unchecked")
                                                  defs)
                         (field-div-unchecked-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (not (equal y 0)))
             (equal (pfcs::definition-satp
                      (pfname "field_div_unchecked") defs (list x y z) prime)
                    (field-div-unchecked-spec x y z prime)))
    :in-theory '((:e field-div-unchecked-circuit)
                 (:e name-simple)
                 definition-satp-to-field-div-unchecked-pred
                 field-div-unchecked-pred-to-spec)))
