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

(defxdoc+ field-div-flagged
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for flagged field division."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not yet implemented in snarkVM.")
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     the constraints")
   (xdoc::@[]
    "\\begin{array}{l}
     (y) (w) = (1 - e) \\\\
     (y) (e) = (0) \\\\
     (x) (w) = (z) \\\\
     (z) (e) = (0)
     \\end{array}")
   (xdoc::p
    "work as follows:
     if @($y \\neq 0$),
     the second constraint becomes @($e = 0$),
     the first constraint becomes @($w = 1 / y$),
     the third constraint becomes @($z = x w = x / y$),
     and the fourth constraint disappears;
     if @($y = 0$),
     the second constraint disappears,
     the first constraint becomes @($e = 1$),
     the third constraint becomes @($y = 0$),
     and the fourth constraint becomes @($z = 0$).
     In other words,
     @($e$) is an error flag,
     signaling whether the division of @($x$) by @($y$)
     is defined (0) or not (1):
     if the error flag is 0, @($x$) is the quotient of @($x$) and @($y$);
     if the error flag is 1, @($z$) is totalized to be 0,
     and @($w$) can be anything.")
   (xdoc::p
    "Note the similarity with @(see field-inv-flagged)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-div-flagged-spec ((x (pfield::fep x prime))
                                (y (pfield::fep y prime))
                                (z (pfield::fep z prime))
                                (e (pfield::fep z prime))
                                (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (and (equal z (if (equal y 0) 0 (pfield::div x y prime)))
       (equal e (if (equal y 0) 1 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-div-flagged-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with the three equality constraints
     described in @(see field-div-flagged)."))
  (pfcs::parse-def
   "field_div_flagged(x,y,z,e) := {
    (y) * (w) == (1 - e),
    (y) * (e) == (0),
    (x) * (w) == (z),
    (z) * (e) == (0)
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

(defsection field-div-flagged-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-div-flagged-circuit)
              :pred field-div-flagged-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-div-flagged-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding the predicate and specification,
     as well as @('pfield::div') to expose @('pfield::inv'),
     and we need a @(':use') hint to apply a theorem in the right way.")
   (xdoc::p
    "Completeness is proved by expanding all the specifications,
     the correctness theorems for the called circuits,
     and using the @('suff') theorem to obtain the conclusion.
     We also need to enable @('pfield::div');
     but here there is no need to disable the rule
     disabled in the soundness theorem (see above).")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-div-flagged-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep e prime))
             (implies (field-div-flagged-pred x y z e prime)
                      (field-div-flagged-spec x y z e prime)))
    :enable (field-div-flagged-pred
             field-div-flagged-spec
             pfield::div)
    :use (:instance pfield::equal-of-inv
                    (a y)
                    (b (field-div-flagged-pred-witness x y z e prime))
                    (p prime))
    :disable pfield::equal-of-inv)

  (defruled field-div-flagged-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep e prime))
             (implies (field-div-flagged-spec x y z e prime)
                      (field-div-flagged-pred x y z e prime)))
    :enable (field-div-flagged-spec
             pfield::div)
    :use (:instance field-div-flagged-pred-suff
                    (w (if (equal y 0) 0 (pfield::inv y prime)))))

  (defruled field-div-flagged-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep e prime))
             (equal (field-div-flagged-pred x y z e prime)
                    (field-div-flagged-spec x y z e prime)))
    :use (field-div-flagged-soundness
          field-div-flagged-completeness))

  (defruled field-div-flagged-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "field_div_flagged" defs)
                         (field-div-flagged-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep e prime))
             (equal (pfcs::definition-satp
                      "field_div_flagged" defs (list x y z e) prime)
                    (field-div-flagged-spec x y z e prime)))
    :in-theory '((:e field-div-flagged-circuit)
                 definition-satp-to-field-div-flagged-pred
                 field-div-flagged-pred-to-spec)))
