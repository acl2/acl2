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

(defxdoc+ field-inv-flagged
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for flagged field inversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not yet implemented in snarkVM.")
   (xdoc::p
    "Given a field element @($x$),
     the constraints")
   (xdoc::@[]
    "\\begin{array}{l}
     (x) (w) = (1 - e) \\\\
     (x) (e) = (0) \\\\
     (w) (1 - e) = (y)
     \\end{array}")
   (xdoc::p
    "work as follows:
     if @($x \\neq 0$),
     the second constraint becomes @($e = 0$),
     the first constraint becomes @($w = 1 / x$),
     and the third constraint becomes @($y = w = 1 / x$).
     if @($x = 0$),
     the second constraint disappears,
     the first constraint becomes @($e = 1$),
     and the third constraint becomes @($y = 0$).
     In other words,
     @($e$) is an error flag,
     signaling whether the inverse of @($x$) is defined (0) or not (1):
     if the error flag is 0, @($y$) is the inverse of @($x$);
     if the error flag is 1, @($y$) is totalized to be 0,
     and @($w$) can be anything."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-inv-flagged-spec ((x (pfield::fep x prime))
                                (y (pfield::fep y prime))
                                (e (pfield::fep e prime))
                                (prime primep))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (and (equal y (if (equal x 0) 0 (pfield::inv x prime)))
       (equal e (if (equal x 0) 1 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-inv-flagged-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with the three equality constraints
     described in @(see field-inv-flagged)."))
  (pfcs::parse-def
   "field_inv_flagged(x, y, e) := {
    (x) * (w) == (1 - e),
    (x) * (e) == (0),
    (w) * (1 - e) == (y)
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

(defsection field-inv-flagged-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-inv-flagged-circuit)
              :pred field-inv-flagged-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-inv-flagged-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved automatically
     via the prime field library rules.")
   (xdoc::p
    "Completeness is proved via the @('suff') theorem
     for the existentially quantified predicate.
     As witness for the internal variable @($w$),
     we use the inverse of @($x$) if @($x \\neq 0$),
     otherwise we use 0 (but other values would work for this case).")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-inv-flagged-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep e prime))
             (implies (field-inv-flagged-pred x y e prime)
                      (field-inv-flagged-spec x y e prime)))
    :enable (field-inv-flagged-pred
             field-inv-flagged-spec))

  (defruled field-inv-flagged-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep e prime))
             (implies (field-inv-flagged-spec x y e prime)
                      (field-inv-flagged-pred x y e prime)))
    :enable field-inv-flagged-spec
    :use (:instance field-inv-flagged-pred-suff
                    (w (if (equal x 0) 0 (pfield::inv x prime)))))

  (defruled field-inv-flagged-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep e prime))
             (equal (field-inv-flagged-pred x y e prime)
                    (field-inv-flagged-spec x y e prime)))
    :use (field-inv-flagged-pred-soundness
          field-inv-flagged-pred-completeness))

  (defruled field-inv-flagged-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (name "field_inv_flagged") defs)
                         (field-inv-flagged-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep e prime))
             (equal (pfcs::definition-satp
                      (name "field_inv_flagged") defs (list x y e) prime)
                    (field-inv-flagged-spec x y e prime)))
    :in-theory '((:e field-inv-flagged-circuit)
                 (:e name)
                 definition-satp-to-field-inv-flagged-pred
                 field-inv-flagged-pred-to-spec)))
