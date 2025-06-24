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

(defxdoc+ field-neq
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field non-equality."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$),
     their non-equality is calculated via constraints of the form")
   (xdoc::@[]
    "\\begin{array}{l}
     (x - y) (w) = (z) \\\\
     (x - y) (1 - z) = (0)
     \\end{array}")
   (xdoc::p
    "If @($x = y$), the first constraint forces @($z = 0$),
     and the second constraint disappears;
     if @($x \\neq y$), the second constraint forces @($z = 1$),
     and the fiest constraint becomes @($w = z / (x - y)$).
     In other words, @($z$) is 1 or 0 depending on whether
     @($x$) and @($y$) are non-equal or equal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-neq-spec ((x (pfield::fep x prime))
                        (y (pfield::fep y prime))
                        (z (pfield::fep z prime))
                        (prime primep))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  (equal z (if (= x y) 0 1))

  ///

  (defruled bitp-z-when-field-neq-spec
    (implies (field-neq-spec x y z prime)
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-neq-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-neq)."))
  (pfcs::parse-def
   "field_neq(x, y, z) := {
    (x - y) * (w) == (z),
    (x - y) * (1 - z) == (0)
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

(defsection field-neq-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-neq-circuit)
               :pred field-neq-pred
               :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-neq-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Soundness is proved by expanding predicate and specification,
     but we need to disable two distributive rules
     that interfere with the proof.")
   (xdoc::p
    "Completeness is proved by expanding the specification
     and then using the @('suff') theorem for the predicate.
     The witness is 0 if @('x') and @('y') are equal,
     otherwise it is the quotient of @('z') and @('x - y').
     We also need to disable a distributive rule that interferes.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-neq-pred-soundness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (implies (field-neq-pred x y z prime)
                      (field-neq-spec x y z prime)))
    :enable (field-neq-pred
             field-neq-spec)
    :disable (pfield::mul-of-add-arg1
              pfield::mul-of-add-arg2))

  (defruled field-neq-pred-completeness
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (implies (field-neq-spec x y z prime)
                      (field-neq-pred x y z prime)))
    :enable field-neq-spec
    :use (:instance field-neq-pred-suff
                    (w (if (equal x y)
                           0
                         (pfield::div z (pfield::sub x y prime) prime))))
    :disable pfield::mul-of-add-arg1)

  (defruled field-neq-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (field-neq-pred x y z prime)
                    (field-neq-spec x y z prime)))
    :use (field-neq-pred-soundness
          field-neq-pred-completeness))

  (defruled field-neq-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "field_neq") defs)
                         (field-neq-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime))
             (equal (pfcs::definition-satp
                      (pfname "field_neq") defs (list x y z) prime)
                    (field-neq-spec x y z prime)))
    :in-theory '((:e field-neq-circuit)
                 (:e name-simple)
                 definition-satp-to-field-neq-pred
                 field-neq-pred-to-spec)))
