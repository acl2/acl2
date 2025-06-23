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

(defxdoc+ field-if
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for field ternary conditional."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a field element @($x$) representing a boolean
     (i.e. such that it is either 0 or 1; see @(see boolean-assert)),
     and given two field elements @($y$) and @($z$),
     the result @($w$) of the ternary conditional
     with test @($x$), `then' branch @($y$), and `else' branch @($z$),
     is obtained via a constraint of the form")
   (xdoc::@[]
    "(x) (y - z) = (w - z)")
   (xdoc::p
    "which works as follows:
     if @($x$) is 0, we have @($w - z = 0$), i.e. @($w = z$);
     if @($x$) is 1, we have @($y - z = w - z$), i.e. @($w = y$).")
   (xdoc::p
    "This circuit has the same form as @(tsee boolean-if)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-if-spec ((x (pfield::fep x prime))
                       (y (pfield::fep y prime))
                       (z (pfield::fep z prime))
                       (w (pfield::fep w prime))
                       (prime primep))
  :guard (bitp x)
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use an @(tsee if), obviously."))
  (equal w (if (= x 1) y z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define field-if-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see field-if)."))
  (pfcs::parse-def
   "field_if(x, y, z, w) := {
    (x) * (y - z) == (w - z)
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

(defsection field-if-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (field-if-circuit)
              :pred field-if-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection field-if-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled field-if-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep w prime)
                  (bitp x))
             (equal (field-if-pred x y z w prime)
                    (field-if-spec x y z w prime)))
    :enable (field-if-pred
             field-if-spec))

  (defruled field-if-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (name "field_if") defs)
                         (field-if-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep w prime)
                  (bitp x))
             (equal (pfcs::definition-satp
                      (name "field_if") defs (list x y z w) prime)
                    (field-if-spec x y z w prime)))
    :in-theory '((:e field-if-circuit)
                 (:e name)
                 definition-satp-to-field-if-pred
                 field-if-pred-to-spec)))
