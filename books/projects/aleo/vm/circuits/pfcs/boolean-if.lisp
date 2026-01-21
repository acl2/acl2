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

(defxdoc+ boolean-if
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for boolean ternary conditional."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given three field elements @($x$), @($y$), and @($z$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(see boolean-assert)),
     the result @($w$) of the ternary conditional
     with test @($x$), `then' branch @($y$), and `else' branch @($z$),
     is obtained via a constraint of the form")
   (xdoc::@[]
    "(x) (y - z) = (w - z)")
   (xdoc::p
    "which works as follows:
     if @($x$) is 0, we have @($w - z = 0$), i.e. @($w = z$);
     if @($x$) is 1, we have @($y - z = w - z$), i.e. @($w = y$).
     Thus, @($w$ is a boolean if all of @($y$) and @($z$) are.")
   (xdoc::p
    "This circuit has the same form as @(tsee field-if)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-if-spec ((x (pfield::fep x prime))
                         (y (pfield::fep y prime))
                         (z (pfield::fep z prime))
                         (w (pfield::fep w prime))
                         (prime primep))
  :guard (and (bitp x) (bitp y) (bitp z))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use an @(tsee if), obviously."))
  (equal w (if (= x 1) y z))

  ///

  (defruled bitp-w-when-boolean-if-spec
    (implies (and (boolean-if-spec x y z w prime)
                  (bitp y)
                  (bitp z))
             (bitp w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-if-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-if)."))
  (pfcs::parse-def
   "boolean_if(x, y, z, w) := {
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

(defsection boolean-if-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-if-circuit)
              :pred boolean-if-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-if-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-if-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep w prime)
                  (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (boolean-if-pred x y z w prime)
                    (boolean-if-spec x y z w prime)))
    :enable (boolean-if-pred
             boolean-if-spec))

  (defruled boolean-if-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition (pfname "boolean_if") defs)
                         (boolean-if-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (pfield::fep w prime)
                  (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (pfcs::definition-satp
                      (pfname "boolean_if") defs (list x y z w) prime)
                    (boolean-if-spec x y z w prime)))
    :in-theory '((:e boolean-if-circuit)
                 (:e name-simple)
                 definition-satp-to-boolean-if-pred
                 boolean-if-pred-to-spec)))
