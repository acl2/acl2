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

(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-or
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for boolean (inclusive) disjunction."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(see boolean-assert)),
     their (inclusive) disjunction @($z$) is obtained via
     a constraint of the form")
   (xdoc::@[]
    "(1 - x) (1 - y) = (1 - z)")
   (xdoc::p
    "which defines @($z$) to be 0 if both @($x$) and @($y$) are 0, otherwise 1.
     Thus, @($z$) is boolean (0 or 1) if both @($x$) and @($y$) are.")
   (xdoc::p
    "This has the same form as @(see boolean-and),
     but with each boolean negated (see @(see boolean-not))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-or-spec ((x (pfield::fep x prime))
                         (y (pfield::fep y prime))
                         (z (pfield::fep z prime))
                         (prime primep))
  :guard (and (bitp x) (bitp y))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use an @(tsee if).
     An alternative is to use @(tsee logior)."))
  (equal z (if (and (= x 0) (= y 0)) 0 1))

  ///

  (defruled bitp-z-when-boolean-or-spec
    (implies (and (boolean-or-spec x y z prime)
                  (bitp x)
                  (bitp y))
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-or-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-or).")
   (xdoc::p
    "An alternative definition could be in terms of
     the @(see boolean-and) and @(see boolean-not) circuits,
     but it is simpler to define this as a single equality constraint."))
  (pfcs::parse-def
   "boolean_or(x, y, z) := {
    (1 - x) * (1 - y) == (1 - z)
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

(defsection boolean-or-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-or-circuit)
              :pred boolean-or-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-or-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification
     is proved automatically via the prime fields library rules.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-or-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-or-pred x y z prime)
                    (boolean-or-spec x y z prime)))
    :enable (boolean-or-pred
             boolean-or-spec))

  (defruled boolean-or-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_or" defs)
                         (boolean-or-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      "boolean_or" defs (list x y z) prime)
                    (boolean-or-spec x y z prime)))
    :in-theory '((:e boolean-or-circuit)
                 definition-satp-to-boolean-or-pred
                 boolean-or-pred-to-spec)))
