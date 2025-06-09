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
(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-xor
  :parents (circuits)
  :short "Formalization and verification of the circuit
          for boolean exclusive disjunction."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two field elements @($x$) and @($y$) representing booleans
     (i.e. such that each field element is either 0 or 1;
     see @(tsee boolean-assert)),
     their exclusive disjunction @($z$) is obtained via
     a constraint of the form")
   (xdoc::@[]
    "(2x) (y) = (x + y - z)")
   (xdoc::p
    "which is equivalent to")
   (xdoc::@[]
    "z = x + y -2xy")
   (xdoc::p
    "which defines @($z$) to be
     1 if @($x$) is 1 and @($y$) is 0,
     1 if @($x$) is 0 and @($y$) is 1,
     0 if @($x$) and @($y$) are both 1, and
     0 if @($x$) and @($y$) are both 0.
     Thus, @($z$) is boolean (0 or 1) if both @($x$) and @($y$) are."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-xor-spec ((x (pfield::fep x prime))
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
     An alternative is to use @(tsee logxor)."))
  (equal z (if (= x y) 0 1))

  ///

  (defruled bitp-z-when-boolean-xor-spec
    (implies (and (boolean-xor-spec x y z prime)
                  (bitp x)
                  (bitp y))
             (bitp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-xor-circuit ()
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a PFCS definition with a single equality constraint
     of the form described in @(see boolean-and)."))
  (pfcs::parse-def
   "boolean_xor(x, y, z) := {
      (2 * x) * (y) == (x + y + -1 * z)
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

(defsection boolean-xor-lifting
  :short "Lifting of the circuit to a predicate."

  (pfcs::lift (boolean-xor-circuit)
              :pred boolean-xor-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-xor-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We need to split into cases based on whether the prime is 2 or not.
     This is not too surprising,
     because of the 2 that appears in the constraints,
     which is the same as 0 if the prime happens to be 2.
     It turns out that, if the prime is 2,
     the constraint still works (i.e. it realizes exclusive disjunction);
     but apparently ACL2 needs to consider this case separately.
     We also need to enable bitp for this proof to work.
     We use the prime fields library rules as with other circuits.")
   (xdoc::p
    "The extension to the circuit is boilerplate."))

  (defruled boolean-xor-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (boolean-xor-pred x y z prime)
                    (boolean-xor-spec x y z prime)))
    :cases ((equal prime 2))
    :enable (boolean-xor-pred
             boolean-xor-spec
             bitp))

  (defruled boolean-xor-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition "boolean_xor" defs)
                         (boolean-xor-circuit))
                  (primep prime)
                  (pfield::fep x prime)
                  (pfield::fep y prime)
                  (pfield::fep z prime)
                  (bitp x)
                  (bitp y))
             (equal (pfcs::definition-satp
                      "boolean_xor" defs (list x y z) prime)
                    (boolean-xor-spec x y z prime)))
    :in-theory '((:e boolean-xor-circuit)
                 definition-satp-to-boolean-xor-pred
                 boolean-xor-pred-to-spec)))
