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

(include-book "boolean-assert")

(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/indexed-names" :dir :system)

(local (include-book "../library-extensions/omaps"))
(local (include-book "../library-extensions/osets"))

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-assert-all
  :parents (circuits)
  :short "Formalization and verification of a circuit
          for asserting that zero or more field elements are booleans
          (i.e. 0 or 1)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a family of PFCS relations of the form")
   (xdoc::codeblock
    "boolean_assert_all_<n>(x_0, ..., x_<n-1>) := {
     boolean_assert(x_0),
     ...
     boolean_assert(x_<n-1>)
     }")
   (xdoc::p
    "where @('<n>') is a natural number that parameterizes the relation.
     This relation calls @(see boolean-assert) on each parameter.")
   (xdoc::p
    "Currently our PFCS library does not provide
     a concrete syntax for parameterized PFCS relations.
     So we construct PFCS abstract syntax,
     which we lift ``manually'' (not via the lifter).
     Proofs of correctness are by induction,
     and cover all the infinitely many members of the family."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-all-spec ((xs (pfield::fe-listp xs prime))
                                 (prime primep))
  (declare (ignore prime))
  :returns (yes/no booleanp)
  :short "Specification of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specification is a predicate over a list of field elements.
     The predicate is defined as @(tsee bit-listp),
     i.e. the recognizer of lists of bits."))
  (bit-listp xs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-all-circuit-body ((xs name-listp))
  :returns (constrs pfcs::constraint-listp)
  :short "Construct the defining body of the PFCS relation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of @(see boolean-assert) calls,
     applied to each parameter.
     To facilitate proofs by induction,
     we define this construction over an arbitrary list of variable names,
     which are then instantiated to @('(x_0 ... x_<n-1>)')."))
  (cond ((endp xs) nil)
        (t (cons (pfcall (pfname "boolean_assert") (pfvar (car xs)))
                 (boolean-assert-all-circuit-body (cdr xs)))))

  ///

  (more-returns
   (constrs pfcs::sr1cs-constraint-listp
            :hints (("Goal"
                     :induct t
                     :in-theory (enable pfcs::sr1cs-constraintp)))))

  (defrule constraint-list-vars-of-boolean-assert-all-circuit-body
    (equal (pfcs::constraint-list-vars (boolean-assert-all-circuit-body xs))
           (set::mergesort (name-list-fix xs)))
    :induct t
    :enable (pfcs::constraint-list-vars
             pfcs::constraint-vars
             pfcs::expression-list-vars
             pfcs::expression-vars
             set::mergesort)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-assert-all-circuit ((n natp))
  :returns (pdef pfcs::definitionp)
  :short "Construction of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The construction is parameterized by @('n').")
   (xdoc::p
    "The name of the circuit includes the parameter @('n'),
     so that a larger circuit can include
     different instances of this circuit without conflict.")
   (xdoc::p
    "The parameter list is @('(x_0 ... x_<n-1>)')."))
  (b* ((para (iname-list "x" n)))
    (pfdef (iname "boolean_assert_all" n)
           para
           (boolean-assert-all-circuit-body para)))

  ///

  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp)))))

  (defrule definition->name-of-boolean-assert-all-circuit
    (equal (pfcs::definition->name (boolean-assert-all-circuit n))
           (iname "boolean_assert_all" n)))

  (defrule definition->para-of-boolean-assert-all-circuit
    (equal (pfcs::definition->para (boolean-assert-all-circuit n))
           (iname-list "x" n)))

  (defrule definition->body-of-boolean-assert-all-circuit
    (equal (pfcs::definition->body (boolean-assert-all-circuit n))
           (boolean-assert-all-circuit-body (iname-list "x" n))))

  (defrule definition-free-vars-of-boolean-assert-all-circuit
    (set::emptyp (pfcs::definition-free-vars (boolean-assert-all-circuit n)))
    :enable pfcs::definition-free-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-assert-all-lifting
  :short "Lifting of the circuit to a predicate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The shallowly embedded predicate is defined as
     the conjunction, for each value,
     of the predicate of the @(see boolean-assert) circuit.")
   (xdoc::p
    "To prove the lifting theorem,
     i.e. the correspondence with the deep embedding,
     first we prove a theorem about the constraints in the body.
     This is where the induction is facilitated
     by the construction that takes an arbitrary list of variables,
     as mentioned in @(tsee boolean-assert-all-circuit-body).
     We induct simultaneously on the list of variables and list of values.
     It is important to assume that the list of variables has no duplicates,
     so that the omap built via @(tsee omap::from-lists) has no overwriting,
     and instead associates corresponding elements of the lists.
     To have a sufficient induction hypothesis,
     we need to generalize the theorem to a generic assignment asg,
     assumed to include at least the one built via @(tsee omap::from-lists).
     The lifting theorem says that
     the list of recursively constructed constraints is satisfied iff
     the shallowly embedded @('boolean-assert-all') predicate holds.
     We use the rule @(tsee pfcs::constraint-satp-to-definition-satp)
     to turn the satisfaction of each constraint into
     the satisfaction of the definition of the @(see boolean-assert) circuit,
     which lets us use the lifting theorem
     @('definition-satp-to-boolean-assert-pred') for that circuit.")
   (xdoc::p
    "Using that theorem, we can prove the lifting theorem for the circuit.
     Note that we prove it for a generic number of variables @('n = (len xs)'),
     and we assume that the definitions defs include
     the definition of the circuit determined by that @('n') as parameter.
     We can use the rule @(tsee pfcs::constraint-relation-nofreevars-satp)
     because the circuit has no free variables,
     so we don't need to deal with the existential quantification."))

  (defund boolean-assert-all-pred (xs p)
    (or (endp xs)
        (and (boolean-assert-pred (car xs) p)
             (boolean-assert-all-pred (cdr xs) p))))


  (defruled constraint-list-satp-to-boolean-assert-all-circuit-body
    (implies (and (equal (pfcs::lookup-definition (pfname "boolean_assert")
                                                  defs)
                         (boolean-assert-circuit))
                  (primep prime)
                  (name-listp xs-vars)
                  (no-duplicatesp-equal xs-vars)
                  (pfield::fe-listp xs-vals prime)
                  (equal (len xs-vars) (len xs-vals))
                  (pfcs::assignmentp asg)
                  (pfcs::assignment-wfp asg prime)
                  (omap::submap (omap::from-lists xs-vars xs-vals) asg))
             (equal (pfcs::constraint-list-satp
                     (boolean-assert-all-circuit-body xs-vars) defs asg prime)
                    (boolean-assert-all-pred xs-vals prime)))
    :induct (acl2::cdr-cdr-induct xs-vars xs-vals)
    :enable (boolean-assert-all-circuit-body
             boolean-assert-all-pred
             pfcs::constraint-list-satp-of-cons
             pfcs::constraint-list-satp-of-nil
             pfcs::constraint-satp-to-definition-satp
             pfcs::eval-expr-list
             pfcs::eval-expr
             acl2::not-reserrp-when-natp
             acl2::not-reserrp-when-nat-listp
             definition-satp-to-boolean-assert-pred
             no-duplicatesp-equal
             omap::assoc-of-car-of-supermap-of-from-lists
             omap::submap-of-from-lists-of-cdr-cdr-when-submap-of-from-lists))

  (defruled definition-satp-to-boolean-assert-all
    (implies (and (equal (pfcs::lookup-definition
                          (iname "boolean_assert_all" (len xs))
                          defs)
                         (boolean-assert-all-circuit (len xs)))
                  (equal (pfcs::lookup-definition (pfname "boolean_assert")
                                                  defs)
                         (boolean-assert-circuit))
                  (primep prime)
                  (pfield::fe-listp xs prime))
             (equal (pfcs::definition-satp
                      (iname "boolean_assert_all" (len xs)) defs xs prime)
                    (boolean-assert-all-pred xs prime)))
    :enable (pfcs::definition-satp
              pfcs::constraint-satp-of-relation-when-nofreevars
              pfcs::constraint-relation-nofreevars-satp
              constraint-list-satp-to-boolean-assert-all-circuit-body
              pfcs::eval-expr-list-of-expression-var-list-and-omap-from-lists)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-assert-all-correctness
  :short "Correctness of the circuit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The equivalence between predicate and specification is proved by induction,
     via the equivalence theorem for single booleans
     and the specification predicates.")
   (xdoc::p
    "The extension to the circuit is boilerplate,
     given the lifting theorem."))

  (defruled boolean-assert-all-pred-to-spec
    (implies (and (primep prime)
                  (pfield::fe-listp xs prime))
             (equal (boolean-assert-all-pred xs prime)
                    (bit-listp xs)))
    :induct t
    :enable (boolean-assert-all-pred
             boolean-assert-pred-to-spec
             boolean-assert-spec
             bit-listp))

  (defruled boolean-assert-all-circuit-to-spec
    (implies (and (equal (pfcs::lookup-definition
                          (iname "boolean_assert_all" (len xs))
                          defs)
                         (boolean-assert-all-circuit (len xs)))
                  (equal (pfcs::lookup-definition (pfname "boolean_assert")
                                                  defs)
                         (boolean-assert-circuit))
                  (primep prime)
                  (pfield::fe-listp xs prime))
             (equal (pfcs::definition-satp
                      (iname "boolean_assert_all" (len xs)) defs xs prime)
                    (bit-listp xs)))
    :enable (boolean-assert-all-pred-to-spec
             definition-satp-to-boolean-assert-all)))
