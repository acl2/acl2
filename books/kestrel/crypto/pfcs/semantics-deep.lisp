; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-operations")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/crypto/r1cs/fe-listp" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(in-theory (disable rtl::primep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics-deeply-embedded
  :parents (semantics)
  :short "Deeply embedded semantics of PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "The semantics informally described in @(see semantics)
     can be formalized, mathematically, as a function
     with the following characteristics.
     The function takes the following inputs:")
   (xdoc::ol
    (xdoc::li
     "A system of constraints.")
    (xdoc::li
     "A constraint or a list of constraints.")
    (xdoc::li
     "An assignment,
      i.e. a finite map from variables to prime field elements"))
   (xdoc::p
    "The function returns one of the following possible outputs:")
   (xdoc::ul
    (xdoc::li
     "The boolean `true', indicating that,
      given the input system of constraints,
      the input constraint or list of constraints
      is satisfied by the input assignment.")
    (xdoc::li
     "The boolean `false', indicating that,
      given the input system of constraints,
      the input constraint or list of constraints
      is not satisfied by the input assignment.")
    (xdoc::li
     "An error indication, indicating that,
      given the input system of constraints,
      the input constraint or list of constraints
      cannot be evaluated as satisfied or not."))
   (xdoc::p
    "The third output happens when, for instance,
     the constraint or constraints reference
     a variable that is not in the assignment,
     or a relation that is not in the system.
     This should never happen when the system and constraint(s) are "
    (xdoc::seetopic "well-formedness" "well-formed")
    ", which we plan to prove formally.")
   (xdoc::p
    "Attempting to define this function in ACL2 runs into an issue.
     A constraint that is a call of a relation is satisfied
     when the constraints that form the body of the relation are,
     in some assigment that extends the one that assigns
     the actual parameters to the formal parameters.
     This is an existential quantification,
     which is expressed via @(tsee defun-sk) in ACL2,
     but the semantics function is recursive,
     and a mutual recursion cannot involve a @(tsee defun-sk).")
   (xdoc::p
    "To overcome this issue,
     we formalize a logical proof system
     to derive assertions about the semantic function sketched above,
     and we define the semantic function in terms of the proof system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap assignment
  :short "Fixtype of assignments."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are assignments of field elements to variables,
     used to express the semantics of PFCS
     (see @(see semantics-deeply-embedded)).")
   (xdoc::p
    "Since the type of field elements depends on the prime,
     we use natural numbers here,
     which are a superset of every possible prime field.
     This way, we can have a fixtype of assignments
     (recall that fixtypes cannot be parameterized, currently)."))
  :key-type symbol
  :val-type nat
  :pred assignmentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assignment-for-prime-p ((asg assignmentp) (p rtl::primep))
  :returns (yes/no booleanp)
  :short "Check if an assignment is for a prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee assignment),
     that fixtype is defined with natural numbers as range type.
     However, those natural numbers are meant to be prime field elements.
     This predicate says whether all the natural numbers in an assignment
     are in fact elements of the prime field specified by the given prime."))
  (b* ((asg (assignment-fix asg)))
    (or (omap::empty asg)
        (b* (((mv & nat) (omap::head asg)))
          (and (pfield::fep nat p)
               (assignment-for-prime-p (omap::tail asg) p)))))
  :hooks (:fix)
  ///

  (defruled fep-of-cdr-of-in-when-assignment-for-prime-p
    (implies (and (assignmentp asg)
                  (assignment-for-prime-p asg p)
                  (consp (omap::in var asg)))
             (pfield::fep (cdr (omap::in var asg)) p))
    :enable (assignment-for-prime-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-expr ((asg assignmentp) (expr expressionp) (p rtl::primep))
  :guard (assignment-for-prime-p asg p)
  :returns (nat? maybe-natp :hyp (rtl::primep p))
  :short "Evaluate an expression, given an assignment and a prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "In effect, this extends the assignment from variables to expressions.
     If a variable is not in the assignment,
     it is an error, indicated by @('nil').
     The evaluation is in the context of a prime field,
     so a constant expression is reduced modulo the prime.
     An addition or multiplication expression is evaluated recursively,
     propagating errors and combining the results
     with the field addition and multiplication operations.
     If the assignment is for a prime field,
     and the evaluation returns a natural number (not an error),
     that natural number is in the prime field."))
  (expression-case
   expr
   :const (mod expr.value p)
   :var (b* ((pair (omap::in expr.name (assignment-fix asg))))
          (if (consp pair)
              (nfix (cdr pair))
            nil))
   :add (b* ((val1 (eval-expr asg expr.arg1 p))
             ((unless val1) nil)
             (val2 (eval-expr asg expr.arg2 p))
             ((unless val2) nil))
          (pfield::add val1 val2 p))
   :mul (b* ((val1 (eval-expr asg expr.arg1 p))
             ((unless val1) nil)
             (val2 (eval-expr asg expr.arg2 p))
             ((unless val2) nil))
          (pfield::mul val1 val2 p)))
  :measure (expression-count expr)
  :hooks (:fix)
  :verify-guards nil ; done below
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  ///

  (defrule natp-of-eval-expr-when-not-nil
    (implies (and (rtl::primep p)
                  (assignmentp asg)
                  (eval-expr asg expr p))
             (natp (eval-expr asg expr p))))

  (defrule fep-of-eval-expr
    (implies (and (rtl::primep p)
                  (assignmentp asg)
                  (assignment-for-prime-p asg p)
                  (eval-expr asg expr p))
             (pfield::fep (eval-expr asg expr p) p))
    :enable fep-of-cdr-of-in-when-assignment-for-prime-p)

  (verify-guards eval-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-expr-list ((asg assignmentp)
                        (exprs expression-listp)
                        (p rtl::primep))
  :guard (assignment-for-prime-p asg p)
  :returns (mv (okp booleanp)
               (nats nat-listp
                     :hyp (and (rtl::primep p)
                               (assignmentp asg))))
  :short "Lift @(tsee eval-expr) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first result is @('nil') if any expression yields an error,
     in which case the second result is also @('nil').
     Otherwise, the first result is @('t')
     and the second result is the list of natural numbers that
     the expressions evaluate to."))
  (b* (((when (endp exprs)) (mv t nil))
       (val (eval-expr asg (car exprs) p))
       ((unless val) (mv nil nil))
       ((mv okp vals) (eval-expr-list asg (cdr exprs) p))
       ((unless okp) (mv nil nil)))
    (mv t (cons val vals)))
  :hooks (:fix)
  ///

  (defrule fe-listp-of-eval-expr-list
    (implies (and (rtl::primep p)
                  (assignmentp asg)
                  (assignment-for-prime-p asg p)
                  (mv-nth 0 (eval-expr-list asg exprs p)))
             (fe-listp (mv-nth 1 (eval-expr-list asg exprs p)) p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum assertion
  :short "Fixtype of semantic assertions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the assertions mentioned in @(see semantics-deeply-embedded).
     They are essentially logical formulas,
     asserting that the mathematical semantic function
     returns the boolean `true' on given inputs.
     There are four kinds of assertions define here:")
   (xdoc::ul
    (xdoc::li
     "Assertions saying that an assignment makes two expressions equal.
      This is for equality constraints.")
    (xdoc::li
     "Assertions saying that an assignment makes a named relation
      true on given expressions.
      This is for constraints that are
      applications of relations to expressions.")
    (xdoc::li
     "Assertions saying that an assignment makes a constraint true.
      This reduces to the two kinds of assertions above, as defined later,
      but it is needed to treat the two kinds of constraint uniformly.")
    (xdoc::li
     "Assertions saying that an assignment makes a list of constraints true.
      This is where we need, as mentioned above,
      the uniform treatment of the two kinds of constraints."))
   (xdoc::p
    "The components of the assertions defined here
     correspond to the inputs of the mathematical semantic function
     sketched in @(see semantics-deeply-embedded),
     with the exception of the constraint system.
     This is left implicit in the assertions,
     because it would be the same in all of them,
     and so it is provided externally;
     see the definition of the semantic function
     in terms of the proof system."))
  (:equal ((asg assignment)
           (left expression)
           (right expression)))
  (:relation ((asg assignment)
              (name symbol)
              (args expression-list)))
  (:constraint ((asg assignment)
                (constr constraint)))
  (:constraints ((asg assignment)
                 (constrs constraint-list)))
  :pred assertionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum proof-tree
  :short "Fixtype of semantic proof trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides assertions (defined in @(tsee assertion)),
     the proof system includes proofs, more precisely proof trees.
     These are structures that, when properly formed,
     provide a proof of an assertion.
     Here we only define the structure of the proof trees;
     how they prove an assertion is defined later.")
   (xdoc::p
    "A proof tree must have enough information that
     it is easy to check whether it proves an assertion or not.
     We have five kinds of proof trees,
     corresponding to the four kinds of assertions as follows:")
   (xdoc::ul
    (xdoc::li
     "Proof trees that prove equality assertions.
      These are isomorphic to equality assertions,
      since it is easy to check whether an assignment
      makes two expressions the same.
      This kind of proof tree has no subtrees;
      it is found at the leaves of larger proof trees.")
    (xdoc::li
     "Proof trees that prove relation application assertions.
      These consist of the same components of the assertion,
      plus a subtree that must prove the satisfaction of
      the constraints in the body that defines the relation,
      for some assignment that extends the one that assigns
      the values of the expressions to the formal parameters.
      This is formalized later; the above is just a sketch.")
    (xdoc::li
     "Proof trees that prove single constraints.
      These have a single proof tree that depends on the kind of constraint.
      Similarly to the third kind of assertions,
      this third kind of proof trees
      serves to treat proof trees for single constraints uniformly.")
    (xdoc::li
     "Proof trees that prove the empty list of constraints.
      These include assignments so that they can be composed
      with proof trees for non-empty lists of constraints.")
    (xdoc::li
     "Proof trees that prove a non-empty list of constraints.
      These have two subtrees,
      one for the first (single) constraint,
      and one for (the list of) remaining constraints.")))
  (:equal ((asg assignment)
           (left expression)
           (right expression)))
  (:relation ((asg assignment)
              (name symbol)
              (args expression-list)
              (sub proof-tree)))
  (:constraint ((sub proof-tree)))
  (:constraints-nil ((asg assignment)))
  (:constraints-cons ((first proof-tree)
                      (rest proof-tree)))
  :pred proof-treep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum proof-outcome
  :short "Fixtype of semantic proof outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the possible results of executing a proof tree:")
   (xdoc::ul
    (xdoc::li
     "The proof tree provides a valid proof of an assertion.")
    (xdoc::li
     "The proof fails to prove any assertion.")
    (xdoc::li
     "The proof causes an error during execution"))
   (xdoc::p
    "See @(tsee exec-proof-tree)."))
  (:assertion ((get assertion)))
  (:fail ())
  (:error ())
  :pred proof-outcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-proof-tree ((ptree proof-treep) (sys systemp) (p rtl::primep))
  :returns (outcome proof-outcomep)
  :short "Execute a proof tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing a proof tree means checking if provides a valid proof
     and in that case computing the assertion it proves.
     If the proof is invalid, a failure indication is returned
     (this could be extended to include more information in the future).
     If some error occurs during the course of the execution of the proof,
     e.g. a variable is not found in an assignment,
     an error indication is returned;
     this should never happen under suitable well-formedness conditions,
     which we plan to formalize and formally prove.
     Note the difference between a failure outcome,
     where no error occurs but the proof tree is invalid,
     and an error outcome,
     where some error occurs that prevents the establishment of
     whether the proof tree is valid or not.")
   (xdoc::p
    "Besides a proof tree, we need a system,
     which provides a context in which
     the constraints are checked.
     In more detail, the system provided
     the definitions of the named relations.")
   (xdoc::p
    "We also need a prime, which defines the prime field
     with respect to which the constraints are checked.")
   (xdoc::p
    "To execute a proof tree for an equality constraint,
     we simply evaluate the constraint.")
   (xdoc::p
    "To execute a proof tree for a relation application,
     we first evaluate the argument expressions, propagating any errors.
     Then we look up the relation in the system, returning an error if absent.
     Then we execute the proof subtree, propagating error and failures.
     If that succeeds, we check that it proves an assertion saying that
     the body of the relation is satisfied
     with an assignment that extends the one that assigns
     the values of the argument expressions to the relation's formal parameters.
     In other words, the subtree must prove that
     it is possible to extend the assignment of arguments to parameters
     in a way that all the constraints of the relation are satisfied.
     This corresponds to the existential quantification
     discussed in @(see semantics-deeply-embedded),
     in some sense.")
   (xdoc::p
    "To execute a proof tree for a constraint,
     we execute the subtree,
     propagating errors and failures.
     In case of success, we wrap the resulting
     equality or relation application assertion
     into a constraint assertion.")
   (xdoc::p
    "To execute a proof tree for the empty list of constraints,
     we produce a successful outcome with the empty list of constraints.")
   (xdoc::p
    "To execute a proof tree for a non-empty list of constraints,
     we first execute the two subtrees, propagating errors and failures.
     Then we check that
     the first one proves a single constraint,
     the second one proves a list of constraints,
     they both prove the same assignment,
     and we produce an assertion with that assignment
     and with the list of all the constraints."))
  (proof-tree-case
   ptree
   :equal
   (b* (((unless (assignment-for-prime-p ptree.asg p))
         (proof-outcome-error))
        (left (eval-expr ptree.asg ptree.left p))
        ((unless left) (proof-outcome-error))
        (right (eval-expr ptree.asg ptree.right p))
        ((unless right) (proof-outcome-error)))
     (if (equal left right)
         (proof-outcome-assertion
          (make-assertion-equal :asg ptree.asg
                                :left ptree.left
                                :right ptree.right))
       (proof-outcome-fail)))
   :relation
   (b* (((unless (assignment-for-prime-p ptree.asg p))
         (proof-outcome-error))
        ((mv okp vals) (eval-expr-list ptree.asg ptree.args p))
        ((unless okp) (proof-outcome-error))
        (def (lookup-definition ptree.name sys))
        ((unless def) (proof-outcome-error))
        ((definition def) def)
        ((unless (= (len def.para) (len vals)))
         (proof-outcome-error))
        (asg-para-vals (omap::from-lists def.para vals))
        (outcome (exec-proof-tree ptree.sub sys p)))
     (proof-outcome-case
      outcome
      :error (proof-outcome-error)
      :fail (proof-outcome-fail)
      :assertion
      (assertion-case
       outcome.get
       :equal (proof-outcome-fail)
       :relation (proof-outcome-fail)
       :constraint (proof-outcome-fail)
       :constraints
       (if (and (omap::submap asg-para-vals outcome.get.asg)
                (equal def.body outcome.get.constrs))
           (proof-outcome-assertion
            (make-assertion-relation :asg ptree.asg
                                     :name ptree.name
                                     :args ptree.args))
         (proof-outcome-fail)))))
   :constraint
   (b* ((outcome (exec-proof-tree ptree.sub sys p)))
     (proof-outcome-case
      outcome
      :error (proof-outcome-error)
      :fail (proof-outcome-fail)
      :assertion
      (assertion-case
       outcome.get
       :equal (proof-outcome-assertion
               (make-assertion-constraint
                :asg outcome.get.asg
                :constr (make-constraint-equal
                         :left outcome.get.left
                         :right outcome.get.right)))
       :relation (proof-outcome-assertion
                  (make-assertion-constraint
                   :asg outcome.get.asg
                   :constr (make-constraint-relation
                            :name outcome.get.name
                            :args outcome.get.args)))
       :constraint (proof-outcome-fail)
       :constraints (proof-outcome-fail))))
   :constraints-nil
   (proof-outcome-assertion
    (make-assertion-constraints :asg ptree.asg
                                :constrs nil))
   :constraints-cons
   (b* ((outcome1 (exec-proof-tree ptree.first sys p))
        ((when (proof-outcome-case outcome1 :error)) (proof-outcome-error))
        ((when (proof-outcome-case outcome1 :fail)) (proof-outcome-fail))
        (outcome2 (exec-proof-tree ptree.rest sys p))
        ((when (proof-outcome-case outcome2 :error)) (proof-outcome-error))
        ((when (proof-outcome-case outcome2 :fail)) (proof-outcome-fail))
        (asr1 (proof-outcome-assertion->get outcome1))
        (asr2 (proof-outcome-assertion->get outcome2))
        ((unless (assertion-case asr1 :constraint)) (proof-outcome-fail))
        ((unless (assertion-case asr2 :constraints)) (proof-outcome-fail))
        (asg1 (assertion-constraint->asg asr1))
        (asg2 (assertion-constraints->asg asr2))
        ((unless (equal asg1 asg2)) (proof-outcome-fail))
        (constr (assertion-constraint->constr asr1))
        (constrs (assertion-constraints->constrs asr2)))
     (proof-outcome-assertion
      (make-assertion-constraints :asg asg1
                                  :constrs (cons constr constrs)))))
  :measure (proof-tree-count ptree)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk constraint-satp ((asg assignmentp)
                            (constr constraintp)
                            (sys systemp)
                            (p rtl::primep))
  :guard (assignment-for-prime-p asg p)
  :returns (yes/no booleanp)
  :short "Semantic function saying if an assignment satisfies a constraint,
          given a system of constraints and a prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the proof system formalized above,
     defining the semantic function
     discussed in @(see semantics-deeply-embedded)
     is easily done,
     by existentially quantifying over proof trees.
     That is, there must exist a proof tree
     that successfully proves the assertion
     corresponding to the assignment and constraint."))
  (exists (ptree)
          (and (proof-treep ptree)
               (equal (exec-proof-tree ptree sys p)
                      (proof-outcome-assertion
                       (make-assertion-constraint :asg asg :constr constr))))))
