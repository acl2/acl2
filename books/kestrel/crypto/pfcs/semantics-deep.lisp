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
(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/lists/repeat" :dir :system))

(local (in-theory (disable rtl::primep)))

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
     "A system of constraints, of type @(tsee system).")
    (xdoc::li
     "A constraint, of type @(tsee constraint).")
    (xdoc::li
     "An assignment,
      i.e. a finite map from variables to prime field elements"))
   (xdoc::p
    "The function returns one of the following possible outputs:")
   (xdoc::ul
    (xdoc::li
     "The boolean `true', indicating that,
      given the input system of constraints,
      the input constraint is satisfied by the input assignment.")
    (xdoc::li
     "The boolean `false', indicating that,
      given the input system of constraints,
      the input constraint is not satisfied by the input assignment.")
    (xdoc::li
     "An error indication, indicating that,
      given the input system of constraints,
      the input constraint cannot be evaluated as satisfied or not."))
   (xdoc::p
    "The third output happens when, for instance,
     the constraint references
     a variable that is not in the assignment,
     or a relation that is not in the system.
     This should never happen when the system and constraint are "
    (xdoc::seetopic "well-formedness" "well-formed")
    ", which we plan to prove formally.")
   (xdoc::p
    "Attempting to define this function in ACL2 runs into an issue.
     A constraint that is a call of a relation is satisfied
     when all the constraints that form the body of the relation are,
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist assignment-list
  :short "Fixtype of lists of assignments."
  :elt-type assignment
  :true-listp t
  :elementp-of-nil t
  :pred assignment-listp)

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
          (and (fep nat p)
               (assignment-for-prime-p (omap::tail asg) p)))))
  :hooks (:fix)
  ///

  (defruled fep-of-cdr-of-in-when-assignment-for-prime-p
    (implies (and (assignmentp asg)
                  (assignment-for-prime-p asg p)
                  (consp (omap::in var asg)))
             (fep (cdr (omap::in var asg)) p)))

  (defrule assignment-for-prime-p-of-tail
    (implies (and (assignmentp asg)
                  (assignment-for-prime-p asg p))
             (assignment-for-prime-p (omap::tail asg) p)))

  (defrule assignment-for-prime-p-of-nil
    (assignment-for-prime-p nil p))

  (defrule assignment-for-prime-p-of-update
    (implies (and (assignmentp asg)
                  (assignment-for-prime-p asg p)
                  (fep nat p))
             (assignment-for-prime-p (omap::update var nat asg) p))
    :enable omap::update
    :prep-lemmas
    ((defrule lemma
       (implies (and (fep (cdr pair) p)
                     (assignment-for-prime-p asg p))
                (assignment-for-prime-p (cons pair asg) p))
       :enable (omap::head
                omap::tail)
       :expand ((assignment-for-prime-p (cons pair asg) p))))))

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
             (fep (eval-expr asg expr p) p))
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

(fty::defprod assertion
  :short "Fixtype of semantic assertions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the assertions mentioned in @(see semantics-deeply-embedded).
     They are essentially logical formulas,
     asserting that the mathematical semantic function
     returns the boolean `true' on given inputs.")
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
  ((asg assignment)
   (constr constraint))
  :pred assertionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist assertion-list
  :short "Fixtype of lists of semantic assertions."
  :elt-type assertion
  :true-listp t
  :elementp-of-nil nil
  :pred assertion-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assertion-list ((asgs assignment-listp) (constrs constraint-listp))
  :guard (equal (len asgs) (len constrs))
  :returns (asrs assertion-listp)
  :short "Lift @(tsee assertion) to lists."
  (cond ((endp asgs) nil)
        ((endp constrs) (acl2::impossible))
        (t (cons (assertion (car asgs) (car constrs))
                 (assertion-list (cdr asgs) (cdr constrs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection assertion-list->asg-list ((x assertion-listp))
  :returns (asgs assignment-listp)
  :short "Lift @(tsee assertion->asg) to lists."
  (assertion->asg x)
  ///
  (fty::deffixequiv assertion-list->asg-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection assertion-list->constr-list ((x assertion-listp))
  :returns (asgs constraint-listp)
  :short "Lift @(tsee assertion->constr) to lists."
  (assertion->constr x)
  ///
  (fty::deffixequiv assertion-list->constr-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes proof-trees

  (fty::deftagsum proof-tree
    :short "Fixtype of semantic proof trees."
    :long
    (xdoc::topstring
     (xdoc::p
      "Besides assertions (defined in @(tsee assertion)),
       the proof system includes proofs, more precisely proof trees.
       These are structures that, when properly formed,
       provide proofs of assertions.
       Here we only define the structure of the proof trees;
       how they prove assertions is defined later.")
     (xdoc::p
      "A proof tree must have enough information that
       it is easy to check whether it proves an assertion or not.
       We have two kinds of proof trees:")
     (xdoc::ul
      (xdoc::li
       "Proof trees that prove equality constraint assertions.
        This kind of proof tree has no subtrees;
        it is found at the leaves of larger proof trees.")
      (xdoc::li
       "Proof trees that prove relation application assertions.
        These include subtrees that must prove the satisfaction of
        the constraints in the body that defines the relation,
        for some assignment that extends the one that assigns
        the values of the expressions to the formal parameters;
        the assignment must be the same for all the subtrees.
        This is formalized later; the description above is only a sketch.")))
    (:equal ((asg assignment)
             (left expression)
             (right expression)))
    (:relation ((asg assignment)
                (name symbol)
                (args expression-list)
                (sub proof-tree-list)))
    :pred proof-treep)

  (fty::deflist proof-tree-list
    :short "Fixtype of lists of semantics proof trees."
    :elt-type proof-tree
    :true-listp t
    :elementp-of-nil nil
    :pred proof-tree-listp))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum proof-list-outcome
  :short "Fixtype of semantic proof list outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the possible results of checking a list of proof trees in turn.
     If any tree yields an error or a failure, that is also the outcome.
     Otherwise, all the trees yield assertions,
     so the outcome is a list of assertions."))
  (:assertions ((get assertion-list)))
  (:fail ())
  (:error ())
  :pred proof-list-outcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec-proof-tree
  :short "Execute a proof tree."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing a proof tree means checking if it provides a valid proof,
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
    "Besides a proof tree, we need a system of constraints,
     which provides a context in which the constraints are checked.
     In more detail, the system provides
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
     Then we execute the proof subtrees, propagating errors and failures.
     If the proof subtrees all succeed, they yield a list of assertions.
     We ensure that they all have the same assignment,
     that such an assignment extends the one that assigns
     the values of the argument expressions to the relation's formal parameters,
     and that the constraints are the ones that
     form the body of the named relation.
     In other words, the subtrees must prove that
     it is possible to extend the assignment of arguments to parameters
     in a way that all the constraints of the relation are satisfied.
     This corresponds to the existential quantification
     discussed in @(see semantics-deeply-embedded),
     in some sense.
     We allow relations with an empty body (i.e. no constraints)
     to be proved by an empty list of subtrees;
     note that in this case there is no assignment
     in the assertions proved by the subtrees,
     because they do not prove any assertions in fact."))

  (define exec-proof-tree ((ptree proof-treep) (sys systemp) (p rtl::primep))
    :returns (outcome proof-outcomep)
    (proof-tree-case
     ptree
     :equal
     (b* (((unless (assignment-for-prime-p ptree.asg p)) (proof-outcome-error))
          (left (eval-expr ptree.asg ptree.left p))
          ((unless left) (proof-outcome-error))
          (right (eval-expr ptree.asg ptree.right p))
          ((unless right) (proof-outcome-error)))
       (if (equal left right)
           (proof-outcome-assertion
            (make-assertion :asg ptree.asg
                            :constr (make-constraint-equal :left ptree.left
                                                           :right ptree.right)))
         (proof-outcome-fail)))
     :relation
     (b* (((unless (assignment-for-prime-p ptree.asg p)) (proof-outcome-error))
          ((mv okp vals) (eval-expr-list ptree.asg ptree.args p))
          ((unless okp) (proof-outcome-error))
          (def (lookup-definition ptree.name sys))
          ((unless def) (proof-outcome-error))
          ((definition def) def)
          ((unless (= (len def.para) (len vals))) (proof-outcome-error))
          (asg-para-vals (omap::from-lists def.para vals))
          (outcome (exec-proof-tree-list ptree.sub sys p)))
       (proof-list-outcome-case
        outcome
        :error (proof-outcome-error)
        :fail (proof-outcome-fail)
        :assertions
        (b* ((asgs (assertion-list->asg-list outcome.get))
             (constrs (assertion-list->constr-list outcome.get))
             ((unless (equal constrs def.body)) (proof-outcome-fail))
             ((unless (or (endp asgs)
                          (and (equal asgs (repeat (len asgs) (car asgs)))
                               (omap::submap asg-para-vals (car asgs)))))
              (proof-outcome-fail)))
          (proof-outcome-assertion
           (make-assertion
            :asg ptree.asg
            :constr (make-constraint-relation :name ptree.name
                                              :args ptree.args)))))))
    :measure (proof-tree-count ptree))

  (define exec-proof-tree-list ((ptrees proof-tree-listp)
                                (sys systemp)
                                (p rtl::primep))
    :returns (outcome proof-list-outcomep)
    (b* (((when (endp ptrees)) (proof-list-outcome-assertions nil))
         (outcome (exec-proof-tree (car ptrees) sys p)))
      (proof-outcome-case
       outcome
       :error (proof-list-outcome-error)
       :fail (proof-list-outcome-fail)
       :assertion
       (b* ((outcome1 (exec-proof-tree-list (cdr ptrees) sys p)))
         (proof-list-outcome-case
          outcome1
          :error (proof-list-outcome-error)
          :fail (proof-list-outcome-fail)
          :assertions
          (proof-list-outcome-assertions (cons outcome.get outcome1.get))))))
    :measure (proof-tree-list-count ptrees)
    ///

    (defret len-of-exec-proof-tree-list
      (implies (proof-list-outcome-case outcome :assertions)
               (equal (len (proof-list-outcome-assertions->get outcome))
                      (len ptrees)))))

  :verify-guards nil ; done below
  ///
  (verify-guards exec-proof-tree)

  (fty::deffixequiv-mutual exec-proof-tree))

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
                       (make-assertion :asg asg :constr constr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk constraint-list-satp ((asg assignmentp)
                                 (constrs constraint-listp)
                                 (sys systemp)
                                 (p rtl::primep))
  :guard (assignment-for-prime-p asg p)
  :returns (yes/no booleanp)
  :short "Semantic function saying if an assignment
          satisfies a list of constraints,
          given a system of constraints and a prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee constraint-satp),
     but for lists of constraints."))
  (exists (ptrees)
          (and (proof-tree-listp ptrees)
               (equal (exec-proof-tree-list ptrees sys p)
                      (proof-list-outcome-assertions
                       (assertion-list (repeat (len constrs) asg)
                                       constrs))))))
