; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-operations")
(include-book "pfield-lib-ext")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "kestrel/fty/nat-result" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (in-theory (disable primep)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (pfcs)
  :short "Semantics of PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "A named relation denotes
     a predicate over a cartesian product of the prime field,
     where the number of factors of the cartesian product
     is the arity of the relation.
     The predicate holds exactly on the tuples of prime field elements
     that, when assigned to the parameters of the relation,
     satisfy all the constraints that define the relation.
     An equality constraint is satisfied
     when its evaluated left and right sides are equal.
     A relation application in the defining body of another one is satisfied
     when the predicate it denotes holds on the prime field elements
     that result from evaluating its argument expressions.
     There must be no recursion in the relation definitions
     for this to be well-defined.
     The body of a relation definition may include variables
     that are not among the formal parameters:
     these are regarded as existentially quantified,
     i.e. the predicate denoted by the relation holds on a tuple
     when there exist values for those extra variables that,
     together with the values of the tuple, satisfy all the constraints.")
   (xdoc::p
    "The semantics informally described above
     can be formalized, mathematically, as a function
     with the following characteristics.
     This mathematical semantic function takes the following inputs:")
   (xdoc::ol
    (xdoc::li
     "A constraint, of type @(tsee constraint).")
    (xdoc::li
     "A list of definitions, of type @(tsee definition-list).")
    (xdoc::li
     "An assignment,
      i.e. a finite map from variables to prime field elements.")
    (xdoc::li
     "The prime."))
   (xdoc::p
    "The mathematical semantic function
     returns one of the following possible outputs:")
   (xdoc::ul
    (xdoc::li
     "The boolean `true', indicating that,
      given the input list of definitions,
      the input constraint is satisfied by the input assignment.")
    (xdoc::li
     "The boolean `false', indicating that,
      given the input list of definitions,
      the input constraint is not satisfied by the input assignment.")
    (xdoc::li
     "An error, indicating that,
      given the input list of definitions,
      the input constraint cannot be evaluated as satisfied or not."))
   (xdoc::p
    "The third output happens when, for instance,
     the constraint references
     a variable that is not in the assignment,
     or a relation that is not in the list of definitions.
     This should never happen when the list of definitions is "
    (xdoc::seetopic "well-formedness" "well-formed")
    ", as we plan to prove formally.")
   (xdoc::p
    "Attempting to define this mathematical semantic function in ACL2
     runs into an issue.
     A constraint that is a call of a relation is satisfied
     when all the constraints that form the body of the relation are satisfied,
     in some assignment that extends the one that assigns
     the actual parameters to the formal parameters.
     This is an existential quantification,
     which is expressed via @(tsee defun-sk) in ACL2,
     but the mathematical semantic function we are describing is recursive,
     and a mutual recursion cannot involve a @(tsee defun-sk) in ACL2.")
   (xdoc::p
    "To overcome this issue,
     we formalize a logical proof system
     to derive assertions about the mathematical semantic function,
     and then we define the function in ACL2 in terms of the proof system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap assignment
  :short "Fixtype of assignments."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are assignments of field elements to variables,
     used to express the semantics of PFCSes
     (see @(see semantics)).")
   (xdoc::p
    "Since the type of field elements depends on the prime,
     we use natural numbers here,
     which are a superset of every possible prime field.
     This way, we can have a fixtype of assignments
     (recall that fixtypes cannot be parameterized, currently)."))
  :key-type string
  :val-type nat
  :pred assignmentp
  ///

  (defrule natp-of-cdr-of-in-when-assignmentp-type
    (implies (and (assignmentp asg)
                  (omap::assoc str asg))
             (natp (cdr (omap::assoc str asg))))
    :rule-classes :type-prescription)

  (defrule assignmentp-of-from-lists
    (implies (and (string-listp keys)
                  (nat-listp vals)
                  (equal (len keys) (len vals)))
             (assignmentp (omap::from-lists keys vals)))
    :enable omap::from-lists))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist assignment-list
  :short "Fixtype of lists of assignments."
  :elt-type assignment
  :true-listp t
  :elementp-of-nil t
  :pred assignment-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assignment-wfp ((asg assignmentp) (p primep))
  :returns (yes/no booleanp)
  :short "Check if an assignment is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee assignment),
     that fixtype is defined with natural numbers as range type.
     However, those natural numbers are meant to be prime field elements.
     This predicate says whether all the natural numbers in an assignment
     are in fact elements of the prime field specified by the given prime."))
  (b* ((asg (assignment-fix asg)))
    (or (omap::emptyp asg)
        (b* (((mv & nat) (omap::head asg)))
          (and (fep nat p)
               (assignment-wfp (omap::tail asg) p)))))
  :hooks (:fix)
  ///

  (defruled fep-of-cdr-of-in-when-assignment-wfp
    (implies (and (assignmentp asg)
                  (assignment-wfp asg p)
                  (consp (omap::assoc var asg)))
             (fep (cdr (omap::assoc var asg)) p)))

  (defrule assignment-wfp-of-tail
    (implies (and (assignmentp asg)
                  (assignment-wfp asg p))
             (assignment-wfp (omap::tail asg) p)))

  (defrule assignment-wfp-of-nil
    (assignment-wfp nil p))

  (defrule assignment-wfp-of-update
    (implies (and (assignmentp asg)
                  (assignment-wfp asg p)
                  (fep nat p))
             (assignment-wfp (omap::update var nat asg) p))
    :enable omap::update
    :prep-lemmas
    ((defrule lemma
       (implies (and (fep (cdr pair) p)
                     (assignment-wfp asg p))
                (assignment-wfp (cons pair asg) p))
       :enable (omap::head
                omap::tail)
       :expand ((assignment-wfp (cons pair asg) p)))))

  (defrule assignment-wfp-of-update*
    (implies (and (assignmentp asg-new)
                  (assignmentp asg-old)
                  (assignment-wfp asg-new p)
                  (assignment-wfp asg-old p))
             (assignment-wfp (omap::update* asg-new asg-old) p))
    :enable omap::update*)

  (defrule assignment-wfp-of-delete
    (implies (and (assignmentp asg)
                  (assignment-wfp asg p))
             (assignment-wfp (omap::delete var asg) p))
    :enable omap::delete)

  (defrule assignment-wfp-of-delete*
    (implies (and (assignmentp asg)
                  (assignment-wfp asg p))
             (assignment-wfp (omap::delete* vars asg) p))
    :enable omap::delete*)

  (defrule assignment-wfp-of-from-lists
    (implies (and (string-listp keys)
                  (fe-listp vals p)
                  (equal (len keys) (len vals)))
             (assignment-wfp (omap::from-lists keys vals) p))
    :induct t
    :enable (len
             omap::from-lists
             pfield::nat-listp-when-fe-listp))

  (defruled fep-of-lookup-when-assignment-wfp
    (implies (and (assignmentp asg)
                  (assignment-wfp asg prime)
                  (omap::assoc var asg))
             (pfield::fep (omap::lookup var asg) prime))
    :enable (omap::lookup
             fep-of-cdr-of-in-when-assignment-wfp))

  (defruled fe-listp-of-list-lookup-when-assignment-wfp
    (implies (and (assignmentp asg)
                  (assignment-wfp asg prime)
                  (omap::list-in vars asg))
             (pfield::fe-listp (omap::list-lookup vars asg) prime))
    :induct t
    :enable (omap::list-lookup
             omap::list-in
             fep-of-lookup-when-assignment-wfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-expr ((expr expressionp) (asg assignmentp) (p primep))
  :guard (assignment-wfp asg p)
  :returns (nat nat-resultp :hyp (primep p))
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
     that natural number is in the prime field.")
   (xdoc::p
    "We prove that evaluating an expression with an assignment
     that has an added variable that is not in the expression,
     is like evaluating the expression with the assignment
     without the added variable."))
  (expression-case
   expr
   :const (mod expr.value p)
   :var (b* ((pair (omap::assoc expr.name (assignment-fix asg))))
          (if (consp pair)
              (nfix (cdr pair))
            (reserr nil)))
   :neg (b* (((ok val) (eval-expr expr.arg asg p)))
          (neg val p))
   :add (b* (((ok val1) (eval-expr expr.arg1 asg p))
             ((ok val2) (eval-expr expr.arg2 asg p)))
          (add val1 val2 p))
   :sub (b* (((ok val1) (eval-expr expr.arg1 asg p))
             ((ok val2) (eval-expr expr.arg2 asg p)))
          (sub val1 val2 p))
   :mul (b* (((ok val1) (eval-expr expr.arg1 asg p))
             ((ok val2) (eval-expr expr.arg2 asg p)))
          (mul val1 val2 p)))
  :measure (expression-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix)
  :verify-guards nil ; done below
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  ///

  (defrule fep-of-eval-expr
    (implies (and (primep p)
                  (assignmentp asg)
                  (assignment-wfp asg p)
                  (not (reserrp (eval-expr expr asg p))))
             (fep (eval-expr expr asg p) p))
    :enable fep-of-cdr-of-in-when-assignment-wfp)

  (verify-guards eval-expr)

  (defruled eval-expr-of-omap-update-of-var-not-in-expr
    (implies (and (stringp var)
                  (natp val)
                  (assignmentp asg)
                  (not (set::in var (expression-vars expr))))
             (equal (eval-expr expr (omap::update var val asg) p)
                    (eval-expr expr asg p)))
    :induct t
    :enable (eval-expr expression-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-expr-list ((exprs expression-listp)
                        (asg assignmentp)
                        (p primep))
  :guard (assignment-wfp asg p)
  :returns (nats nat-list-resultp :hyp (primep p))
  :short "Lift @(tsee eval-expr) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that evaluating a list of expressions with an assignment
     that has an added variable that is not in the list of expressions,
     is like evaluating the list of expressions with the assignment
     without the added variable.")
   (xdoc::p
    "We prove that evaluating a list of distinct variables (as expressions)
     with an assignment that assigns values from a list
     to the variables in the same order,
     yields those values, in the same order."))
  (b* (((when (endp exprs)) nil)
       ((ok val) (eval-expr (car exprs) asg p))
       ((ok vals) (eval-expr-list (cdr exprs) asg p)))
    (cons val vals))
  :hooks (:fix)
  :prepwork
  ((local
    (in-theory
     (enable acl2::natp-when-nat-resultp-and-not-reserrp
             acl2::nat-listp-when-nat-list-resultp-and-not-reserrp))))
  ///

  (defrule fe-listp-of-eval-expr-list
    (implies (and (primep p)
                  (assignmentp asg)
                  (assignment-wfp asg p)
                  (not (reserrp (eval-expr-list exprs asg p))))
             (fe-listp (eval-expr-list exprs asg p) p)))

  (defret len-of-eval-expr-list
    (implies (nat-listp nats)
             (equal (len nats)
                    (len exprs)))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defruled eval-expr-list-of-omap-udpate-of-var-not-in-exprs
    (implies (and (stringp var)
                  (natp val)
                  (assignmentp asg)
                  (not (set::in var (expression-list-vars exprs))))
             (equal (eval-expr-list exprs (omap::update var val asg) p)
                    (eval-expr-list exprs asg p)))
    :induct t
    :enable (eval-expr-list
             expression-list-vars
             eval-expr-of-omap-update-of-var-not-in-expr))

  (defruled eval-expr-list-of-expression-var-list-and-omap-from-lists
    (implies (and (string-listp vars)
                  (no-duplicatesp-equal vars)
                  (fe-listp vals p)
                  (equal (len vars)
                         (len vals)))
             (equal (eval-expr-list (expression-var-list vars)
                                    (omap::from-lists vars vals)
                                    p)
                    vals))
    :induct (acl2::cdr-cdr-induct vars vals)
    :enable (len
             eval-expr-list
             eval-expr
             no-duplicatesp-equal
             omap::from-lists
             acl2::not-reserrp-when-nat-listp
             eval-expr-list-of-omap-udpate-of-var-not-in-exprs))

  (defruled not-reserrp-of-eval-expr-list-of-atom
    (implies (and (primep p)
                  (atom exprs))
             (not (reserrp (eval-expr-list exprs asg p)))))

  (defruled reserrp-of-eval-expr-list-of-cons
    (implies (primep p)
             (equal (reserrp (eval-expr-list (cons expr exprs) asg p))
                    (or (reserrp (eval-expr expr asg p))
                        (reserrp (eval-expr-list exprs asg p)))))
    :enable (acl2::not-reserrp-when-nat-listp
             acl2::natp-when-nat-resultp-and-not-reserrp
             acl2::nat-listp-when-nat-list-resultp-and-not-reserrp))

  (defruled reserrp-of-eval-expr-list-of-append
    (implies (primep p)
             (equal (reserrp (eval-expr-list (append exprs1 exprs2) asg p))
                    (or (reserrp (eval-expr-list exprs1 asg p))
                        (reserrp (eval-expr-list exprs2 asg p)))))
    :induct t
    :enable (append
             not-reserrp-of-eval-expr-list-of-atom
             reserrp-of-eval-expr-list-of-cons)
    :disable eval-expr-list)

  (defruled eval-expr-list-of-cons-when-not-error
    (implies (and (not (reserrp (pfcs::eval-expr expr asg p)))
                  (not (reserrp (pfcs::eval-expr-list exprs asg p))))
             (equal (eval-expr-list (cons expr exprs) asg p)
                    (cons (eval-expr expr asg p)
                          (eval-expr-list exprs asg p)))))

  (defruled eval-expr-list-of-append-when-not-error
    (implies (and (primep p)
                  (not (reserrp (pfcs::eval-expr-list exprs1 asg p)))
                  (not (reserrp (pfcs::eval-expr-list exprs2 asg p))))
             (equal (eval-expr-list (append exprs1 exprs2) asg p)
                    (append (eval-expr-list exprs1 asg p)
                            (eval-expr-list exprs2 asg p))))
    :induct t
    :enable (append
             reserrp-of-eval-expr-list-of-append)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod assertion
  :short "Fixtype of semantic assertions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the assertions mentioned in @(see semantics).
     They are essentially logical formulas,
     asserting that the mathematical semantic function
     returns the boolean `true' on the given inputs.")
   (xdoc::p
    "The components of the assertions defined here
     correspond to the inputs of the mathematical semantic function
     sketched in @(see semantics),
     with the exception of the list of definitions.
     This is left implicit in the assertions,
     because it would be the same in all of them,
     and so it is provided externally;
     see @(tsee constraint-satp)."))
  ((asg assignment)
   (constr constraint))
  :pred assertionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist assertion-list
  :short "Fixtype of lists of semantic assertions."
  :elt-type assertion
  :true-listp t
  :elementp-of-nil nil
  :pred assertion-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection assertion-list->asg-list ((x assertion-listp))
  :returns (asgs assignment-listp)
  :short "Lift @(tsee assertion->asg) to lists."
  (assertion->asg x)
  ///
  (fty::deffixequiv assertion-list->asg-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection assertion-list->constr-list ((x assertion-listp))
  :returns (constrs constraint-listp)
  :short "Lift @(tsee assertion->constr) to lists."
  (assertion->constr x)
  ///
  (fty::deffixequiv assertion-list->constr-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assertion-list-from ((asgs assignment-listp) (constrs constraint-listp))
  :guard (equal (len asgs) (len constrs))
  :returns (asrs assertion-listp)
  :short "Lift @(tsee assertion) to lists."
  (cond ((endp asgs) nil)
        ((endp constrs) (acl2::impossible))
        (t (cons (assertion (car asgs) (car constrs))
                 (assertion-list-from (cdr asgs) (cdr constrs)))))
  :guard-hints (("Goal" :in-theory (enable len)))
  :hooks (:fix)
  ///

  (defrule assertion-list->asg-list-of-assertion-list-from
    (implies (equal (len asgs) (len constrs))
             (equal (assertion-list->asg-list
                     (assertion-list-from asgs constrs))
                    (assignment-list-fix asgs)))
    :induct t
    :enable (assertion-list->asg-list len))

  (defrule assertion-list->constr-list-of-assertion-list-from
    (implies (equal (len asgs) (len constrs))
             (equal (assertion-list->constr-list
                     (assertion-list-from asgs constrs))
                    (constraint-list-fix constrs)))
    :induct t
    :enable (assertion-list->constr-list len))

  (defrule assertion-list-from-of-assertion-list->asg/constr-list
    (implies (assertion-listp assertions)
             (equal (assertion-list-from
                     (assertion-list->asg-list assertions)
                     (assertion-list->constr-list assertions))
                    assertions))
    :enable (assertion-list->asg-list
             assertion-list->constr-list))

  (defrule len-of-assertion-list-from
    (equal (len (assertion-list-from asgs constrs))
           (min (len asgs) (len constrs)))
    :induct t
    :enable (len min)))

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
       how they prove assertions is defined in @(tsee exec-proof-tree).")
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
        the values of the expressions to the formal parameters.
        Let @('asgpara') be the assignment that assigns
        the values of the expressions to the formal parameters,
        and let @('asgsub') the assignment that extends @('asgpara')
        and that must satisfy all the constraints that define the relation.
        Note that @('asgpara') and @('asgsub') are different from
        the assignment @('asg') that is
        the homonymous component in the proof tree,
        i.e. the one that must satisfy the relation.
        The assignment @('asgsub') is specified indirectly in the proof tree,
        via the @('asgfree') component, which is the difference
        between @('asgsub') and @('asgpara'):
        the domain of @('asgfree') must be
        disjoint from the parameters of the relation,
        and must provide mappings from the non-parameter variables
        used in the constraints of the relation.
        All of this is formalized later;
        the description just given is only a sketch.")))
    (:equal ((asg assignment)
             (left expression)
             (right expression)))
    (:relation ((asg assignment)
                (name string)
                (args expression-list)
                (sub proof-tree-list)
                (asgfree assignment)))
    :pred proof-treep)

  (fty::deflist proof-tree-list
    :short "Fixtype of lists of semantics proof trees."
    :elt-type proof-tree
    :true-listp t
    :elementp-of-nil nil
    :pred proof-tree-listp)

  :prepwork ((local (in-theory (enable nfix)))))

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
     which we plan to formally specify and prove.
     Note the difference between a failure outcome,
     where no error occurs but the proof tree is invalid,
     and an error outcome,
     where some error occurs that prevents the establishment of
     whether the proof tree is valid or not.")
   (xdoc::p
    "Besides a proof tree, we need a list of definitions,
     which provides a context in which the constraints are checked.")
   (xdoc::p
    "We also need a prime, which defines the prime field
     with respect to which the constraints are checked.")
   (xdoc::p
    "To execute a proof tree for an equality constraint,
     we simply evaluate the constraint.")
   (xdoc::p
    "To execute a proof tree for a relation application,
     we first evaluate the argument expressions, propagating any errors.
     Then we look up the relation in the list of definitions,
     returning an error if absent.
     Then we execute the proof subtrees, propagating errors and failures.
     If the proof subtrees all succeed, they yield a list of assertions.
     We ensure that they all have the same assignment,
     specifically the one that is obtained by extending,
     with the assignment @('asgfree') that is the component of the proof tree,
     the assignment @('asgpara') that assigns
     the values of the argument expressions to the relation's formal parameters.
     We require @('asgfree') to have as keys
     exactly the free variables of the relation;
     this implies that the keys are disjoint from @('asgpara').
     We ensure that the constraints are the ones that
     form the body of the named relation.
     In other words, the subtrees must prove that
     it is possible to extend the assignment of arguments to parameters
     in a way that all the constraints of the relation are satisfied.
     This corresponds to the existential quantification
     discussed in @(see semantics),
     in some suitable sense.
     We allow relations with an empty body (i.e. no constraints)
     to be proved by an empty list of subtrees;
     note that in this case there is no use of @('asgfree')
     (which may just be @('nil')),
     because the subtrees do not prove any assertions in this case."))

  (define exec-proof-tree ((ptree proof-treep)
                           (defs definition-listp)
                           (p primep))
    :returns (outcome proof-outcomep)
    (proof-tree-case
     ptree
     :equal
     (b* (((unless (assignment-wfp ptree.asg p)) (proof-outcome-error))
          (left (eval-expr ptree.left ptree.asg p))
          ((unless (natp left)) (proof-outcome-error))
          (right (eval-expr ptree.right ptree.asg p))
          ((unless (natp right)) (proof-outcome-error)))
       (if (equal left right)
           (proof-outcome-assertion
            (make-assertion :asg ptree.asg
                            :constr (make-constraint-equal :left ptree.left
                                                           :right ptree.right)))
         (proof-outcome-fail)))
     :relation
     (b* (((unless (assignment-wfp ptree.asg p))
           (proof-outcome-error))
          (vals (eval-expr-list ptree.args ptree.asg p))
          ((unless (nat-listp vals)) (proof-outcome-error))
          (def (lookup-definition ptree.name defs))
          ((unless def) (proof-outcome-error))
          ((definition def) def)
          ((unless (= (len def.para) (len vals))) (proof-outcome-error))
          (asgpara (omap::from-lists def.para vals))
          ((unless (assignment-wfp ptree.asgfree p))
           (proof-outcome-error))
          ((unless (equal (omap::keys ptree.asgfree)
                          (definition-free-vars def)))
           (proof-outcome-fail))
          (asgsub (omap::update* ptree.asgfree asgpara))
          (outcome (exec-proof-tree-list ptree.sub defs p)))
       (proof-list-outcome-case
        outcome
        :error (proof-outcome-error)
        :fail (proof-outcome-fail)
        :assertions
        (b* ((asgs (assertion-list->asg-list outcome.get))
             (constrs (assertion-list->constr-list outcome.get))
             ((unless (equal constrs def.body)) (proof-outcome-fail))
             ((unless (equal asgs (repeat (len asgs) asgsub)))
              (proof-outcome-fail)))
          (proof-outcome-assertion
           (make-assertion
            :asg ptree.asg
            :constr (make-constraint-relation :name ptree.name
                                              :args ptree.args)))))))
    :measure (proof-tree-count ptree))

  (define exec-proof-tree-list ((ptrees proof-tree-listp)
                                (defs definition-listp)
                                (p primep))
    :returns (outcome proof-list-outcomep)
    (b* (((when (endp ptrees)) (proof-list-outcome-assertions nil))
         (outcome (exec-proof-tree (car ptrees) defs p)))
      (proof-outcome-case
       outcome
       :error (proof-list-outcome-error)
       :fail (proof-list-outcome-fail)
       :assertion
       (b* ((outcome1 (exec-proof-tree-list (cdr ptrees) defs p)))
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
                      (len ptrees)))
      :hints (("Goal" :in-theory (enable len)))))

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below
  ///
  (verify-guards exec-proof-tree)

  (fty::deffixequiv-mutual exec-proof-tree)

  (defrule proof-tree-equal-assignment-is-assertion-assignment
    (implies (proof-tree-case ptree :equal)
             (b* ((outcome (exec-proof-tree ptree defs p)))
               (implies (proof-outcome-case outcome :assertion)
                        (equal (assertion->asg
                                (proof-outcome-assertion->get outcome))
                               (proof-tree-equal->asg ptree)))))
    :expand (exec-proof-tree ptree defs p))

  (defrule proof-tree-relation-assignment-is-assertion-assignment
    (implies (proof-tree-case ptree :relation)
             (b* ((outcome (exec-proof-tree ptree defs p)))
               (implies (proof-outcome-case outcome :assertion)
                        (equal (assertion->asg
                                (proof-outcome-assertion->get outcome))
                               (proof-tree-relation->asg ptree)))))
    :expand (exec-proof-tree ptree defs p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk constraint-satp ((constr constraintp)
                            (defs definition-listp)
                            (asg assignmentp)
                            (p primep))
  :guard (assignment-wfp asg p)
  :returns (yes/no booleanp)
  :short "Semantic function checking if a constaint is satisfied,
          given a list of definitions, an assignment, and a prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the proof system formalized above,
     defining the semantic function
     discussed in @(see semantics)
     is easily done,
     by existentially quantifying over proof trees.
     That is, there must exist a proof tree
     that successfully proves the assertion
     corresponding to the assignment and constraint."))
  (exists (ptree)
          (and (proof-treep ptree)
               (equal (exec-proof-tree ptree defs p)
                      (proof-outcome-assertion
                       (make-assertion :asg asg :constr constr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk constraint-list-satp ((constrs constraint-listp)
                                 (defs definition-listp)
                                 (asg assignmentp)
                                 (p primep))
  :guard (assignment-wfp asg p)
  :returns (yes/no booleanp)
  :short "Semantic function saying if an assignment
          satisfies a list of constraints,
          given a list of definitions and a prime field."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee constraint-satp),
     but for lists of constraints."))
  (exists (ptrees)
          (and (proof-tree-listp ptrees)
               (equal (exec-proof-tree-list ptrees defs p)
                      (proof-list-outcome-assertions
                       (assertion-list-from (repeat (len constrs) asg)
                                            constrs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-satp ((sys systemp) (asg assignmentp) (p primep))
  :guard (assignment-wfp asg p)
  :returns (yes/no booleanp)
  :short "Check if an assignment satisfies a system."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the constraints in the system must be satisfied,
     in the context of the definitions in the system."))
  (constraint-list-satp (system->constraints sys)
                        (system->definitions sys)
                        asg
                        p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-satp ((name stringp)
                         (defs definition-listp)
                         (vals (fe-listp vals p))
                         (p primep))
  :returns (yes/no booleanp)
  :short "Check if a sequence of prime field elements
          satisfies a named PFCS definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We find the definition with the given name,
     to obtain its parameters.
     We form an assignment of the prime field elements to the parameters,
     in order, and we check if this assignment satisfies
     the constraint consisting of
     a call of the definition on its parameters.")
   (xdoc::p
    "This is a convenient abbreviation
     for expressing the satisfiability of a definition."))
  (b* ((def (lookup-definition name defs))
       ((unless def) nil)
       (para (definition->para def))
       ((unless (= (len vals) (len para))) nil)
       (asg (omap::from-lists para vals))
       (constr (make-constraint-relation
                :name name
                :args (expression-var-list para))))
    (constraint-satp constr defs asg p))
  :guard-hints (("Goal" :in-theory (enable pfield::nat-listp-when-fe-listp))))
