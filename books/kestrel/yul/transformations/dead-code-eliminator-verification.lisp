; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "dead-code-eliminator")
(include-book "../language/dynamic-semantics")

(include-book "kestrel/std/util/defund-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dead-code-eliminator-verification
  :parents (dead-code-eliminator)
  :short "Formal verification of correctness of
          the @('DeadCodeEliminator') transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We verify the correctness of the transformation
     as formalized in ACL2 in @(see dead-code-eliminator).")
   (xdoc::p
    "We prove that the elimination of dead code performed by the transformation
     does not affect the dynamic semantics of the code,
     i.e. the code calculates the same outputs for the same inputs
     (essentially; more on this below).
     In the Yul context, inputs must be understood as
     (parts of) the computation state,
     and outputs must be understood as
     expression results as well as (parts of) the computation state.")
   (xdoc::p
    "We prove correctness theorems
     for all the execution functions in the dynamic semantics:
     a theorem for executing expressions,
     a theorem for executing statements,
     and so on.
     This is natural, given that the proof is by mutual induction.
     These execution functions
     have slightly different argument and result types,
     but they all take an initial computation state as argument,
     and they all return a possibly modified computation state as result,
     along with values for expressions (see @(tsee eoutcome))
     and modes for statements (see @(tsee soutcome)).")
   (xdoc::p
    "Roughly speaking, we prove theorems of the form")
   (xdoc::codeblock
    "(exec (xform ast) cstate) = (exec ast cstate)")
   (xdoc::p
    "where @('exec') is one of the execution functions
     (e.g. @(tsee exec-statement)),
     @('ast') is an AST of Yul abstract syntax
     (e.g. a value of type @(tsee statement)),
     @('xform') is the function that transforms @('ast')
     (e.g. @(tsee statement-dead)),
     and @('cstate') is a computation state.
     But the actual formal assertion we prove is slightly different,
     for two reasons explained below.")
   (xdoc::p
    "The first reason is that the execution functions
     also take function environments as arguments,
     which contain function bodies that must be transformed.
     Thus, we define transformation functions on function environments,
     and we refine the formulation of our theorems to")
   (xdoc::codeblock
    "(exec (xform ast) cstate (xform funenv)) = (exec ast state funenv)")
   (xdoc::p
    "The second reason, and refinement of the theorems,
     has to do with error results,
     which may be returned by the defensive execution functions.
     The error values include information about AST pieces
     and the ACL2 call stack (see @(tsee fty::defresult)),
     which causes a dependency of error values
     on more than just the input/output behavior of ACL2 functions,
     but also on the ASTs executed and the specific calls.
     Since the @('DeadCodeEliminator') transformation
     removes certain pieces of ASTs,
     some functions may return slightly different error values
     when run on @('(xform ast)') vs. @('ast').
     The difference is inessential from a semantic point of view.
     Thus, we define equivalence relations on execution results,
     which weaken equality to accommodate slightly different errors.
     The equivalence holds when two execution results are
     either not errors and equal, or both errors;
     that is, we consider all errors equivalent,
     but we consider non-errors non-equivalent unless equal.
     The theorem formulation is thus further refined to")
   (xdoc::codeblock
    "(exec (xform ast) cstate (xform funenv)) ~=~ (exec ast cstate funenv)")
   (xdoc::p
    "where @('~=~') denotes the equivalence
     (we use this symbol just here, for readability).")
   (xdoc::p
    "The description above has left out the @('limit') input of @('exec').
     For this @('DeadCodeEliminator') transformation,
     that input is unchanged between the left side and right side,
     because this transformation does not affect
     the values taken by the limit during execution:
     this transformation just removes code
     that would never be executed anyways.")
   (xdoc::p
    "The theorems above are simultaneously proved
     by mutual induction on the execution functions.
     Since the execution functions make use of auxiliary semantic functions,
     e.g. to read and write variables,
     we first prove theorems about these functions.
     These theorems also have essentially the form discussed above,
     with the necessary adaptations.")
   (xdoc::p
    "It should be clear that the approach explained above
     is more general than the @('DeadCodeEliminator') transformation,
     and should be applicable to other Yul transformations as well.
     To summarize, the approach is:")
   (xdoc::ol
    (xdoc::li
     "Extend the transformation from syntactic to semantic entities.")
    (xdoc::li
     "Define equivalence relations over execution results.")
    (xdoc::li
     "Prove equivalence theorems for the auxiliary semantic functions.")
    (xdoc::li
     "Prove equivalence theorems for the execution functions."))
   (xdoc::p
    "Some theorems about the auxiliary semantic semantics
     can be proved as equality rather than equivalences.")
   (xdoc::p
    "In the proofs, we generally enable
     functions @('...-result-dead') that transform result values,
     such as @(tsee cstate-result-dead).
     This exposes the error and non-error cases in the proof.
     Perhaps there is a way to avoid enabling these functions,
     and using suitable rules instead.")
   (xdoc::p
    "In the proofs, we generally enable
     the equivalence relations @('...-result-okeq'),
     such as @(tsee cstate-result-okeq).
     This, together with the enabling of the @('...-result-dead') functions,
     exposes the error and non-error cases.
     Perhaps there is a way to avoid enabling these functions,
     and using suitable rules instead."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 1: Extend the transformation from syntactic to semantic entities.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo-dead ((info funinfop))
  :returns (new-info funinfop)
  :short "Eliminate dead code in function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We apply the transformation to the body of the function."))
  (change-funinfo info :body (block-dead (funinfo->body info)))
  :hooks (:fix)
  ///

  (defrule funinfo-dead-of-funinfo
    (equal (funinfo-dead (funinfo inputs outputs body))
           (funinfo inputs outputs (block-dead body))))

  (defrule funinfo->inputs-of-funinfo-dead
    (equal (funinfo->inputs (funinfo-dead info))
           (funinfo->inputs info)))

  (defrule funinfo->outputs-of-funinfo-dead
    (equal (funinfo->outputs (funinfo-dead info))
           (funinfo->outputs info)))

  (defrule funinfo->body-of-funinfo-dead
    (equal (funinfo->body (funinfo-dead info))
           (block-dead (funinfo->body info)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-dead ((funscope funscopep))
  :returns (new-funscope funscopep)
  :short "Eliminate dead code in function scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform all the function information values of the map."))
  (b* ((funscope (funscope-fix funscope))
       ((when (omap::empty funscope)) nil)
       ((mv name info) (omap::head funscope)))
    (omap::update name (funinfo-dead info) (funscope-dead (omap::tail funscope))))
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule keys-of-funscope-dead
    (implies (funscopep funscope)
             (equal (omap::keys (funscope-dead funscope))
                    (omap::keys funscope))))

  (defrule consp-of-in-of-funscope-dead
    (implies (funscopep funscope)
             (equal (consp (omap::in fun (funscope-dead funscope)))
                    (consp (omap::in fun funscope)))))

  (defrule cdr-of-in-of-funscope-dead
    (implies (and (funscopep funscope)
                  (omap::in fun funscope))
             (equal (cdr (omap::in fun (funscope-dead funscope)))
                    (funinfo-dead (cdr (omap::in fun funscope))))))

  (defrule funscope-dead-of-update
    (implies (and (identifierp name)
                  (funinfop info)
                  (funscopep funscope))
             (equal (funscope-dead (omap::update name info funscope))
                    (omap::update name
                                  (funinfo-dead info)
                                  (funscope-dead funscope))))
    :enable (omap::head
             omap::tail
             omap::update
             funscopep)
    :hints ('(:expand ((:free (name info funscope)
                        (funscope-dead (cons (cons name info) funscope))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-result-dead ((funscope? funscope-resultp))
  :returns (new-funscope? funscope-resultp)
  :short "Eliminate dead code in errors and function scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform function scopes and leave errors unchanged."))
  (b* ((funscope? (funscope-result-fix funscope?)))
    (if (resulterrp funscope?)
        funscope?
      (funscope-dead funscope?)))
  :hooks (:fix)
  ///

  (defrule funscope-result-dead-when-funscopep
    (implies (funscopep funscope)
             (equal (funscope-result-dead funscope)
                    (funscope-dead funscope)))
    :enable (funscopep resulterrp))

  (defrule funscope-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (funscope-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funenv-dead ((funenv funenvp))
  :returns (new-funenv funenvp)
  :short "Eliminate dead code in function environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform all the function scopes in the list."))
  (cond ((endp funenv) nil)
        (t (cons (funscope-dead (car funenv))
                 (funenv-dead (cdr funenv)))))
  :hooks (:fix)
  ///

  (defrule funenv-dead-of-cons
    (equal (funenv-dead (cons funscope funscopes))
           (cons (funscope-dead funscope)
                 (funenv-dead funscopes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funenv-result-dead ((funenv? funenv-resultp))
  :returns (new-funenv? funenv-resultp)
  :short "Eliminate dead code in errors and function environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform function environments and leave errors unchanged."))
  (b* ((funenv? (funenv-result-fix funenv?)))
    (if (resulterrp funenv?)
        funenv?
      (funenv-dead funenv?)))
  :hooks (:fix)
  ///

  (defrule funenv-result-dead-when-funenvp
    (implies (funenvp funenv)
             (equal (funenv-result-dead funenv)
                    (funenv-dead funenv)))
    :enable (funenvp resulterrp))

  (defrule funenv-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (funenv-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo+funenv-dead ((funinfoenv funinfo+funenv-p))
  :returns (new-funinfoenv funinfo+funenv-p)
  :short "Eliminate dead code in pairs consisting of
          function information and a function environment."
  (b* (((funinfo+funenv funinfoenv) funinfoenv))
    (make-funinfo+funenv :info (funinfo-dead funinfoenv.info)
                         :env (funenv-dead funinfoenv.env)))
  :hooks (:fix)
  ///

  (defrule funinfo+funenv->info-of-funinfo+funenv-dead
    (equal (funinfo+funenv->info (funinfo+funenv-dead funinfoenv))
           (funinfo-dead (funinfo+funenv->info funinfoenv))))

  (defrule funinfo+funenv->env-of-funinfo+funenv-dead
    (equal (funinfo+funenv->env (funinfo+funenv-dead funinfoenv))
           (funenv-dead (funinfo+funenv->env funinfoenv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo+funenv-result-dead ((funinfoenv? funinfo+funenv-resultp))
  :returns (new-funinfoenv? funinfo+funenv-resultp)
  :short "Eliminate dead code in errors
          and pairs consisting of
          function information and a function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform the pairs and leave errors unchanged."))
  (b* ((funinfoenv? (funinfo+funenv-result-fix funinfoenv?)))
    (if (resulterrp funinfoenv?)
        funinfoenv?
      (funinfo+funenv-dead funinfoenv?)))
  :hooks (:fix)
  ///

  (defrule funinfo+funenv-result-dead-when-funinfo+funenv-p
    (implies (funinfo+funenv-p funinfoenv)
             (equal (funinfo+funenv-result-dead funinfoenv)
                    (funinfo+funenv-dead funinfoenv)))
    :enable (funinfo+funenv-p resulterrp))

  (defrule funinfo+funenv-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (funinfo+funenv-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 2: Define equivalence relations over execution results.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eoutcome-result-okeq ((x eoutcome-resultp) (y eoutcome-resultp))
  :returns (yes/no booleanp)
  :short "Equality of expression outcome results modulo errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the equivalence relation on expression outcomes
     discussed in @(see dead-code-eliminator-verification)."))
  (b* ((x (eoutcome-result-fix x))
       (y (eoutcome-result-fix y)))
    (cond ((resulterrp x) (resulterrp y))
          ((resulterrp y) (resulterrp x))
          (t (equal x y))))
  :hooks (:fix)
  ///
  (defequiv eoutcome-result-okeq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define soutcome-result-okeq ((x soutcome-resultp) (y soutcome-resultp))
  :returns (yes/no booleanp)
  :short "Equality of statement outcome results modulo errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the equivalence relation on statement outcomes
     discussed in @(see dead-code-eliminator-verification)."))
  (b* ((x (soutcome-result-fix x))
       (y (soutcome-result-fix y)))
    (cond ((resulterrp x) (resulterrp y))
          ((resulterrp y) (resulterrp x))
          (t (equal x y))))
  :hooks (:fix)
  ///
  (defequiv soutcome-result-okeq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 3: Prove equivalence theorems for the auxiliary semantic functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule find-fun-of-dead
  :short "Correctness theorem for @(tsee find-fun)."
  (equal (find-fun fun (funenv-dead funenv))
         (funinfo+funenv-result-dead (find-fun fun funenv)))
  :use (:instance lemma (funenv (funenv-fix funenv)))
  :prep-lemmas
  ((defruled lemma
     (implies (funenvp funenv)
              (equal (find-fun fun (funenv-dead funenv))
                     (funinfo+funenv-result-dead (find-fun fun funenv))))
     :enable (find-fun
              funinfo+funenv-dead))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ensure-funscope-disjoint-of-dead
  :short "Correctness theorem for @(tsee ensure-funscope-disjoint)."
  (equal (ensure-funscope-disjoint (funscope-dead funscope)
                                   (funenv-dead funenv))
         (ensure-funscope-disjoint funscope funenv))
  :use (:instance lemma
        (funscope (funscope-fix funscope))
        (funenv (funenv-fix funenv)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (funscopep funscope)
                   (funenvp funenv))
              (equal (ensure-funscope-disjoint (funscope-dead funscope)
                                               (funenv-dead funenv))
                     (ensure-funscope-disjoint funscope funenv)))
     :enable ensure-funscope-disjoint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funinfo-for-fundef-of-dead
  :short "Correctness theorem for @(tsee funinfo-for-fundef)."
  (equal (funinfo-for-fundef (fundef-dead fundef))
         (funinfo-dead (funinfo-for-fundef fundef)))
  :enable funinfo-for-fundef
  :expand (fundef-dead fundef))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funscope-for-fundefs-of-dead
  :short "Correctness theorem for @(tsee funscope-for-fundefs)."
  (equal (funscope-for-fundefs (fundef-list-dead fundefs))
         (funscope-result-dead (funscope-for-fundefs fundefs)))
  :enable (funscope-for-fundefs
           funscopep-when-funscope-resultp-and-not-resulterrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-funs-of-dead
  :short "Correctness theorem for @(tsee add-funs)."
  (equal (add-funs (fundef-list-dead fundefs) (funenv-dead funenv))
         (funenv-result-dead (add-funs fundefs funenv)))
  :use (:instance lemma
        (fundefs (fundef-list-fix fundefs))
        (funenv (funenv-fix funenv)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (fundef-listp fundefs)
                   (funenvp funenv))
              (equal (add-funs (fundef-list-dead fundefs) (funenv-dead funenv))
                     (funenv-result-dead (add-funs fundefs funenv))))
     :enable (add-funs
              funscopep-when-funscope-resultp-and-not-resulterrp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule statements-to-fundefs-of-dead
  :short "Correctness theorem for @(tsee statements-to-fundefs)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This proof is a bit more elaborate than others
     because of the @('afterp') flag of @(tsee statement-list-dead).
     To have a sufficiently strong induction hypothesis
     we need that flag to be generic, not to have a specific value.
     Thus, we introduce a predicate universally quantified over @('afterp'),
     and we prove that it holds by induction.
     There may be a way to avoid the explicit quantification,
     particularly because we are only interested in two values of @('afterp'),
     namely @('nil') and non-@('nil')."))
  (equal (statements-to-fundefs (statement-list-dead stmts afterp))
         (fundef-list-dead (statements-to-fundefs stmts)))
  :use pred-holds
  :enable pred-necc

  :prep-lemmas

  ((defund-sk pred (stmts)
     (forall (afterp)
             (equal (statements-to-fundefs (statement-list-dead stmts afterp))
                    (fundef-list-dead (statements-to-fundefs stmts))))
     :rewrite :direct)

   (defruled pred-base
     (implies (not (consp stmts))
              (pred stmts))
     :enable (pred
              statements-to-fundefs
              statement-list-dead))

   (defruled pred-step
     (implies (and (consp stmts)
                   (pred (cdr stmts)))
              (pred stmts))
     :enable (pred
              pred-necc
              statements-to-fundefs
              statement-list-dead))

   (defruled pred-holds
     (pred stmts)
     :induct (len stmts)
     :enable (pred-base pred-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 4: Prove equivalence theorems for the execution functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-of-dead-computed-hints
  :short "Computed hints to prove the execution theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned earlier,
     the main theorems are proved by mutual execution,
     using the flag approach.")
   (xdoc::p
    "The current proof uses some @(':use') and @(':expand') hints
     for certain cases of the induction proof.
     Attempting to apply these hints to all cases uniformly
     causes the proof to be too slow (if it works at all),
     presumably due to many unnecessary case splits.
     There may be ways to avoid the @(':use') hints,
     by proving and enabling suitable rules,
     but this needs more work; it was not immediate to do.
     It is less clear whether the @(':expand') hints could be avoided,
     given that the functions in question are already enabled,
     but ACL2's heuristics prevent their expansion,
     even though forcing the expand with the @(':expand') hints
     leads to a successful proof in the end.
     Perhaps they might be applied uniformly to all subgoals,
     but this may cause proof brittleness or inefficiency.
     Thus, limiting these @(':use') and @(':expand') hints to the needed cases
     seems to be the right thing at this moment.")
   (xdoc::p
    "We also want to limit the enabling of certain functions
     to certain cases of the induction proof.
     We need to study this in more detail,
     but initial experiments suggested that those enablements
     may cause adverse effects in the cases in which they are not needed).
     So again limiting the enablements to the needed proof cases
     seems to be the right thing at this moment.")
   (xdoc::p
    "To avoid the brittleness and unreadability of subgoal hints,
     we use computed hints to robustly and readably designate
     the proof cases to which specific hints must apply.
     We do that with the function below,
     which uses two macros for conciseness.
     The proof cases are denoted based on
     the flag value and possibly the kind of statement;
     these are expressed in terms of occurrences of terms in the clauses."))

  (defmacro exec-of-dead-flag-is (flag)
    `(acl2::occur-lst '(acl2::flag-is ',flag) clause))

  (defmacro exec-of-dead-stmt-kind-is (kind)
    `(acl2::occur-lst '(equal (statement-kind$inline stmt) ',kind) clause))

  (defun exec-of-dead-hints (id clause world)
    (declare (ignore id world))
    (cond
     ((exec-of-dead-flag-is exec-expression)
      '(:in-theory (enable exec-expression)))
     ((exec-of-dead-flag-is exec-expression-list)
      '(:in-theory (enable exec-expression-list)))
     ((exec-of-dead-flag-is exec-funcall)
      '(:in-theory (enable exec-funcall)))
     ((exec-of-dead-flag-is exec-function)
      '(:in-theory (enable exec-function)))
     ((exec-of-dead-flag-is exec-statement)
      `(:in-theory (enable exec-statement
                           statement-dead)
        ,@(and (or (exec-of-dead-stmt-kind-is :if)
                   (exec-of-dead-stmt-kind-is :for)
                   (exec-of-dead-stmt-kind-is :switch))
               '(:expand (statement-dead stmt)))))
     ((exec-of-dead-flag-is exec-statement-list)
      '(:in-theory (e/d (exec-statement-list
                         statement-list-dead)
                        (statement-kind-when-mode-regular))
        :use (:instance statement-kind-when-mode-regular
              (stmt (car stmts))
              (limit (1- limit)))))
     ((exec-of-dead-flag-is exec-block)
      '(:in-theory (enable exec-block
                           block-dead)))
     ((exec-of-dead-flag-is exec-for-iterations)
      '(:in-theory (enable exec-for-iterations)))
     ((exec-of-dead-flag-is exec-switch-rest)
      '(:in-theory (enable exec-switch-rest
                           swcase-dead
                           swcase-list-dead
                           block-option-some->val)
        :expand ((block-option-dead default)
                 (exec-switch-rest cases
                                   default
                                   target
                                   cstate
                                   funenv
                                   limit)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-of-dead
  :short "Correctness theorems of the execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We locally enable the equivalence relations,
     since we always want to expand them in the proofs.
     Note that, if we put them into a goal hint,
     they would not apply to subgoals where computed hints apply;
     this is why we locally enable them instead.")
   (xdoc::p
    "We locally enable the @('...-result-dead') functions,
     since we always want to expand them in the proofs.
     This way, we expose the two cases, error and non-error."))

  (local (in-theory (enable eoutcome-result-okeq
                            soutcome-result-okeq
                            funenv-result-dead
                            funinfo+funenv-result-dead)))

  (defthm-exec-flag

    (defthm exec-expression-of-dead
      (eoutcome-result-okeq
       (exec-expression expr
                        cstate
                        (funenv-dead funenv)
                        limit)
       (exec-expression expr
                        cstate
                        funenv
                        limit))
      :flag exec-expression)

    (defthm exec-expression-list-of-dead
      (eoutcome-result-okeq
       (exec-expression-list exprs
                             cstate
                             (funenv-dead funenv)
                             limit)
       (exec-expression-list exprs
                             cstate
                             funenv
                             limit))
      :flag exec-expression-list)

    (defthm exec-funcall-of-dead
      (eoutcome-result-okeq
       (exec-funcall call
                     cstate
                     (funenv-dead funenv)
                     limit)
       (exec-funcall call
                     cstate
                     funenv
                     limit))
      :flag exec-funcall)

    (defthm exec-function-of-dead
      (eoutcome-result-okeq
       (exec-function fun
                      args
                      cstate
                      (funenv-dead funenv)
                      limit)
       (exec-function fun
                      args
                      cstate
                      funenv
                      limit))
      :flag exec-function)

    (defthm exec-statement-of-dead
      (soutcome-result-okeq
       (exec-statement (statement-dead stmt)
                       cstate
                       (funenv-dead funenv)
                       limit)
       (exec-statement stmt
                       cstate
                       funenv
                       limit))
      :flag exec-statement)

    (defthm exec-statement-list-of-dead
      (soutcome-result-okeq
       (exec-statement-list (statement-list-dead stmts nil)
                            cstate
                            (funenv-dead funenv)
                            limit)
       (exec-statement-list stmts
                            cstate
                            funenv
                            limit))
      :flag exec-statement-list)

    (defthm exec-block-of-dead
      (soutcome-result-okeq
       (exec-block (block-dead block)
                   cstate
                   (funenv-dead funenv)
                   limit)
       (exec-block block
                   cstate
                   funenv
                   limit))
      :flag exec-block)

    (defthm exec-for-iterations-of-dead
      (soutcome-result-okeq
       (exec-for-iterations test
                            (block-dead update)
                            (block-dead body)
                            cstate
                            (funenv-dead funenv)
                            limit)
       (exec-for-iterations test
                            update
                            body
                            cstate
                            funenv
                            limit))
      :flag exec-for-iterations)

    (defthm exec-switch-rest-of-dead
      (soutcome-result-okeq
       (exec-switch-rest (swcase-list-dead cases)
                         (block-option-dead default)
                         target
                         cstate
                         (funenv-dead funenv)
                         limit)
       (exec-switch-rest cases
                         default
                         target
                         cstate
                         funenv
                         limit))
      :flag exec-switch-rest)

    :hints (exec-of-dead-hints)))
