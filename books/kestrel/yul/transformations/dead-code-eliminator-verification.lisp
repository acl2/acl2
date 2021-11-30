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
     also take function states as arguments,
     which contain function bodies that must be transformed.
     Thus, we define transformation functions on function states,
     and we refine the formulation of our theorems to")
   (xdoc::codeblock
    "(exec (xform ast) cstate (xform fstate)) = (exec ast state fstate)")
   (xdoc::p
    "The second reason and refinement of the theorems
     has to do with error results,
     which may be returned by the defensive execution functions.
     The error values include information about the ACL2 call stack
     (see @(tsee fty::defresult)),
     which causes a dependency of error values
     on more than just the input/output behavior of ACL2 functions,
     but also on their specific calls.
     Since the @('DeadCodeEliminator') transformation
     removes certain pieces of ASTs,
     recursive functions like @(tsee add-funs-in-statement-list)
     may return slightly different error values
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
    "(exec (xform ast) cstate (xform fstate)) ~=~ (exec ast cstate fstate)")
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

(define funinfo-result-dead ((info? funinfo-resultp))
  :returns (new-info? funinfo-resultp)
  :short "Eliminate dead code in function information results."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform function information and leave errors unchanged."))
  (b* ((info? (funinfo-result-fix info?)))
    (if (resulterrp info?)
        info?
      (funinfo-dead info?)))
  :hooks (:fix)
  ///

  (defrule funinfo-result-dead-when-funinfop
    (implies (funinfop funinfo)
             (equal (funinfo-result-dead funinfo)
                    (funinfo-dead funinfo)))
    :enable (funinfop resulterrp))

  (defrule funinfo-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (funinfo-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fstate-dead ((fstate fstatep))
  :returns (new-fstate fstatep)
  :short "Eliminate dead code in function states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform all the function information values of the map."))
  (b* ((fstate (fstate-fix fstate))
       ((when (omap::empty fstate)) nil)
       ((mv name info) (omap::head fstate)))
    (omap::update name (funinfo-dead info) (fstate-dead (omap::tail fstate))))
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule fstate-keys-of-dead
    (implies (fstatep fstate)
             (equal (omap::keys (fstate-dead fstate))
                    (omap::keys fstate))))

  (defrule fstate-consp-of-in-of-dead
    (implies (fstatep fstate)
             (equal (consp (omap::in fun (fstate-dead fstate)))
                    (consp (omap::in fun fstate)))))

  (defrule fstate-val-of-dead
    (implies (and (fstatep fstate)
                  (omap::in fun fstate))
             (equal (cdr (omap::in fun (fstate-dead fstate)))
                    (funinfo-dead (cdr (omap::in fun fstate))))))

  (defrule fstate-update-of-dead
    (implies (and (identifierp name)
                  (funinfop info)
                  (fstatep fstate))
             (equal (omap::update name
                                  (funinfo-dead info)
                                  (fstate-dead fstate))
                    (fstate-dead (omap::update name info fstate))))
    :enable (omap::head
             omap::tail
             omap::update
             fstatep)
    :hints ('(:expand ((:free (name info fstate)
                        (fstate-dead (cons (cons name info) fstate))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fstate-result-dead ((fstate? fstate-resultp))
  :returns (new-fstate? fstate-resultp)
  :short "Eliminate dead code in function state results."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform function states and leave errors unchanged."))
  (b* ((fstate? (fstate-result-fix fstate?)))
    (if (resulterrp fstate?)
        fstate?
      (fstate-dead fstate?)))
  :hooks (:fix)
  ///

  (defrule fstate-result-dead-when-fstatep
    (implies (fstatep fstate)
             (equal (fstate-result-dead fstate)
                    (fstate-dead fstate)))
    :enable (fstatep resulterrp))

  (defrule fstate-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (fstate-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 2: Define equivalence relations over execution results.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cstate-result-okeq ((x cstate-resultp) (y cstate-resultp))
  :returns (yes/no booleanp)
  :short "Equality of computation state results modulo errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the equivalence relation on computation states
     discussed in @(see dead-code-eliminator-verification)."))
  (b* ((x (cstate-result-fix x))
       (y (cstate-result-fix y)))
    (cond ((resulterrp x) (resulterrp y))
          ((resulterrp y) (resulterrp x))
          (t (equal x y))))
  :hooks (:fix)
  ///
  (defequiv cstate-result-okeq))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fstate-result-okeq ((x fstate-resultp) (y fstate-resultp))
  :returns (yes/no booleanp)
  :short "Equality of function state results modulo errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the equivalence relation on computation states
     discussed in @(see dead-code-eliminator-verification)."))
  (b* ((x (fstate-result-fix x))
       (y (fstate-result-fix y)))
    (cond ((resulterrp x) (resulterrp y))
          ((resulterrp y) (resulterrp x))
          (t (equal x y))))
  :hooks (:fix)
  ///
  (defequiv fstate-result-okeq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 3: Prove equivalence theorems for the auxiliary semantic functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule get-fun-of-dead
  :short "Correctness theorem for @(tsee get-fun)."
  (equal (get-fun fun (fstate-dead fstate))
         (funinfo-result-dead (get-fun fun fstate)))
  :use (:instance lemma (fstate (fstate-fix fstate)))
  :prep-lemmas
  ((defruled lemma
     (implies (fstatep fstate)
              (equal (get-fun fun (fstate-dead fstate))
                     (funinfo-result-dead (get-fun fun fstate))))
     :enable get-fun)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-fun-of-dead
  :short "Correctness theorem for @(tsee add-fun)."
  (equal (add-fun fun (funinfo-dead info) (fstate-dead fstate))
         (fstate-result-dead (add-fun fun info fstate)))
  :use (:instance lemma
        (fstate (fstate-fix fstate))
        (info (funinfo-fix info)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (fstatep fstate)
                   (funinfop info))
              (equal (add-fun fun (funinfo-dead info) (fstate-dead fstate))
                     (fstate-result-dead (add-fun fun info fstate))))
     :enable (add-fun
              fstate-result-dead))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funinfo-for-fundef-of-dead
  :short "Correctness theorem for @(tsee funinfo-for-fundef)."
  (equal (funinfo-for-fundef (fundef-dead fdef))
         (funinfo-dead (funinfo-for-fundef fdef)))
  :enable funinfo-for-fundef
  :expand (fundef-dead fdef))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-funs-in-statement-list-of-dead
  :short "Correctness theorem for @(tsee add-funs-in-statement-list)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike the previous theorems, this one needs the equivalence.
     This is because @(tsee add-funs-in-statement-list)
     goes through the statement list,
     but the transformation may remove statements.
     Thus, even though @(tsee add-funs-in-statement-list)
     retrieves the same functions from the statements
     because the transformations does not remove them
     (more precisely, it retrieves transformed function definitions),
     an error value may have stacks of different sizes,
     due to the different number of recursive calls.")
   (xdoc::p
    "This proof is a bit more elaborate
     because of the @('afterp') flag of @(tsee statement-list-dead).
     To have a sufficiently strong induction hypothesis
     we need that flag to be generic, not to have a specific value.
     Thus, we introduce a predicate universally quantified over @('afterp'),
     and we prove that it holds by induction.
     There may be a way to avoid the explicit quantification,
     particularly because we are only interested in two values of @('afterp'),
     namely @('nil') and non-@('nil')."))
  (fstate-result-okeq
   (add-funs-in-statement-list (statement-list-dead stmts afterp)
                               (fstate-dead fstate))
   (fstate-result-dead
    (add-funs-in-statement-list stmts fstate)))
  :use pred-holds
  :enable pred-necc

  :prep-lemmas

  ((defund-sk pred (stmts)
     (forall (afterp fstate)
             (fstate-result-okeq
              (add-funs-in-statement-list (statement-list-dead stmts afterp)
                                          (fstate-dead fstate))
              (fstate-result-dead
               (add-funs-in-statement-list stmts fstate))))
     :rewrite :direct)

   (defruled pred-base
     (implies (not (consp stmts))
              (pred stmts))
     :enable (pred
              add-funs-in-statement-list
              statement-list-dead))

   (defruled pred-step
     (implies (and (consp stmts)
                   (pred (cdr stmts)))
              (pred stmts))
     :enable lemma
     :expand (pred stmts)
     :prep-lemmas
     ((defruled lemma
        (implies (and (consp stmts)
                      (pred (cdr stmts)))
                 (fstate-result-okeq
                  (add-funs-in-statement-list (statement-list-dead stmts afterp)
                                              (fstate-dead fstate))
                  (fstate-result-dead
                   (add-funs-in-statement-list stmts fstate))))
        :enable (pred-necc
                 add-funs-in-statement-list
                 statement-list-dead
                 fstate-result-dead)
        :expand (statement-list-dead stmts afterp))))

   (defruled pred-holds
     (pred stmts)
     :induct (len stmts)
     :enable (pred-base pred-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 4: Prove equivalence theorems for the execution functions.

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
      `(:in-theory (e/d (exec-statement
                         statement-dead)
                        (add-funs-in-statement-list-of-dead))
        ,@(and (or (exec-of-dead-stmt-kind-is :if)
                   (exec-of-dead-stmt-kind-is :for)
                   (exec-of-dead-stmt-kind-is :switch))
               '(:expand (statement-dead stmt)))
        ,@(and (exec-of-dead-stmt-kind-is :for)
               '(:use ((:instance add-funs-in-statement-list-of-dead
                        (stmts (block->statements (statement-for->init stmt)))
                        (afterp nil)))))))
     ((exec-of-dead-flag-is exec-statement-list)
      '(:in-theory (e/d (exec-statement-list
                         statement-list-dead)
                        (statement-kind-when-mode-regular))
        :use (:instance statement-kind-when-mode-regular
              (stmt (car stmts))
              (limit (1- limit)))))
     ((exec-of-dead-flag-is exec-block)
      '(:in-theory (e/d (exec-block
                         block-dead)
                        (add-funs-in-statement-list-of-dead))
        :use ((:instance add-funs-in-statement-list-of-dead
               (stmts (block->statements block))
               (afterp nil)))))
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
                                   fstate
                                   limit)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-induction-depth-limit 1)

(defsection exec-of-dead
  :short "Correctness theorems of the execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We locally enable the equivalence relations,
     since we always want to expand them in the proofs.
     Note that, if we put them into a goal hint,
     they would not apply to computed hints;
     this is why we locally enable them instead.")
   (xdoc::p
    "We locally enable the @('...-result-dead') functions,
     since we always want to expand them in the proofs.
     This way, we expose the two cases, error and non-error."))

  (local (in-theory (enable cstate-result-okeq
                            eoutcome-result-okeq
                            soutcome-result-okeq
                            fstate-result-okeq
                            funinfo-result-dead
                            fstate-result-dead)))

  (defthm-exec-flag

    (defthm exec-expression-of-dead
      (eoutcome-result-okeq
       (exec-expression expr
                        cstate
                        (fstate-dead fstate)
                        limit)
       (exec-expression expr
                        cstate
                        fstate
                        limit))
      :flag exec-expression)

    (defthm exec-expression-list-of-dead
      (eoutcome-result-okeq
       (exec-expression-list exprs
                             cstate
                             (fstate-dead fstate)
                             limit)
       (exec-expression-list exprs
                             cstate
                             fstate
                             limit))
      :flag exec-expression-list)

    (defthm exec-funcall-of-dead
      (eoutcome-result-okeq
       (exec-funcall call
                     cstate
                     (fstate-dead fstate)
                     limit)
       (exec-funcall call
                     cstate
                     fstate
                     limit))
      :flag exec-funcall)

    (defthm exec-function-of-dead
      (eoutcome-result-okeq
       (exec-function fun
                      args
                      cstate
                      (fstate-dead fstate)
                      limit)
       (exec-function fun
                      args
                      cstate
                      fstate
                      limit))
      :flag exec-function)

    (defthm exec-statement-of-dead
      (soutcome-result-okeq
       (exec-statement (statement-dead stmt)
                       cstate
                       (fstate-dead fstate)
                       limit)
       (exec-statement stmt
                       cstate
                       fstate
                       limit))
      :flag exec-statement)

    (defthm exec-statement-list-of-dead
      (soutcome-result-okeq
       (exec-statement-list (statement-list-dead stmts nil)
                            cstate
                            (fstate-dead fstate)
                            limit)
       (exec-statement-list stmts
                            cstate
                            fstate
                            limit))
      :flag exec-statement-list)

    (defthm exec-block-of-dead
      (soutcome-result-okeq
       (exec-block (block-dead block)
                   cstate
                   (fstate-dead fstate)
                   limit)
       (exec-block block
                   cstate
                   fstate
                   limit))
      :flag exec-block)

    (defthm exec-for-iterations-of-dead
      (soutcome-result-okeq
       (exec-for-iterations test
                            (block-dead update)
                            (block-dead body)
                            cstate
                            (fstate-dead fstate)
                            limit)
       (exec-for-iterations test
                            update
                            body
                            cstate
                            fstate
                            limit))
      :flag exec-for-iterations)

    (defthm exec-switch-rest-of-dead
      (soutcome-result-okeq
       (exec-switch-rest (swcase-list-dead cases)
                         (block-option-dead default)
                         target
                         cstate
                         (fstate-dead fstate)
                         limit)
       (exec-switch-rest cases
                         default
                         target
                         cstate
                         fstate
                         limit))
      :flag exec-switch-rest)

    :hints (exec-of-dead-hints)))
