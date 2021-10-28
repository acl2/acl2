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
    "The first reason is that the computation state includes functions,
     which go in and out of scope as blocks are entered and exited.
     Thus, if @('(exec (xform ast) cstate)') adds functions to @('cstate'),
     it may add slightly different functions from @('(exec ast cstate)'),
     namely functions that have been transformed by @('xform').
     Thus, we define transformation function
     on semantic entities like computation states,
     and we refine the formulation of our theorems to")
   (xdoc::codeblock
    "(exec (xform ast) (xform cstate)) = (xform (exec ast state))")
   (xdoc::p
    "where the left-hand side execution now operates on
     all transformed syntactic and semantic entities,
     while the right-hand side execution operates on the untransformed entities.
     This can be visualized as a commuting diagram:
     transforming and then executing
     is the same as
     executing and then tansforming.
     Note that this form also gives adequately strong induction hypotheses
     in the proof of the theorems.")
   (xdoc::p
    "The second reason and refinement of the theorems
     has to do with error results,
     which may be returned by the defensive execution functions.
     The error values include information about the ACL2 call stack
     (see @(tsee fty::defresult)),
     which causes a dependencies of error values
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
    "(exec (xform ast) (xform cstate)) ~=~ (xform (exec ast cstate))")
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
     that would never be executed anyways.
     However, for other transformations,
     in general we would have to prove theorems of the form")
   (xdoc::codeblock
    "(exec (xform ast) (xform cstate) (xform limit))"
    "~=~"
    "(xform (exec ast cstate limit))")
   (xdoc::p
    "where the limit on the left side is transformed based on
     the effect of the transformation on
     how the limit changes through execution.
     In essense, the limit must be adjusted in a way that
     execution on the transformed entities suitably corresponds to
     execution on the untransformed entities.")
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

(define cstate-dead ((cstate cstatep))
  :returns (new-cstate cstatep)
  :short "Eliminate dead code in computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform the function state,
     leaving the local state unchanged."))
  (change-cstate cstate :functions (fstate-dead (cstate->functions cstate)))
  :hooks (:fix)
  ///

  (defrule cstate-dead-of-cstate
    (equal (cstate-dead (cstate local functions))
           (cstate local (fstate-dead functions))))

  (defrule cstate->local-of-cstate-dead
    (equal (cstate->local (cstate-dead cstate))
           (cstate->local cstate)))

  (defrule cstate->functions-of-cstate-dead
    (equal (cstate->functions (cstate-dead cstate))
           (fstate-dead (cstate->functions cstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cstate-result-dead ((cstate? cstate-resultp))
  :returns (new-cstate? cstate-resultp)
  :short "Eliminate dead code in computation state results."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform computation states and leave errors unchanged."))
  (b* ((cstate? (cstate-result-fix cstate?)))
    (if (resulterrp cstate?)
        cstate?
      (cstate-dead cstate?)))
  :hooks (:fix)
  ///

  (defrule cstate-result-dead-when-cstatep
    (implies (cstatep cstate)
             (equal (cstate-result-dead cstate)
                    (cstate-dead cstate)))
    :enable (cstatep resulterrp))

  (defrule cstate-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (cstate-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eoutcome-dead ((outcome eoutcomep))
  :returns (new-outcome eoutcomep)
  :short "Eliminate dead code in expression outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform the computation state,
     leaving the values unchanged."))
  (change-eoutcome outcome :cstate (cstate-dead (eoutcome->cstate outcome)))
  :hooks (:fix)
  ///

  (defrule eoutcome-dead-of-eoutcome
    (equal (eoutcome-dead (eoutcome cstate values))
           (eoutcome (cstate-dead cstate) values)))

  (defrule eoutcome->cstate-of-eoutcome-dead
    (equal (eoutcome->cstate (eoutcome-dead outcome))
           (cstate-dead (eoutcome->cstate outcome))))

  (defrule eoutcome->values-of-eoutcome-dead
    (equal (eoutcome->values (eoutcome-dead outcome))
           (eoutcome->values outcome))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eoutcome-result-dead ((outcome? eoutcome-resultp))
  :returns (new-outcome? eoutcome-resultp)
  :short "Eliminate dead code in expression outcome results."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform expression results and leave errors unchanged."))
  (b* ((outcome? (eoutcome-result-fix outcome?)))
    (if (resulterrp outcome?)
        outcome?
      (eoutcome-dead outcome?)))
  :hooks (:fix)
  ///

  (defrule eoutcome-result-dead-when-eoutcomep
    (implies (eoutcomep outcome)
             (equal (eoutcome-result-dead outcome)
                    (eoutcome-dead outcome)))
    :enable (eoutcomep resulterrp))

  (defrule eoutcome-result-dead-when-resulterrp
    (implies (resulterrp error)
             (equal (eoutcome-result-dead error)
                    error))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define soutcome-dead ((outcome soutcomep))
  :returns (new-outcome soutcomep)
  :short "Eliminate dead code in statement outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform the computation state,
     leaving the mode unchanged."))
  (change-soutcome outcome :cstate (cstate-dead (soutcome->cstate outcome)))
  :hooks (:fix)
  ///

  (defrule soutcome-dead-of-soutcome
    (equal (soutcome-dead (soutcome cstate mode))
           (soutcome (cstate-dead cstate) mode)))

  (defrule soutcome->cstate-of-soutcome-dead
    (equal (soutcome->cstate (soutcome-dead outcome))
           (cstate-dead (soutcome->cstate outcome))))

  (defrule soutcome->mode-of-soutcome-dead
    (equal (soutcome->mode (soutcome-dead outcome))
           (soutcome->mode outcome))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define soutcome-result-dead ((outcome? soutcome-resultp))
  :returns (new-outcome? soutcome-resultp)
  :short "Eliminate dead code in statement outcome results."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform expression results and leave errors unchanged."))
  (b* ((outcome? (soutcome-result-fix outcome?)))
    (if (resulterrp outcome?)
        outcome?
      (soutcome-dead outcome?)))
  :hooks (:fix)
  ///

  (defrule soutcome-result-dead-when-soutcomep
    (implies (soutcomep outcome)
             (equal (soutcome-result-dead outcome)
                    (soutcome-dead outcome)))
    :enable (soutcomep resulterrp))

  (defrule soutcome-result-dead-of-resulterr
    (equal (soutcome-result-dead (resulterr info stack))
           (resulterr info stack))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 3: Prove equivalence theorems for the auxiliary semantic functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule exec-literal-of-dead
  :short "Correctness theorem for @(tsee exec-literal)."
  (equal (exec-literal lit (cstate-dead cstate))
         (eoutcome-result-dead (exec-literal lit cstate)))
  :enable exec-literal)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule read-var-value-of-dead
  :short "Correctness theorem for @(tsee read-var-value)."
  (equal (read-var-value var (cstate-dead cstate))
         (read-var-value var cstate))
  :enable read-var-value)

(defrule read-vars-values-of-dead
  :short "Correctness theorem for @(tsee read-vars-values)."
  (equal (read-vars-values vars (cstate-dead cstate))
         (read-vars-values vars cstate))
  :enable read-vars-values)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule exec-path-of-dead
  :short "Correctness theorem for @(tsee exec-path)."
  (equal (exec-path path (cstate-dead cstate))
         (eoutcome-result-dead (exec-path path cstate)))
  :enable exec-path)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule write-var-value-of-dead
  :short "Correctness theorem for @(tsee write-var-value)."
  (equal (write-var-value var val (cstate-dead cstate))
         (cstate-result-dead (write-var-value var val cstate)))
  :enable write-var-value)

(defrule write-vars-values-of-dead
  :short "Correctness theorem for @(tsee write-vars-values)."
  (equal (write-vars-values vars vals (cstate-dead cstate))
         (cstate-result-dead (write-vars-values vars vals cstate)))
  :enable (write-vars-values
           cstate-result-dead))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-var-value-of-dead
  :short "Correctness theorem for @(tsee add-var-value)."
  (equal (add-var-value var val (cstate-dead cstate))
         (cstate-result-dead (add-var-value var val cstate)))
  :enable add-var-value)

(defrule add-vars-values-of-dead
  :short "Correctness theorem for @(tsee add-vars-values)."
  (equal (add-vars-values vars vals (cstate-dead cstate))
         (cstate-result-dead (add-vars-values vars vals cstate)))
  :enable (add-vars-values
           cstate-result-dead))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule init-local-of-dead
  :short "Correctness theorem for @(tsee init-local)."
  (equal (init-local in-vars in-vals out-vars (cstate-dead cstate))
         (cstate-result-dead
          (init-local in-vars in-vals out-vars cstate)))
  :enable (init-local
           cstate-result-dead)
  :prep-lemmas
  ((defrule lemma
     (equal (add-vars-values vars
                             vals
                             (cstate nil
                                     (fstate-dead (cstate->functions cstate))))
            (cstate-result-dead
             (add-vars-values vars
                              vals
                              (cstate nil
                                      (cstate->functions cstate)))))
     :enable cstate-result-dead
     :disable add-vars-values-of-dead
     :use (:instance add-vars-values-of-dead
           (cstate (cstate nil (cstate->functions cstate)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule restrict-vars-of-dead
  :short "Correctness theorem for @(tsee restrict-vars)."
  (equal (restrict-vars vars (cstate-dead cstate))
         (cstate-result-dead (restrict-vars vars cstate)))
  :enable restrict-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule get-fun-of-dead
  :short "Correctness theorem for @(tsee get-fun)."
  (equal (get-fun fun (cstate-dead cstate))
         (funinfo-result-dead (get-fun fun cstate)))
  :enable get-fun)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-fun-of-dead
  :short "Correctness theorem for @(tsee add-fun)."
  (equal (add-fun fun (funinfo-dead info) (cstate-dead cstate))
         (cstate-result-dead (add-fun fun info cstate)))
  :use (:instance lemma (info (funinfo-fix info)))
  :prep-lemmas
  ((defrule lemma
     (implies (funinfop info)
              (equal (add-fun fun (funinfo-dead info) (cstate-dead cstate))
                     (cstate-result-dead (add-fun fun info cstate))))
     :enable (add-fun
              cstate-result-dead))))

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
     (more precisely, it retrieves transformed function definitions,
     whose dead code is removed),
     an error value may have stacks of different sizes,
     due to the different number of recursive calls.")
   (xdoc::p
    "This proof is a bit more elaborate
     because of the @('afterp') flag of @(tsee statement-list-dead).
     To have a sufficiently strong induction hypothesis
     we need that flag to be generic, not to have a specific value.
     Thus, we introduced a predicate universally quantified over @('afterp'),
     and we prove that it holds by induction.
     There may a way to avoid the explicit quantification,
     particularly because we are only interested in two values of @('afterp'),
     namely @('nil') and non-@('nil')."))
  (cstate-result-okeq
   (add-funs-in-statement-list (statement-list-dead stmts afterp)
                               (cstate-dead cstate))
   (cstate-result-dead
    (add-funs-in-statement-list stmts cstate)))
  :use pred-holds
  :enable pred-necc

  :prep-lemmas

  ((defund-sk pred (stmts)
     (forall (afterp cstate)
             (cstate-result-okeq
              (add-funs-in-statement-list (statement-list-dead stmts afterp)
                                          (cstate-dead cstate))
              (cstate-result-dead
               (add-funs-in-statement-list stmts cstate))))
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
                 (cstate-result-okeq
                  (add-funs-in-statement-list (statement-list-dead stmts afterp)
                                              (cstate-dead cstate))
                  (cstate-result-dead
                   (add-funs-in-statement-list stmts cstate))))
        :enable (pred-necc
                 add-funs-in-statement-list
                 statement-list-dead
                 cstate-result-dead)
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
      '(:in-theory (enable exec-expression-list
                           eoutcome-result-dead
                           eoutcome-result-okeq)))
     ((exec-of-dead-flag-is exec-funcall)
      '(:in-theory (enable exec-funcall
                           eoutcome-result-dead
                           eoutcome-result-okeq)))
     ((exec-of-dead-flag-is exec-function)
      '(:in-theory (enable exec-function
                           funinfo-result-dead
                           cstate-result-dead
                           soutcome-result-dead
                           eoutcome-result-okeq
                           soutcome-result-okeq)))
     ((exec-of-dead-flag-is exec-statement)
      `(:in-theory (e/d (exec-statement
                         statement-dead
                         cstate-result-dead
                         eoutcome-result-dead
                         soutcome-result-dead
                         cstate-result-okeq
                         eoutcome-result-okeq
                         soutcome-result-okeq)
                        (add-funs-in-statement-list-of-dead
                         restrict-vars-of-dead))
        ,@(and (or (exec-of-dead-stmt-kind-is :if)
                   (exec-of-dead-stmt-kind-is :for)
                   (exec-of-dead-stmt-kind-is :switch))
               '(:expand (statement-dead stmt)))
        ,@(and (exec-of-dead-stmt-kind-is :for)
               '(:use ((:instance add-funs-in-statement-list-of-dead
                        (stmts (block->statements (statement-for->init stmt)))
                        (afterp nil))
                       (:instance restrict-vars-of-dead
                        (vars (omap::keys (cstate->local cstate)))
                        (cstate (cstate (cstate->local
                                         (soutcome->cstate
                                          (exec-statement-list
                                           (block->statements
                                            (statement-for->init stmt))
                                           (add-funs-in-statement-list
                                            (block->statements
                                             (statement-for->init stmt))
                                            cstate)
                                           (+ -1 limit))))
                                        (cstate->functions cstate))))
                       (:instance restrict-vars-of-dead
                        (vars (omap::keys (cstate->local cstate)))
                        (cstate (cstate (cstate->local
                                         (soutcome->cstate
                                          (exec-for-iterations
                                           (statement-for->test stmt)
                                           (statement-for->update stmt)
                                           (statement-for->body stmt)
                                           (add-funs-in-statement-list
                                            (block->statements
                                             (statement-for->init stmt))
                                            cstate)
                                           (+ -1 limit))))
                                        (cstate->functions cstate)))))))))
     ((exec-of-dead-flag-is exec-statement-list)
      '(:in-theory (e/d (exec-statement-list
                         statement-list-dead
                         soutcome-result-dead
                         soutcome-result-okeq)
                        (statement-kind-when-mode-regular))
        :expand (statement-list-dead stmt nil)
        :use (:instance statement-kind-when-mode-regular
              (stmt (car stmts))
              (limit (1- limit)))))
     ((exec-of-dead-flag-is exec-block)
      '(:in-theory (e/d (exec-block
                         block-dead
                         cstate-result-dead
                         soutcome-result-dead
                         cstate-result-okeq
                         soutcome-result-okeq)
                        (add-funs-in-statement-list-of-dead
                         restrict-vars-of-dead))
        :use ((:instance add-funs-in-statement-list-of-dead
               (stmts (block->statements block))
               (afterp nil))
              (:instance restrict-vars-of-dead
               (vars (omap::keys (cstate->local cstate)))
               (cstate (cstate
                        (cstate->local
                         (soutcome->cstate
                          (exec-statement-list
                           (block->statements block)
                           (add-funs-in-statement-list (block->statements block)
                                                       cstate)
                           (+ -1 limit))))
                        (cstate->functions cstate)))))))
     ((exec-of-dead-flag-is exec-for-iterations)
      '(:in-theory (enable exec-for-iterations
                           eoutcome-result-dead
                           soutcome-result-dead
                           eoutcome-result-okeq
                           soutcome-result-okeq)))
     ((exec-of-dead-flag-is exec-switch-rest)
      '(:in-theory (enable exec-switch-rest
                           swcase-dead
                           swcase-list-dead
                           soutcome-result-dead
                           soutcome-result-okeq
                           block-option-some->val)
        :expand ((block-option-dead default)
                 (exec-switch-rest cases default target cstate limit)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-of-dead
  :short "Correctness theorems of the execution functions."

  (defthm-exec-flag

    (defthm exec-expression-of-dead
      (eoutcome-result-okeq
       (exec-expression expr
                        (cstate-dead cstate)
                        limit)
       (eoutcome-result-dead
        (exec-expression expr cstate limit)))
      :flag exec-expression)

    (defthm exec-expression-list-of-dead
      (eoutcome-result-okeq
       (exec-expression-list exprs
                             (cstate-dead cstate)
                             limit)
       (eoutcome-result-dead
        (exec-expression-list exprs cstate limit)))
      :flag exec-expression-list)

    (defthm exec-funcall-of-dead
      (eoutcome-result-okeq
       (exec-funcall call
                     (cstate-dead cstate)
                     limit)
       (eoutcome-result-dead
        (exec-funcall call cstate limit)))
      :flag exec-funcall)

    (defthm exec-function-of-dead
      (eoutcome-result-okeq
       (exec-function fun
                      args
                      (cstate-dead cstate)
                      limit)
       (eoutcome-result-dead
        (exec-function fun args cstate limit)))
      :flag exec-function)

    (defthm exec-statement-of-dead
      (soutcome-result-okeq
       (exec-statement (statement-dead stmt)
                       (cstate-dead cstate)
                       limit)
       (soutcome-result-dead
        (exec-statement stmt cstate limit)))
      :flag exec-statement)

    (defthm exec-statement-list-of-dead
      (soutcome-result-okeq
       (exec-statement-list (statement-list-dead stmts nil)
                            (cstate-dead cstate)
                            limit)
       (soutcome-result-dead
        (exec-statement-list stmts cstate limit)))
      :flag exec-statement-list)

    (defthm exec-block-of-dead
      (soutcome-result-okeq
       (exec-block (block-dead block)
                   (cstate-dead cstate)
                   limit)
       (soutcome-result-dead
        (exec-block block cstate limit)))
      :flag exec-block)

    (defthm exec-for-iterations-of-dead
      (soutcome-result-okeq
       (exec-for-iterations test
                            (block-dead update)
                            (block-dead body)
                            (cstate-dead cstate)
                            limit)
       (soutcome-result-dead
        (exec-for-iterations test update body cstate limit)))
      :flag exec-for-iterations)

    (defthm exec-switch-rest-of-dead
      (soutcome-result-okeq
       (exec-switch-rest (swcase-list-dead cases)
                         (block-option-dead default)
                         target
                         (cstate-dead cstate)
                         limit)
       (soutcome-result-dead
        (exec-switch-rest cases default target cstate limit)))
      :flag exec-switch-rest)

    :hints (exec-of-dead-hints)))
