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
(include-book "dead-code-eliminator-nofun")
(include-book "no-function-definitions-dynamic")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dead-code-eliminator-execution
  :parents (dead-code-eliminator)
  :short "Proof that the @('DeadCodeEliminator') transformation preserves
          the execution behavior."
  :long
  (xdoc::topstring
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
     can be proved as equalities rather than equivalences.")
   (xdoc::p
    "In the proofs, we generally enable
     functions @('...-result-dead') that transform result values.
     This exposes the error and non-error cases in the proof.
     Perhaps there is a way to avoid enabling these functions,
     and using suitable rules instead.")
   (xdoc::p
    "In the proofs, we generally enable
     the equivalence relations @('...-result-okeq').
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
    (omap::update name
                  (funinfo-dead info)
                  (funscope-dead (omap::tail funscope))))
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
  :hooks (:fix))

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
  :hooks (:fix))

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
  :hooks (:fix))

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
     discussed in @(see dead-code-eliminator-execution)."))
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
     discussed in @(see dead-code-eliminator-execution)."))
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
              funinfo+funenv-result-dead
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
           funscope-result-dead
           funscopep-when-funscope-resultp-and-not-resulterrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-funs-of-dead
  :short "Correctness theorem for @(tsee add-funs)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is relevant for the top-level block,
     which has function definitions."))
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
              funscope-result-dead
              funenv-result-dead
              funscopep-when-funscope-resultp-and-not-resulterrp
              not-resulterrp-when-funenvp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Step 4: Prove equivalence theorems for the execution functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-of-dead
  :short "Correctness theorems of the execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned earlier,
     the main theorems are proved by mutual execution,
     using the flag approach.")
   (xdoc::p
    "The current proof uses some @(':use') and @(':expand') hints
     for certain cases of the induction proof.
     For robustness and efficiency,
     we prefer to apply these hints only to those cases.
     (In earlier version of this proof, which was more complex at the time,
     attempting to apply these hints to all cases uniformly
     caused the proof to be too slow, if it worked at all,
     presumably due to many unnecessary case splits.)
     There may be actually ways to avoid the @(':use') hints,
     by proving and enabling suitable rules.
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
    "To avoid the brittleness and unreadability of subgoal hints,
     we use computed hints to robustly and readably designate
     the proof cases to which specific hints must apply.
     We do that with the function below,
     which uses two macros for conciseness.
     The proof cases are denoted based on
     the flag value and possibly the kind of statement;
     these are expressed in terms of occurrences of terms in the clauses.")
   (xdoc::p
    "We locally enable, for all subgoals,
     the execution functions,
     the transformation functions,
     and the no-function-definition predicates.
     We also enable the equivalence relations,
     since we always want to expand them in the proofs.
     And we enable some additional rules, motivated by the arising subgoals.
     Note that, if we put these enablements into a goal hint,
     they would not apply to subgoals where computed hints apply;
     this is why we locally enable them instead."))

  (defmacro exec-of-dead-flag-is (flag)
    `(acl2::occur-lst '(acl2::flag-is ',flag) clause))

  (defmacro exec-of-dead-stmt-kind-is (kind)
    `(acl2::occur-lst '(equal (statement-kind$inline stmt) ',kind) clause))

  (defun exec-of-dead-hints (id clause world)
    (declare (ignore id world))
    (cond
     ((exec-of-dead-flag-is exec-statement)
      `(,@(and (or (exec-of-dead-stmt-kind-is :if)
                   (exec-of-dead-stmt-kind-is :for)
                   (exec-of-dead-stmt-kind-is :switch))
               '(:expand ((exec-statement stmt cstate funenv limit)
                          (statement-dead stmt))))))
     ((exec-of-dead-flag-is exec-statement-list)
      '(:in-theory (disable statement-kind-when-mode-regular)
        :use (:instance statement-kind-when-mode-regular
              (stmt (car stmts))
              (limit (1- limit)))
        :expand (exec-statement-list (statement-list-dead stmts)
                                     cstate
                                     (funenv-dead funenv)
                                     limit)))
     ((exec-of-dead-flag-is exec-block)
      '(:expand (exec-block block cstate funenv limit)))
     ((exec-of-dead-flag-is exec-switch-rest)
      '(:expand ((block-option-dead default)
                 (block-option-nofunp default)
                 (exec-switch-rest cases
                                   default
                                   target
                                   cstate
                                   funenv
                                   limit))))))

  (local (in-theory (enable eoutcome-result-okeq
                            soutcome-result-okeq
                            funenv-result-dead
                            funinfo+funenv-result-dead
                            exec-expression
                            exec-expression-list
                            exec-funcall
                            exec-function
                            exec-statement
                            exec-statement-list
                            exec-block
                            exec-for-iterations
                            exec-switch-rest
                            statement-dead
                            statement-list-dead
                            block-dead
                            block-option-dead
                            swcase-dead
                            swcase-list-dead
                            statement-nofunp
                            statement-list-nofunp
                            block-nofunp
                            block-option-nofunp
                            swcase-nofunp
                            swcase-list-nofunp
                            fundef-nofunp
                            block-option-some->val
                            block-nofunp-of-funinfo->body
                            not-resulterrp-when-funenvp)))

  (set-induction-depth-limit 1)

  (defthm-exec-flag

    (defthm exec-expression-of-dead
      (implies (funenv-nofunp funenv)
               (eoutcome-result-okeq
                (exec-expression expr
                                 cstate
                                 (funenv-dead funenv)
                                 limit)
                (exec-expression expr
                                 cstate
                                 funenv
                                 limit)))
      :flag exec-expression)

    (defthm exec-expression-list-of-dead
      (implies (funenv-nofunp funenv)
               (eoutcome-result-okeq
                (exec-expression-list exprs
                                      cstate
                                      (funenv-dead funenv)
                                      limit)
                (exec-expression-list exprs
                                      cstate
                                      funenv
                                      limit)))
      :flag exec-expression-list)

    (defthm exec-funcall-of-dead
      (implies (funenv-nofunp funenv)
               (eoutcome-result-okeq
                (exec-funcall call
                              cstate
                              (funenv-dead funenv)
                              limit)
                (exec-funcall call
                              cstate
                              funenv
                              limit)))
      :flag exec-funcall)

    (defthm exec-function-of-dead
      (implies (funenv-nofunp funenv)
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
                               limit)))
      :flag exec-function)

    (defthm exec-statement-of-dead
      (implies (and (statement-nofunp stmt)
                    (funenv-nofunp funenv))
               (soutcome-result-okeq
                (exec-statement (statement-dead stmt)
                                cstate
                                (funenv-dead funenv)
                                limit)
                (exec-statement stmt
                                cstate
                                funenv
                                limit)))
      :flag exec-statement)

    (defthm exec-statement-list-of-dead
      (implies (and (statement-list-nofunp stmts)
                    (funenv-nofunp funenv))
               (soutcome-result-okeq
                (exec-statement-list (statement-list-dead stmts)
                                     cstate
                                     (funenv-dead funenv)
                                     limit)
                (exec-statement-list stmts
                                     cstate
                                     funenv
                                     limit)))
      :flag exec-statement-list)

    (defthm exec-block-of-dead
      (implies (and (block-nofunp block)
                    (funenv-nofunp funenv))
               (soutcome-result-okeq
                (exec-block (block-dead block)
                            cstate
                            (funenv-dead funenv)
                            limit)
                (exec-block block
                            cstate
                            funenv
                            limit)))
      :flag exec-block)

    (defthm exec-for-iterations-of-dead
      (implies (and (block-nofunp update)
                    (block-nofunp body)
                    (funenv-nofunp funenv))
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
                                     limit)))
      :flag exec-for-iterations)

    (defthm exec-switch-rest-of-dead
      (implies (and (swcase-list-nofunp cases)
                    (block-option-nofunp default)
                    (funenv-nofunp funenv))
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
                                  limit)))
      :flag exec-switch-rest)

    :hints (exec-of-dead-hints)))
