; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "static-safety-checking")
(include-book "dynamic-semantics")

(include-book "../language/errors")

(local (include-book "../library-extensions/lists"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-soundness
  :parents (language)
  :short "Proof of static soundness of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that if the safety checks in the static semantics are satisfied,
     no dynamic semantics errors can occur during execution,
     except for running out of the artificial limit counter
     (since the static semantics clearly does not check for termination).
     This is a soundness property,
     because the safety checks in the static semantics
     are designed exactly to prevent the occurrence of those errors,
     which the dynamic semantics defensively checks."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-var-list ((vars identifier-listp) (varset identifier-setp))
  :returns (yes/no booleanp)
  :short "Check if the variables in a list are all in a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee check-var) to lists.
     It is not actually part of the formalization of the static safety checks,
     because that formalization uses @(tsee check-var)
     to define @(tsee check-safe-path),
     and then lifts the latter to lists.
     For the static soundness proof,
     it is useful to have this @('check-var-list') function.
     We may refactor the static safety checks to include this function,
     at some point, but for now we just define it here.")
   (xdoc::p
    "We prove a theorem that turns @(tsee check-var-list)
     into the inclusion of the list of variable in the variable table,
     which is a set."))
  (or (endp vars)
      (and (check-var (car vars) varset)
           (check-var-list (cdr vars) varset)))
  :hooks (:fix)
  ///

  (defruled check-var-list-to-set-list-in
    (implies (and (identifier-listp vars)
                  (identifier-setp varset))
             (equal (check-var-list vars varset)
                    (set::list-in vars varset)))
    :enable (check-var
             set::list-in)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-theorems-about-modes
  :short "Theorems about modes for the static soundness proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of enumeration fixtypes like @(tsee mode)
     are usually compared via their kinds (i.e. @(tsee mode-kind)),
     rather than directly;
     the fixtype definition macros in fact generate theorems to this effect,
     along with useful theorems such as the forward chaining rule that
     @(tsee mode-kind) is one of four known possibilities.")
   (xdoc::p
    "However, our ACL2 static safety checking functions return sets of modes
     (for statements, blocks, and other constructs),
     and the static soundness theorems say that
     the mode returned by the ACL2 execution functions are in those sets.
     This set membership formulation does not blend well with
     the kind-centric treatment of modes.
     Thus, here we introduce theorems that
     turn kind comparisons into mode comparisons.
     Because some of the theorems about kinds no longer apply,
     we also need to add some similar theorems for modes,
     and certain explicit non-equality theorems.")
   (xdoc::p
    "This is not very satisfactory.
     There may be a way to avoid all of this,
     and somehow handle mode kinds with set membership well."))

  (defruled equal-of-mode-kind-continue
    (implies (modep mode)
             (equal (equal (mode-kind mode) :continue)
                    (equal mode (mode-continue)))))

  (defruled equal-of-mode-kind-break
    (implies (modep mode)
             (equal (equal (mode-kind mode) :break)
                    (equal mode (mode-break)))))

  (defruled equal-of-mode-kind-regular
    (implies (modep mode)
             (equal (equal (mode-kind mode) :regular)
                    (equal mode (mode-regular)))))

  (defruled equal-of-mode-kind-leave
    (implies (modep mode)
             (equal (equal (mode-kind mode) :leave)
                    (equal mode (mode-leave)))))

  (defruled mode-regular-not-continue
    (not (equal (mode-regular)
                (mode-continue))))

  (defruled mode-regular-not-break
    (not (equal (mode-regular)
                (mode-break))))

  (defruled mode-leave-not-continue
    (not (equal (mode-leave)
                (mode-continue))))

  (defruled mode-leave-not-break
    (not (equal (mode-leave)
                (mode-break))))

  (defruled mode-leave-if-not-regular/continue/break
    (implies (and (modep mode)
                  (not (equal mode (mode-regular)))
                  (not (equal mode (mode-continue)))
                  (not (equal mode (mode-break))))
             (equal (equal mode (mode-leave))
                    t)))

  (defruled mode-possibilities
    (implies (modep x)
             (or (equal x (mode-regular))
                 (equal x (mode-leave))
                 (equal x (mode-break))
                 (equal x (mode-continue)))))

  (defruled soutcome->mode-regular-lemma
    (implies (and (set::in (soutcome->mode outcome) modes)
                  (not (equal (soutcome->mode outcome) (mode-break)))
                  (not (equal (soutcome->mode outcome) (mode-continue)))
                  (not (set::in (mode-leave) modes)))
             (equal (soutcome->mode outcome) (mode-regular)))
    :use (:instance mode-possibilities (x (soutcome->mode outcome)))
    :disable (equal-of-mode-leave
              equal-of-mode-continue
              equal-of-mode-break
              equal-of-mode-regular)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo-to-funtype ((funinfo funinfop))
  :returns (ftype funtypep)
  :short "Turn function information into a function type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function type is the static counterpart of function information.
     We extract the number of inputs and outputs
     from the function information's input and output lists."))
  (b* (((funinfo funinfo) funinfo))
    (make-funtype :in (len funinfo.inputs) :out (len funinfo.outputs)))
  :hooks (:fix)
  ///

  (defruled len-of-funinfo->inputs
    (equal (len (funinfo->inputs funinfo))
           (funtype->in (funinfo-to-funtype funinfo))))

  (defruled len-of-funinfo->outputs
    (equal (len (funinfo->outputs funinfo))
           (funtype->out (funinfo-to-funtype funinfo)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-to-funtable ((funscope funscopep))
  :returns (funtab funtablep)
  :short "Turn a function scope into a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the function information values of the omap into function types.
     They keys of the omap are unchanged.")
   (xdoc::p
    "See @(tsee funenv-to-funtable) for more explanation on
     the purpose of this computation."))
  (b* ((funscope (funscope-fix funscope))
       ((when (omap::emptyp funscope)) nil)
       ((mv name funinfo) (omap::head funscope))
       (funtab (funscope-to-funtable (omap::tail funscope))))
    (omap::update name (funinfo-to-funtype funinfo) funtab))
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule in-of-funscope-to-funtable
    (iff (omap::assoc fun (funscope-to-funtable funscope))
         (omap::assoc fun (funscope-fix funscope))))

  (defrule consp-of-assoc-of-funscope-to-funtable
    (equal (consp (omap::assoc fun (funscope-to-funtable funscope)))
           (consp (omap::assoc fun (funscope-fix funscope)))))

  (defrule keys-of-funscope-to-funtable
    (equal (omap::keys (funscope-to-funtable funscope))
           (omap::keys (funscope-fix funscope))))

  (defruled funscope-to-funtable-of-update
    (implies (and (identifierp fun)
                  (funinfop info)
                  (funscopep funscope))
             (equal (funscope-to-funtable (omap::update fun info funscope))
                    (omap::update fun
                                  (funinfo-to-funtype info)
                                  (funscope-to-funtable funscope))))
    :enable (funscopep
             omap::update
             omap::head
             omap::tail
             omap::mapp)
    :disable (omap::weak-update-induction
              omap::use-weak-update-induction)
    :expand ((funscope-to-funtable (cons (car funscope)
                                         (omap::update fun
                                                       info
                                                       (cdr funscope)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funenv-to-funtable ((funenv funenvp))
  :returns (funtab funtablep)
  :short "Turn a function environment into a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "In formulating the static soundness theorems,
     we need to relate the ACL2 dynamic execution functions,
     which take function environments as arguments,
     with the ACL2 static safety checking functions,
     which take function tables as arguments:
     the function tables are the static counterparts of
     the function environments.
     This ACL2 function carries out this mapping,
     by creating function tables for the function scopes
     and joining them together.
     It is a run-time invariant that
     the function scopes in a function environment have disjoint keys;
     thus, the use of @(tsee omap::update*) is not going to
     overwrite any mappings.
     However, we do not need to require this invariant here,
     as this ACL2 function can be well-defined without it."))
  (b* (((when (endp funenv)) nil)
       (funtab-cdr (funenv-to-funtable (cdr funenv)))
       (funtab-car (funscope-to-funtable (car funenv))))
    (omap::update* funtab-car funtab-cdr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo-safep ((funinfo funinfop) (funtab funtablep))
  :returns (yes/no booleanp)
  :short "Check the safety of function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "A key execution invariant needed for the static soundness proof
     is that, if the code being executed passes the static safety checks,
     then the functions in the function environments pass those checks.
     This predicate captures this notion of safety for function information:
     it performs the same checks as @(tsee check-safe-fundef),
     except that it does so on function information
     instead of a function definition
     (so we could not use @(tsee check-safe-fundef) here,
     because we have no function definition).
     Safety is necessarily checked with respect to some function table.
     See @(tsee funscope-safep) and @(tsee funenv-safep)
     for more information."))
  (b* (((funinfo funinfo) funinfo)
       (varset (add-vars funinfo.inputs nil))
       ((when (reserrp varset)) nil)
       (varset (add-vars funinfo.outputs varset))
       ((when (reserrp varset)) nil)
       (modes (check-safe-block funinfo.body varset funtab))
       ((when (reserrp modes)) nil)
       ((when (set::in (mode-break) modes)) nil)
       ((when (set::in (mode-continue) modes)) nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-safep ((funscope funscopep) (funtab funtablep))
  :returns (yes/no booleanp)
  :short "Check the safety of a function scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee funinfo-safep) for motivation (i.e. the invariant).
     This predicate checks the safety of all the values of the omap."))
  (b* (((when (or (not (mbt (funscopep funscope)))
                  (omap::emptyp funscope)))
        t)
       ((mv & info) (omap::head funscope)))
    (and (funinfo-safep info funtab)
         (funscope-safep (omap::tail funscope) funtab)))
  :hooks (:fix)
  ///

  (defrule funscope-safep-of-update
    (implies (and (identifierp fun)
                  (funinfop funinfo)
                  (funscopep funscope)
                  (funinfo-safep funinfo funtab)
                  (funscope-safep funscope funtab))
             (funscope-safep (omap::update fun funinfo funscope) funtab))
    :enable (funscopep
             omap::update
             omap::head
             omap::tail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funenv-safep ((funenv funenvp))
  :returns (yes/no booleanp)
  :short "Check the safey of a function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The invariant alluded to in @(tsee funinfo-safep) is here defined.
     Recall that a function enviroment is a stack of function scope.
     The invariant is that each function scope is safe
     (i.e. all the functions in the scope are safe)
     with respect to the function table consisting of
     that scope and all the preceding scopes in the stack.
     In fact, as a new function scope is pushed onto the stack,
     the functions are safe with respect to
     not only the functions already in scope,
     but also the functions of the new scope:
     a function is always in its own scope,
     making recursive calls possible."))
  (or (endp funenv)
      (and (funscope-safep (car funenv) (funenv-to-funtable funenv))
           (funenv-safep (cdr funenv))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-theorems-about-find-fun
  :short "Theorems about @(tsee find-fun) for the static soundness proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that if a function environment is safe,
     and if @(tsee find-fun) succeeds in that environment,
     then the resulting function is safe.
     We prove this for function scopes first,
     then for function environments.
     The latter is an important theorem to use in the static soundness proof:
     it serves to establish the safety of a function's body,
     when executing the function,
     so that the static soundness inductive hypothesis about the function
     applies, i.e. tells us that the execution of the body
     will not return an error result.")
   (xdoc::p
    "We also prove certain properties that relate
     @(tsee get-funtype) and @(tsee find-fun),
     which are static/dynamic counterparts."))

  (defruled check-safe-block-when-funscope-safep
    (implies (and (identifierp fun)
                  (funscopep funscope)
                  (funscope-safep funscope funtab)
                  (consp (omap::assoc fun funscope)))
             (b* ((funinfo (cdr (omap::assoc fun funscope)))
                  (varset0 (add-vars (funinfo->inputs funinfo) nil))
                  (varset (add-vars (funinfo->outputs funinfo) varset0))
                  (modes (check-safe-block (funinfo->body funinfo)
                                           varset
                                           funtab)))
               (and (not (reserrp varset0))
                    (not (reserrp varset))
                    (not (reserrp modes))
                    (not (set::in (mode-break) modes))
                    (not (set::in (mode-continue) modes)))))
    :enable (funscope-safep
             funinfo-safep))

  (defruled check-safe-block-when-funenv-safep
    (b* ((funinfoenv (find-fun fun funenv)))
      (implies (and (funenv-safep funenv)
                    (not (reserrp funinfoenv)))
               (b* ((funinfo (funinfo+funenv->info funinfoenv))
                    (funenv1 (funinfo+funenv->env funinfoenv))
                    (varset0 (add-vars (funinfo->inputs funinfo) nil))
                    (varset (add-vars (funinfo->outputs funinfo) varset0))
                    (modes (check-safe-block (funinfo->body funinfo)
                                             varset
                                             (funenv-to-funtable funenv1))))
                 (and (not (reserrp varset0))
                      (not (reserrp varset))
                      (not (reserrp modes))
                      (not (set::in (mode-break) modes))
                      (not (set::in (mode-continue) modes))
                      (funenv-safep funenv1)))))
    :enable (find-fun
             funenv-safep)
    :hints ('(:use (:instance check-safe-block-when-funscope-safep
                              (fun (identifier-fix fun))
                              (funscope (funscope-fix (car funenv)))
                              (funtab (funenv-to-funtable funenv))))))

  (defruled funinfo-to-funtype-of-cdr-of-in
    (implies (and (funscopep funscope)
                  (consp (omap::assoc fun funscope)))
             (equal (funinfo-to-funtype (cdr (omap::assoc fun funscope)))
                    (cdr (omap::assoc fun (funscope-to-funtable funscope)))))
    :enable funscope-to-funtable)

  (defrule funinfo-to-funtype-of-find-fun-info
    (b* ((funinfoenv (find-fun fun funenv))
         (funtype (get-funtype fun (funenv-to-funtable funenv))))
      (implies (not (reserrp funinfoenv))
               (b* ((funinfo (funinfo+funenv->info funinfoenv)))
                 (and (not (reserrp funtype))
                      (equal (funinfo-to-funtype funinfo)
                             funtype)))))
    :expand (funenv-to-funtable funenv)
    :enable (find-fun
             funenv-to-funtable
             get-funtype
             funinfo-to-funtype-of-cdr-of-in
             not-reserrp-when-funtypep
             funtypep-when-funtype-resultp-and-not-reserrp)
    :prep-lemmas
    ((defrule lemma
       (implies (and (funtablep funtab)
                     (consp (omap::assoc fun funtab)))
                (funtypep (cdr (omap::assoc fun funtab)))))))

  (defruled reserrp-of-find-fun
    (equal (reserrp (find-fun fun funenv))
           (reserrp (get-funtype fun (funenv-to-funtable funenv))))
    :enable (funenv-to-funtable
             find-fun
             get-funtype
             not-reserrp-when-funinfo+funenv-p
             not-reserrp-when-funtypep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-theorems-about-add-funs
  :short "Theorems about @(tsee add-funs) for the static soundness proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to how @(tsee get-funtype) and @(tsee find-fun)
     are static/dynamic counterparts,
     so @(tsee add-funtypes) and @(tsee add-funs)
     are static/dynamic counterparts.
     Here we prove theorems that relate the latter two,
     or that relate functions that the latter two are built on.")
   (xdoc::p
    "We also prove theorems about the preservation of
     the safety invariant of function environments.
     Essentially, given a safe function environments,
     if we extend it with a new scope whose functions
     are safe in the function table that also includes those functions,
     we push a scope into the stack that satisfies the invariant;
     and furthermore, the existing scopes still satisfy the invariant,
     because the invariant only refers to the current and earlier scopes,
     not to later ones that are pushed."))

  (defrule funinfo-to-funtype-of-funinfo-for-fundef
    (equal (funinfo-to-funtype (funinfo-for-fundef fundef))
           (funtype-for-fundef fundef))
    :enable (funinfo-to-funtype
             funinfo-for-fundef
             funtype-for-fundef))

  (defruled in-funscope-for-fundefs-iff-in-funtable-for-fundefs
    (implies (and (not (reserrp (funscope-for-fundefs fundefs)))
                  (not (reserrp (funtable-for-fundefs fundefs))))
             (equal (consp (omap::assoc fun (funscope-for-fundefs fundefs)))
                    (consp (omap::assoc fun (funtable-for-fundefs fundefs)))))
    :enable (funscope-for-fundefs
             funtable-for-fundefs))

  (defruled error-funscope-for-fundefs-iff-error-funtable-for-fundefs
    (equal (reserrp (funscope-for-fundefs fundefs))
           (reserrp (funtable-for-fundefs fundefs)))
    :enable (funscope-for-fundefs
             funtable-for-fundefs
             funtablep-when-funtable-resultp-and-not-reserrp
             not-reserrp-when-funtablep
             in-funscope-for-fundefs-iff-in-funtable-for-fundefs))

  (defrule funscope-to-funtable-of-funscope-for-fundefs
    (implies (not (reserrp (funscope-for-fundefs fundefs)))
             (equal (funscope-to-funtable (funscope-for-fundefs fundefs))
                    (funtable-for-fundefs fundefs)))
    :enable (funscope-to-funtable
             funscope-for-fundefs
             funtable-for-fundefs
             error-funscope-for-fundefs-iff-error-funtable-for-fundefs
             funscopep-when-funscope-resultp-and-not-reserrp
             funscope-to-funtable-of-update
             in-funscope-for-fundefs-iff-in-funtable-for-fundefs))

  (defruled keys-of-funscope-for-fundefs-is-keys-of-funtable-for-fundefs
    (implies (and (not (reserrp (funscope-for-fundefs fundefs)))
                  (not (reserrp (funtable-for-fundefs fundefs))))
             (equal (omap::keys (funscope-for-fundefs fundefs))
                    (omap::keys (funtable-for-fundefs fundefs))))
    :enable (funscope-for-fundefs
             funtable-for-fundefs))

  (defrule funenv-to-funtable-of-add-funs
    (implies (not (reserrp (add-funs fundefs funenv)))
             (equal (funenv-to-funtable (add-funs fundefs funenv))
                    (add-funtypes fundefs (funenv-to-funtable funenv))))
    :enable (add-funs
             add-funtypes
             funenv-to-funtable
             error-funscope-for-fundefs-iff-error-funtable-for-fundefs
             ensure-funscope-disjoint
             not-reserrp-when-funenvp
             funscopep-when-funscope-resultp-and-not-reserrp
             keys-of-funscope-for-fundefs-is-keys-of-funtable-for-fundefs
             set::intersect-of-union))

  (defruled error-add-funs-iff-error-add-funtypes
    (equal (reserrp (add-funs fundefs funenv))
           (reserrp (add-funtypes fundefs (funenv-to-funtable funenv))))
    :enable (add-funs
             add-funtypes
             funenv-to-funtable
             error-funscope-for-fundefs-iff-error-funtable-for-fundefs
             ensure-funscope-disjoint
             not-reserrp-when-funenvp
             funscopep-when-funscope-resultp-and-not-reserrp
             keys-of-funscope-for-fundefs-is-keys-of-funtable-for-fundefs
             set::intersect-of-union
             funtablep-when-funtable-resultp-and-not-reserrp))

  (defrule funinfo-safep-of-funinfo-for-fundef
    (implies (not (reserrp (check-safe-fundef fundef funtab)))
             (funinfo-safep (funinfo-for-fundef fundef) funtab))
    :enable (funinfo-safep
             check-safe-fundef
             funinfo-for-fundef))

  (defrule funscope-safep-of-funscope-for-fundefs
    (implies (and (not (reserrp (check-safe-fundef-list fundefs funtab)))
                  (not (reserrp (funscope-for-fundefs fundefs))))
             (funscope-safep (funscope-for-fundefs fundefs) funtab))
    :enable (funscope-safep
             funscope-for-fundefs
             check-safe-fundef-list
             funscopep-when-funscope-resultp-and-not-reserrp))

  (defruled car-of-add-funs
    (implies (not (reserrp (add-funs fundefs funenv)))
             (equal (car (add-funs fundefs funenv))
                    (funscope-for-fundefs fundefs)))
    :enable add-funs)

  (defruled cdr-of-add-funs
    (implies (not (reserrp (add-funs fundefs funenv)))
             (equal (cdr (add-funs fundefs funenv))
                    (funenv-fix funenv)))
    :enable add-funs)

  (defruled not-error-funscope-for-fundefs-when-not-error-add-funs
    (implies (not (reserrp (add-funs fundefs funenv)))
             (not (reserrp (funscope-for-fundefs fundefs))))
    :enable add-funs)

  (defrule funenv-safep-of-add-funs
    (implies (and (funenv-safep funenv)
                  (not (reserrp (add-funs fundefs funenv)))
                  (not (reserrp
                        (check-safe-fundef-list
                         fundefs
                         (add-funtypes fundefs (funenv-to-funtable funenv))))))
             (funenv-safep (add-funs fundefs funenv)))
    :expand (funenv-safep (add-funs fundefs funenv))
    :enable (not-error-funscope-for-fundefs-when-not-error-add-funs
             car-of-add-funs
             cdr-of-add-funs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cstate-to-vars ((cstate cstatep))
  :returns (varset identifier-setp)
  :short "Turn a computation state into a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable table is the static counterpart of
     the local state of a computation state in the dynamic execution.
     The variable table consists of the keys of the omap.")
   (xdoc::p
    "We prove a theorem to fold the body of this function
     into the function call.
     This is the opposite of unfolding the definition.
     We use this rule in the main static soundness theorem.
     This rule is not very satisfactory;
     we will look into avoiding it in some way."))
  (omap::keys (cstate->local cstate))
  :hooks (:fix)
  ///

  (defruled cstate-to-vars-fold-def
    (equal (omap::keys (cstate->local cstate))
           (cstate-to-vars cstate))
    :enable cstate-to-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-cstate-to-vars-and-execution
  :short "Theorems about @(tsee cstate-to-vars) and execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove theorems saying how the execution functions,
     and the auxiliary functions they use,
     operate on the variable tables obtained from the computation states.
     Many functions leave the variable table unchanged;
     some extend it, which we express via @(tsee set::subset).
     In the case of @(tsee restrict-vars),
     the theorem provides the exact result.")
   (xdoc::p
    "For the @(tsee set::subset) cases,
     we could prove more precise results, in terms of set operations;
     we had that during the development of the static soundness proof,
     but at some point it seemed that the @(tsee set::subset) formulation
     was more convenient.
     This is somewhat undesirable though:
     it seems more principled and clear to calculate the exact variable tables,
     rather than just constraining them to be superset.
     We will revisit this, seeing if we can keep the proof working
     with the theorems reformulated
     (perhaps this may actually make the overall proof simpler).")
   (xdoc::p
    "Note the use of the @('cstate-to-vars-fold-def') rule
     in the mutual induction proof below.
     This rule, and its undesirability,
     is discussed in @(tsee cstate-to-vars).
     This might be actually related to the issue
     discussed in the paragraph just above."))

  (defrule cstate-to-vars-of-write-var-value
    (b* ((cstate1 (write-var-value var val cstate)))
      (implies (not (reserrp cstate1))
               (equal (cstate-to-vars cstate1)
                      (cstate-to-vars cstate))))
    :enable (write-var-value
             cstate-to-vars
             omap::consp-of-assoc-to-in-of-keys))

  (defrule cstate-to-vars-of-write-vars-values
    (b* ((cstate1 (write-vars-values vars vals cstate)))
      (implies (not (reserrp cstate1))
               (equal (cstate-to-vars cstate1)
                      (cstate-to-vars cstate))))
    :enable write-vars-values)

  (defrule cstate-to-vars-of-restrict-vars
    (equal (cstate-to-vars (restrict-vars vars cstate))
           (set::intersect (identifier-set-fix vars)
                           (cstate-to-vars cstate)))
    :enable (cstate-to-vars
             restrict-vars))

  (defrule cstate-to-vars-of-add-var-value
    (b* ((cstate1 (add-var-value var val cstate)))
      (implies (not (reserrp cstate1))
               (equal (cstate-to-vars cstate1)
                      (set::insert (identifier-fix var)
                                   (cstate-to-vars cstate)))))
    :enable (add-var-value
             cstate-to-vars))

  (defrule cstate-to-vars-of-add-vars-values
    (b* ((cstate1 (add-vars-values vars vals cstate)))
      (implies (not (reserrp cstate1))
               (equal (cstate-to-vars cstate1)
                      (set::list-insert (identifier-list-fix vars)
                                        (cstate-to-vars cstate)))))
    :enable (add-vars-values
             set::list-insert))

  (defrule cstate-to-vars-of-exec-literal
    (b* ((outcome (exec-literal lit cstate)))
      (implies (not (reserrp outcome))
               (equal (cstate-to-vars (eoutcome->cstate outcome))
                      (cstate-to-vars cstate))))
    :enable exec-literal)

  (defrule cstate-to-vars-of-exec-path
    (b* ((outcome (exec-path path cstate)))
      (implies (not (reserrp outcome))
               (equal (cstate-to-vars (eoutcome->cstate outcome))
                      (cstate-to-vars cstate))))
    :enable exec-path)

  (defthm-exec-flag

    (defthm cstate-to-vars-of-exec-expression
      (b* ((outcome (exec-expression expr cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (eoutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-expression)

    (defthm cstate-to-vars-of-exec-expression-list
      (b* ((outcome (exec-expression-list exprs cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (eoutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-expression-list)

    (defthm cstate-to-vars-of-exec-funcall
      (b* ((outcome (exec-funcall call cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (eoutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-funcall)

    (defthm cstate-to-vars-of-exec-function
      (b* ((outcome (exec-function fun args cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (eoutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-function)

    (defthm cstate-to-vars-of-exec-statement
      (b* ((outcome (exec-statement stmt cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (set::subset (cstate-to-vars cstate)
                              (cstate-to-vars
                               (soutcome->cstate outcome)))))
      :flag exec-statement)

    (defthm cstate-to-vars-of-exec-statement-list
      (b* ((outcome (exec-statement-list stmts cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (set::subset (cstate-to-vars cstate)
                              (cstate-to-vars
                               (soutcome->cstate outcome)))))
      :flag exec-statement-list)

    (defthm cstate-to-vars-of-exec-block
      (b* ((outcome (exec-block block cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (soutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-block)

    (defthm cstate-to-vars-of-exec-for-iterations
      (b* ((outcome (exec-for-iterations test update body cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (soutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-for-iterations)

    (defthm cstate-to-vars-of-exec-switch-rest
      (b* ((outcome (exec-switch-rest cases default target cstate funenv limit)))
        (implies (not (reserrp outcome))
                 (equal (cstate-to-vars (soutcome->cstate outcome))
                        (cstate-to-vars cstate))))
      :flag exec-switch-rest)

    :hints (("Goal" :in-theory (enable exec-expression
                                       exec-expression-list
                                       exec-funcall
                                       exec-function
                                       exec-statement
                                       exec-statement-list
                                       exec-block
                                       exec-for-iterations
                                       exec-switch-rest
                                       set::subset-transitive
                                       cstate-to-vars-fold-def
                                       set::intersect-with-subset-left)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-of-variable-reading
  :short "Theorems about the static soundness of variable reading."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee check-var) and @(tsee check-var-list) succeed,
     also @(tsee read-var-value) and @(tsee read-vars-values) do."))

  (defruled read-var-value-when-check-var
    (implies (check-var var (cstate-to-vars cstate))
             (not (reserrp (read-var-value var cstate))))
    :enable (check-var
             read-var-value
             not-reserrp-when-valuep
             cstate-to-vars
             omap::consp-of-assoc-to-in-of-keys))

  (defruled read-vars-values-when-check-var-list
    (implies (check-var-list vars (cstate-to-vars cstate))
             (not (reserrp (read-vars-values vars cstate))))
    :enable (check-var-list
             read-vars-values
             valuep-when-value-resultp-and-not-reserrp
             not-reserrp-when-value-listp
             value-listp-when-value-list-resultp-and-not-reserrp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-of-variable-addition
  :short "Theorems about the static soundness of variable addition."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee add-var) and @(tsee add-vars) succeed,
     also @(tsee add-var-value) and @(tsee add-vars-values) do.
     Furthermore, the variable table for the resulting computation states
     is the same returned by the safety checks."))

  (defrule add-var-value-when-add-var
    (b* ((varset1 (add-var var (cstate-to-vars cstate)))
         (cstate1 (add-var-value var val cstate)))
      (implies (not (reserrp varset1))
               (and (not (reserrp cstate1))
                    (equal (cstate-to-vars cstate1)
                           varset1))))
    :enable (add-var
             add-var-value
             cstate-to-vars
             omap::consp-of-assoc-to-in-of-keys))

  (defrule add-vars-values-when-add-vars
    (b* ((varset1 (add-vars vars (cstate-to-vars cstate)))
         (cstate1 (add-vars-values vars vals cstate)))
      (implies (and (not (reserrp varset1))
                    (equal (len vals) (len vars)))
               (and (not (reserrp cstate1))
                    (equal (cstate-to-vars cstate1)
                           varset1))))
    :induct (add-vars-values vars vals cstate)
    :enable (add-vars
             add-vars-values
             add-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-of-variable-writing
  :short "Theorems about the static soundness of variable writing."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee check-safe-path) and @(tsee check-safe-path-list) succeeds,
     also @(tsee write-var-value) and @(tsee write-vars-values) do.
     These are proved by showing that path checking
     ensures the success of @(tsee path-to-var) and @(tsee paths-to-vars),
     and also the success of @(tsee check-var) and @(tsee check-var-list).
     Then we show that @(tsee check-var) and @(tsee check-var-list)
     ensure that @(tsee write-var-value) and @(tsee write-vars-values) succeed,
     and finally we put things together."))

  (defrule path-to-var-when-check-safe-path
    (implies (not (reserrp (check-safe-path path varset)))
             (not (reserrp (path-to-var path))))
    :enable (check-safe-path
             path-to-var
             not-reserrp-when-identifierp))

  (defrule check-var-when-check-safe-path
    (implies (not (reserrp (check-safe-path path varset)))
             (check-var (path-to-var path) varset))
    :enable (check-safe-path
             path-to-var))

  (defrule paths-to-vars-when-check-safe-path-list
    (implies (not (reserrp (check-safe-path-list paths varset)))
             (not (reserrp (paths-to-vars paths))))
    :enable (check-safe-path-list
             paths-to-vars)
    :expand (reserrp (cons (path-to-var (car paths))
                           (paths-to-vars (cdr paths)))))

  (defrule check-var-list-when-check-safe-path-list
    (implies (not (reserrp (check-safe-path-list paths varset)))
             (check-var-list (paths-to-vars paths) varset))
    :enable (check-safe-path-list
             check-var-list
             paths-to-vars))

  (defrule write-var-value-when-check-var
    (implies (check-var var (cstate-to-vars cstate))
             (not (reserrp (write-var-value var val cstate))))
    :enable (write-var-value
             check-var
             cstate-to-vars
             omap::consp-of-assoc-to-in-of-keys))

  (defrule write-var-value-when-check-safe-path
    (implies (not (reserrp
                   (check-safe-path path (cstate-to-vars cstate))))
             (not (reserrp
                   (write-var-value (path-to-var path) val cstate)))))

  (defrule write-vars-values-when-check-var-list
    (implies (and (check-var-list vars (cstate-to-vars cstate))
                  (equal (len vals) (len vars)))
             (not (reserrp (write-vars-values vars vals cstate))))
    :enable (check-var-list
             write-vars-values))

  (defrule write-vars-values-when-check-safe-path-list
    (implies (and (not (reserrp
                        (check-safe-path-list paths
                                              (cstate-to-vars cstate))))
                  (equal (len vals) (len paths)))
             (not (reserrp
                   (write-vars-values (paths-to-vars paths) vals cstate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-theorems-about-init-local
  :short "Theorems about @(tsee init-local) for the static soundness proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some of these are actually more general and could be moved.
     These more general theorems are about adding variables,
     which is what @(tsee init-local) does for the local state of course.")
   (xdoc::p
    "First, we show that @(tsee add-var-value) fails iff @(tsee add-var) does
     (the value put into the variable entails no constraints),
     and the same holds for @(tsee add-vars-values) and @(tsee add-vars)
     provided that the number of values matches the number of variables.")
   (xdoc::p
    "We prove a theorem that characterizes the effect of @(tsee init-local)
     on the variable table of the computation state.
     This should belong to
     the theorems in @(see theorems-about-cstate-to-vars-and-execution),
     and it can probably put there, but currently it needs some other theorems,
     but it may be possible to streamline and simplify its proof.")
   (xdoc::p
    "The theorem @('check-var-list-when-add-vars-not-error')
     serves to establish that the output variables of a function are readable
     given that they have been added via @(tsee init-local).
     This is not really a theorem about @(tsee init-local), but it is related;
     nonetheless, we may move this theorem at some point.")
   (xdoc::p
    "We finally show that @(tsee init-local) fails iff
     the addition of the variables to the variable table fails,
     or the number of values does not match the number of variables."))

  (defruled error-add-var-value-iff-error-add-var
    (equal (reserrp (add-var-value var val cstate))
           (reserrp (add-var var (cstate-to-vars cstate))))
    :enable (add-var
             add-var-value
             cstate-to-vars
             omap::consp-of-assoc-to-in-of-keys
             not-reserrp-when-cstatep
             not-reserrp-when-identifier-setp))

  (defruled error-add-vars-values-iff-error-add-vars
    (implies (equal (len vals) (len vars))
             (equal (reserrp (add-vars-values vars vals cstate))
                    (reserrp (add-vars vars (cstate-to-vars cstate)))))
    :enable (add-vars-values
             add-vars
             error-add-var-value-iff-error-add-var
             not-reserrp-when-identifier-setp))

  (defrule cstate-to-vars-of-init-local
    (implies (and (equal (len in-vals)
                         (len in-vars))
                  (not (reserrp
                        (init-local in-vars in-vals out-vars cstate))))
             (equal (cstate-to-vars
                     (init-local in-vars in-vals out-vars cstate))
                    (add-vars out-vars (add-vars in-vars nil))))
    :enable (init-local
             error-add-vars-values-iff-error-add-vars))

  (defruled check-var-list-when-add-vars-not-error
    (implies (and (identifier-listp vars)
                  (identifier-setp varset)
                  (not (reserrp (add-vars vars varset))))
             (check-var-list vars (add-vars vars varset)))
    :enable (add-vars-to-set-list-insert
             check-var-list-to-set-list-in))

  (defruled reserrp-of-init-local
    (equal (reserrp (init-local in-vars in-vals out-vars cstate))
           (or (reserrp (add-vars in-vars nil))
               (reserrp (add-vars out-vars (add-vars in-vars nil)))
               (not (equal (len in-vals) (len in-vars)))))
    :cases ((equal (len in-vals) (len in-vars)))
    :enable (init-local
             error-add-vars-values-iff-error-add-vars)
    :prep-lemmas
    ((defrule lemma
       (implies (not (equal (len vals) (len vars)))
                (reserrp (add-vars-values vars vals cstate)))
       :enable add-vars-values))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-checking-expression-lists-in-reverse
  :short "Theorems about @(tsee check-safe-expression-list) and @(tsee rev)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lists of expressions are used as function arguments.
     The static semantics checks them in order,
     while the dynamic semantics executes them in reverse
     (see @(tsee exec-funcall).
     Since execution may have side effect, order is important.
     However, it is appropriate, and simpler, for the static semantics
     to check expressions in order without reversing them:
     the result is the same.")
   (xdoc::p
    "However, this creates a ``gap'' that needs to be bridged
     in the static soundness proof.
     We do that with the theorems below.
     The first serves to prove the second.
     The third is a good simplification rule.
     The fourth is awkward, but it is currently needed
     to discharge a hypothesis in the main proof;
     without this, the third theorem rewrites away some relevant term."))

  (defrule reserrp-of-check-safe-expression-list-of-append
    (equal (reserrp (check-safe-expression-list (append es es1)
                                                varset
                                                funtab))
           (or (reserrp (check-safe-expression-list es varset funtab))
               (reserrp (check-safe-expression-list es1 varset funtab))))
    :enable check-safe-expression-list)

  (defrule reserrp-of-check-safe-expression-list-of-rev
    (equal (reserrp (check-safe-expression-list (rev es) varset funtab))
           (reserrp (check-safe-expression-list es varset funtab)))
    :enable (check-safe-expression-list rev))

  (defruled check-safe-expression-list-to-len
    (implies (not (reserrp (check-safe-expression-list es varset funtab)))
             (equal (check-safe-expression-list es varset funtab) (len es)))
    :enable check-safe-expression-list)

  (defruled check-safe-expression-list-not-error-when-rev
    (implies (not (reserrp (check-safe-expression-list (rev es)
                                                       varset
                                                       funtab)))
             (not (reserrp (check-safe-expression-list es varset funtab))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-of-literal-execution
  :short "Theorem about the static soundness of literal execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is very simple, because both static and dynamic semantics
     evaluate the literal.")
   (xdoc::p
    "We also show that it returns one value."))

  (defrule exec-literal-when-check-safe-literal
    (implies (not (reserrp (check-safe-literal lit)))
             (b* ((outcome (exec-literal lit cstate)))
               (and (not (reserrp outcome))
                    (equal (eoutcome->cstate outcome)
                           (cstate-fix cstate))
                    (equal (len (eoutcome->values outcome))
                           1))))
    :enable (check-safe-literal
             exec-literal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundness-of-path-execution
  :short "Theorem about the static soundness of path execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is fairly easy, and relies on
     the theorem about @(tsee read-var-value) and @(tsee check-var)."))

  (defrule exec-path-when-check-safe-path
    (implies (not (reserrp
                   (check-safe-path path (cstate-to-vars cstate))))
             (b* ((outcome (exec-path path cstate)))
               (and (not (reserrp outcome))
                    (equal (eoutcome->cstate outcome)
                           (cstate-fix cstate))
                    (equal (len (eoutcome->values outcome))
                           1))))
    :enable (check-safe-path
             exec-path
             path-to-var
             not-reserrp-when-valuep
             not-reserrp-when-identifierp
             read-var-value-when-check-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection static-soundess-of-execution
  :short "Main static soundness theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are about the mutually recursive execution functions.
     Each theorem says that if the static safety checks succeed,
     with respect to the variable table for the computation state
     and the function table for the function environment,
     if the function environment is safe,
     and if the execution function does not return a limit error,
     then the execution function does not return an error,
     and the outcome is consistent with the result of the safety checks:
     for expressions, the number of values matches the calculated number;
     for statements (and blocks etc.), the mode is in the calculated set.")
   (xdoc::p
    "We currently have an undesired lemma that is
     somewhat specific to one of the arising subgoals.
     We plan to look into avoiding this.")
   (xdoc::p
    "The hints for the main inductive theorem mainly consist in
     enabling certain functions and theorems.
     We obviously enable the execution and checking functions;
     unfortunately we also need an @(':expand') hint,
     as just enabling the functions is not enough, apparently.
     We also enable @(tsee reserr-limitp),
     so the cases in which execution returns a limit error
     are quickly resolved away.
     We enable the mode theorems discussed in
     @(see static-soundness-theorems-about-modes);
     we also need to disable theorems, generated by the fixtype definition,
     that would otherwise interfere with these theorems.
     We enable the awkward @('cstate-to-vars-fold-def'),
     which is needed for the somewhat specific lemma below,
     which we also enable.
     We enable two @('<option-fixtype>-some->val') functions,
     which reduce to identities.
     We enable the theorems about reversed expression lists
     discussed in @(see theorems-about-checking-expression-lists-in-reverse).
     The remaining enabled theorems are motivated by the subgoals, as common;
     perhaps they could be rationalized and explained better.")
   (xdoc::p
    "As is often the case,
     the proof also makes implicit use of enabled-by-default rules.
     Some are theorems that relate static and dynamic counterparts.
     We also remark the use of the @('...-extends-varset') theorems
     that accompany the static safety checking formalization."))

  (defruled exec-statement-list-cstate-to-vars-lemma
    (implies (and (not (reserrp (add-funs (statements-to-fundefs stmts)
                                          funenv)))
                  (not (reserrp (exec-statement-list
                                 stmts
                                 cstate
                                 (add-funs (statements-to-fundefs stmts)
                                           funenv)
                                 limit))))
             (equal (intersect
                     (cstate-to-vars cstate)
                     (cstate-to-vars
                      (soutcome->cstate
                       (exec-statement-list stmts
                                            cstate
                                            (add-funs
                                             (statements-to-fundefs stmts)
                                             funenv)
                                            limit))))
                    (cstate-to-vars cstate)))
    :use (:instance cstate-to-vars-of-exec-statement-list
                    (cstate (add-funs (statements-to-fundefs stmts) funenv)))
    :enable set::intersect-with-subset-left)

  (defthm-exec-flag

    (defthm exec-expression-static-soundness
      (b* ((results (check-safe-expression expr
                                           (cstate-to-vars cstate)
                                           (funenv-to-funtable funenv)))
           (outcome (exec-expression expr cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp results))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (eoutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (equal (len (eoutcome->values outcome))
                             results))))
      :flag exec-expression)

    (defthm exec-expression-list-static-soundness
      (b* ((results (check-safe-expression-list exprs
                                                (cstate-to-vars cstate)
                                                (funenv-to-funtable funenv)))
           (outcome (exec-expression-list exprs cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp results))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (eoutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (equal (len (eoutcome->values outcome))
                             results))))
      :flag exec-expression-list)

    (defthm exec-funcall-static-soundness
      (b* ((results (check-safe-funcall call
                                        (cstate-to-vars cstate)
                                        (funenv-to-funtable funenv)))
           (outcome (exec-funcall call cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp results))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (eoutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (equal (len (eoutcome->values outcome))
                             results))))
      :flag exec-funcall)

    (defthm exec-function-static-soundness
      (b* ((ftype (get-funtype fun (funenv-to-funtable funenv)))
           (outcome (exec-function fun args cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp ftype))
                      (equal (len args)
                             (funtype->in ftype))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (eoutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (equal (len (eoutcome->values outcome))
                             (funtype->out ftype)))))
      :flag exec-function)

    (defthm exec-statement-static-soundness
      (b* ((varsmodes (check-safe-statement stmt
                                            (cstate-to-vars cstate)
                                            (funenv-to-funtable funenv)))
           (outcome (exec-statement stmt cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp varsmodes))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (soutcome->cstate outcome))
                             (vars+modes->vars varsmodes))
                      (set::in (soutcome->mode outcome)
                               (vars+modes->modes varsmodes)))))
      :flag exec-statement)

    (defthm exec-statement-list-static-soundness
      (b* ((varsmodes (check-safe-statement-list stmts
                                                 (cstate-to-vars cstate)
                                                 (funenv-to-funtable funenv)))
           (outcome (exec-statement-list stmts cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp varsmodes))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (if (equal (soutcome->mode outcome)
                                 (mode-regular))
                          (equal (cstate-to-vars (soutcome->cstate outcome))
                                 (vars+modes->vars varsmodes))
                        (set::subset (cstate-to-vars (soutcome->cstate outcome))
                                     (vars+modes->vars varsmodes)))
                      (set::in (soutcome->mode outcome)
                               (vars+modes->modes varsmodes)))))
      :flag exec-statement-list)

    (defthm exec-block-static-soundness
      (b* ((modes (check-safe-block block
                                    (cstate-to-vars cstate)
                                    (funenv-to-funtable funenv)))
           (outcome (exec-block block cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp modes))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (soutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (set::in (soutcome->mode outcome)
                               modes))))
      :flag exec-block)

    (defthm exec-for-iterations-static-soundness
      (b* ((test-results (check-safe-expression test
                                                (cstate-to-vars cstate)
                                                (funenv-to-funtable funenv)))
           (update-modes (check-safe-block update
                                           (cstate-to-vars cstate)
                                           (funenv-to-funtable funenv)))
           (body-modes (check-safe-block body
                                         (cstate-to-vars cstate)
                                         (funenv-to-funtable funenv)))
           (outcome (exec-for-iterations test update body cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp test-results))
                      (equal test-results 1)
                      (not (reserrp update-modes))
                      (not (set::in (mode-break) update-modes))
                      (not (set::in (mode-continue) update-modes))
                      (not (reserrp body-modes))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (soutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (set::in (soutcome->mode outcome)
                               (set::difference
                                (set::insert (mode-regular)
                                             (set::union body-modes update-modes))
                                (set::insert (mode-break)
                                             (set::insert (mode-continue)
                                                          nil)))))))
      :flag exec-for-iterations)

    (defthm exec-switch-rest-static-soundness
      (b* ((cases-modes (check-safe-swcase-list cases
                                                (cstate-to-vars cstate)
                                                (funenv-to-funtable funenv)))
           (default-modes (check-safe-block-option default
                                                   (cstate-to-vars cstate)
                                                   (funenv-to-funtable funenv)))
           (outcome (exec-switch-rest cases default target cstate funenv limit)))
        (implies (and (funenv-safep funenv)
                      (not (reserrp cases-modes))
                      (not (reserrp default-modes))
                      (not (reserr-limitp outcome)))
                 (and (not (reserrp outcome))
                      (equal (cstate-to-vars (soutcome->cstate outcome))
                             (cstate-to-vars cstate))
                      (set::in (soutcome->mode outcome)
                               (set::union cases-modes default-modes)))))
      :flag exec-switch-rest)

    :hints (("Goal"
             :in-theory
             (e/d
              (exec-expression
               exec-expression-list
               exec-funcall
               exec-function
               exec-statement
               exec-statement-list
               exec-block
               exec-for-iterations
               exec-switch-rest
               check-safe-expression
               check-safe-expression-list
               check-safe-funcall
               check-safe-statement
               check-safe-variable-single
               check-safe-variable-multi
               check-safe-assign-single
               check-safe-assign-multi
               check-safe-statement-list
               check-safe-block
               check-safe-block-option
               check-safe-swcase
               check-safe-swcase-list
               check-safe-literal
               reserr-limitp
               reserr-limitp-aux
               equal-of-mode-kind-continue
               equal-of-mode-kind-break
               equal-of-mode-kind-leave
               equal-of-mode-kind-regular
               mode-regular-not-continue
               mode-regular-not-break
               mode-leave-not-continue
               mode-leave-not-break
               soutcome->mode-regular-lemma
               cstate-to-vars-fold-def
               exec-statement-list-cstate-to-vars-lemma
               funcall-option-some->val
               expression-option-some->val
               check-safe-expression-list-to-len
               check-safe-expression-list-not-error-when-rev
               error-add-funs-iff-error-add-funtypes
               check-safe-fundef-list-of-statements-to-fundefs
               error-add-funs-iff-error-add-funtypes
               mode-setp-when-mode-set-resultp-and-not-reserrp
               mode-leave-if-not-regular/continue/break
               identifier-setp-when-identifier-set-resultp-and-not-reserrp
               check-safe-block-when-funenv-safep
               len-of-funinfo->inputs
               len-of-funinfo->outputs
               read-vars-values-when-check-var-list
               check-var-list-when-add-vars-not-error
               cstate-to-vars-of-init-local
               reserrp-of-init-local
               reserrp-of-find-fun)
              (equal-of-mode-continue
               equal-of-mode-break
               equal-of-mode-regular
               equal-of-mode-leave))
             :expand ((check-safe-statement stmt
                                            (cstate-to-vars cstate)
                                            (funenv-to-funtable funenv)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule exec-top-block-static-soundness
  :short "Top-level static soundness theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to the top-level block.
     If the block is safe,
     then its execution can only return either a final state
     or a limit error, never any other kind of error."))
  (implies (not (reserrp (check-safe-top-block block)))
           (b* ((cstate (exec-top-block block limit)))
             (implies (not (reserr-limitp cstate))
                      (not (reserrp cstate)))))
  :enable (check-safe-top-block
           exec-top-block
           reserr-limitp
           reserr-limitp-aux)
  :disable exec-block-static-soundness
  :use (:instance exec-block-static-soundness
                  (cstate (cstate nil))
                  (funenv nil)))
