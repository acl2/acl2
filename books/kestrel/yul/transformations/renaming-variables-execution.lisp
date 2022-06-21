; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "renaming-variables")

(include-book "../language/dynamic-semantics")
(include-book "../language/errors")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "../library-extensions/alists"))
(local (include-book "../library-extensions/omaps"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming-variables-execution
  :parents (renaming-variables)
  :short "Proof that variable renaming preserves the execution behavior."
  :long
  (xdoc::topstring
   (xdoc::p
    "We start by extending the variable renaming relation
     from the abstract syntax to the dynamic semantic entities,
     namely function environments and computation states
     (and their constituents).
     For these, we define the relation as a predicate,
     instead of a function that may return errors,
     as we never need to return anything if the relation holds
     (while, for certain abstract syntax entities,
     we need to return additional information, e.g. the extended renaming.")
   (xdoc::p
    "Then we prove theorems relating variable renamings
     to the various dynamic semantic operations.
     Examples of these operations are writing variables,
     finding functions in environments, and so on.")
   (xdoc::p
    "Next, we show some properties of computation states and variable renamings,
     which do not involve dynamic semantic operations.")
   (xdoc::p
    "Then we prove theorems saying
     that executing a list of statements yields a computation state
     with a superset of the starting variables,
     and that executing loop iterations yields a computation state
     with the same variables as the starting state.
     These theorems are independent from variable renaming,
     and could be moved to a more central place,
     possibly complemented by similar properties
     for executing other kinds of abstract syntax entities.")
   (xdoc::p
    "Then we prove some theorems about limit errors.
     In particular, we prove that
     several dynamic semantic operations never return limit errors.
     These theorems are actually independent from variable renaming,
     and could be moved to a more central place.")
   (xdoc::p
    "Before proving the main theorems,
     we prove two preliminary ones having to do with
     the use of @(tsee restrict-vars) in execution,
     when dealing with parallel executions related by variable renaming.")
   (xdoc::p
    "Finally we prove theorems
     about the execution functions and variable renaming.
     We do that by induction, using a custom induction schema."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo-renamevarp ((old funinfop) (new funinfop))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "An old and new function information are related by variable renaming when
     their inputs and outputs form a renaming
     under which the bodies are related by the renaming relation."))
  (b* ((ren (add-vars-to-var-renaming (funinfo->inputs old)
                                      (funinfo->inputs new)
                                      (renaming nil)))
       ((when (resulterrp ren)) nil)
       (ren (add-vars-to-var-renaming (funinfo->outputs old)
                                      (funinfo->outputs new)
                                      ren))
       ((when (resulterrp ren)) nil))
    (not (resulterrp (block-renamevar (funinfo->body old)
                                      (funinfo->body new)
                                      ren))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-renamevarp ((old funscopep) (new funscopep))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over function scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two scopes must have the same function names,
     and the function information for the same function name must be related."))
  (b* ((old (funscope-fix old))
       (new (funscope-fix new)))
    (and (or (and (omap::empty old)
                  (omap::empty new))
             (and (not (omap::empty old))
                  (not (omap::empty new))
                  (b* (((mv old-fun old-info) (omap::head old))
                       ((mv new-fun new-info) (omap::head new)))
                    (and (equal old-fun new-fun)
                         (funinfo-renamevarp old-info new-info)
                         (funscope-renamevarp (omap::tail old)
                                              (omap::tail new))))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funenv-renamevarp ((old funenvp) (new funenvp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over function environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two environments must have the same number of scopes,
     and the corresponding scopes must be related."))
  (or (and (endp old)
           (endp new))
      (and (consp old)
           (consp new)
           (funscope-renamevarp (car old) (car new))
           (funenv-renamevarp (cdr old) (cdr new))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk lstate-match-renamevarp ((old lstatep) (new lstatep) (ren renamingp))
  :returns (yes/no booleanp)
  :short "Value matching part of the
          variable renaming relation over local states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The full relation is defined in @(tsee lstate-renamevarp),
     as consisting of three conditions.
     This quantified function expresses one of these conditions.
     The condition is that every pair of variables in the renaming
     have the same value (if any) in the old and new local states.
     Note that this allows the local states to have no values
     for some variable pairs in the renaming,
     so long as they both do not have it;
     or they both have it, and it is the same value in that case."))
  (forall (old-var new-var)
          (implies (member-equal (cons old-var new-var)
                                 (renaming->list ren))
                   (equal (cdr (omap::in old-var (lstate-fix old)))
                          (cdr (omap::in new-var (lstate-fix new))))))
  ///

  (fty::deffixequiv-sk lstate-match-renamevarp
    :args ((old lstatep) (new lstatep) (ren renamingp)))

  (defruled lstate-match-renamevarp-rewrite
    (implies (and (lstate-match-renamevarp old new ren)
                  (lstatep old)
                  (lstatep new)
                  (member-equal (cons old-var new-var)
                                (renaming->list ren)))
             (equal (cdr (omap::in old-var old))
                    (cdr (omap::in new-var new))))
    :use lstate-match-renamevarp-necc
    :disable (lstate-match-renamevarp lstate-match-renamevarp-necc))

  (defruled lstate-match-renamevarp-of-nil
    (lstate-match-renamevarp nil nil (renaming nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lstate-renamevarp ((old lstatep) (new lstatep) (ren renamingp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over local states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renaming must cover all the variables in the old and new local states,
     i.e. every variable in the states must be in the renaming.
     Furthermore, the two states must agree on the renaming:
     see @(tsee lstate-match-renamevarp)."))
  (and (set::subset (omap::keys (lstate-fix old)) (renaming-old ren))
       (set::subset (omap::keys (lstate-fix new)) (renaming-new ren))
       (lstate-match-renamevarp old new ren))
  :hooks (:fix)
  ///

  (defruled same-defined-when-lstate-renamevarp
    (implies (and (lstatep old-lstate)
                  (lstatep new-lstate)
                  (identifierp old-var)
                  (identifierp new-var)
                  (lstate-renamevarp old-lstate new-lstate ren)
                  (member-equal (cons old-var new-var)
                                (renaming->list ren)))
             (iff (set::in old-var (omap::keys old-lstate))
                  (set::in new-var (omap::keys new-lstate))))
    :enable omap::set-in-keys-to-in
    :use ((:instance lstate-match-renamevarp-rewrite
           (old old-lstate)
           (new new-lstate))
          (:instance valuep-of-cdr-of-in-lstatep
           (x old-lstate)
           (k old-var))
          (:instance valuep-of-cdr-of-in-lstatep
           (x new-lstate)
           (k new-var)))
    :disable valuep-of-cdr-of-in-lstatep)

  (defruled lstate-renamevarp-of-nil
    (lstate-renamevarp nil nil (renaming nil))
    :use lstate-match-renamevarp-of-nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cstate-renamevarp ((old cstatep) (new cstatep) (ren renamingp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The underlying local states must be related."))
  (lstate-renamevarp (cstate->local old)
                     (cstate->local new)
                     ren)
  :hooks (:fix)
  ///

  (defruled cstate-renamevarp-of-nil
    (cstate-renamevarp (change-cstate old-cstate :local nil)
                       (change-cstate new-cstate :local nil)
                       (renaming nil))
    :use lstate-renamevarp-of-nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eoutcome-renamevarp ((old eoutcomep) (new eoutcomep) (ren renamingp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over expression outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The underlying computation states must be related,
     and the two value lists must be the same.
     The latter condition is because values are not subject to renamings."))
  (and (cstate-renamevarp (eoutcome->cstate old)
                          (eoutcome->cstate new)
                          ren)
       (equal (eoutcome->values old)
              (eoutcome->values new)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define soutcome-renamevarp ((old soutcomep) (new soutcomep) (ren renamingp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over statement outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The underlying computation states must be related,
     and the two modes must be the same.
     The latter condition is because modes are not subject to renamings."))
  (and (cstate-renamevarp (soutcome->cstate old)
                          (soutcome->cstate new)
                          ren)
       (equal (soutcome->mode old)
              (soutcome->mode new)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eoutcome-result-renamevarp ((old eoutcome-resultp)
                                    (new eoutcome-resultp)
                                    (ren renamingp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over expression outcome results."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either they are both (possibly different) errors,
     or they are related expression outcomes."))
  (b* ((old (eoutcome-result-fix old))
       (new (eoutcome-result-fix new)))
    (or (and (resulterrp old)
             (resulterrp new))
        (and (not (resulterrp old))
             (not (resulterrp new))
             (eoutcome-renamevarp old new ren))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define soutcome-result-renamevarp ((old soutcome-resultp)
                                    (new soutcome-resultp)
                                    (ren renamingp))
  :returns (yes/no booleanp)
  :short "Variable renaming relation over statement outcome results."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either they are both (possibly different) errors,
     or they are related statement outcomes."))
  (b* ((old (soutcome-result-fix old))
       (new (soutcome-result-fix new)))
    (or (and (resulterrp old)
             (resulterrp new))
        (and (not (resulterrp old))
             (not (resulterrp new))
             (soutcome-renamevarp old new ren))))
  :hooks (:fix)
  ///

  (defruled soutcome-result-renamevarp-to-soutcome-renamevarp
    (implies (and (soutcome-resultp x)
                  (soutcome-resultp y)
                  (not (resulterrp x))
                  (not (resulterrp y)))
             (equal (soutcome-result-renamevarp x y ren)
                    (soutcome-renamevarp x y ren))))

  (defruled soutcome-result-renamevarp-of-errors-not-error
    (implies (and (resulterrp x)
                  (resulterrp y))
             (soutcome-result-renamevarp x y ren))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection function-environments-when-renaming-variables
  :short "Theorems about function environments and variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two function definitions are related by variable renaming,
     their corresponding function information is as well.")
   (xdoc::p
    "If two lists of function definitions are related,
     so are the corresponding scopes.
     This is proved via an intermediate theorem saying that
     adding related function information to related function scopes
     yields related function scopes.")
   (xdoc::p
    "Adding related function definitions to related function environments
     yields related function environments.
     This concerns @(tsee add-funs).")
   (xdoc::p
    "Retrieving the same function from related function scopes
     yields related function information.")
   (xdoc::p
    "Related function scopes have the same keys.
     This is stated in two slightly different theorems.")
   (xdoc::p
    "If two function environments are related, so are their @(tsee cdr)s.")
   (xdoc::P
    "Finding a function from related function environments
     yields related information and remaining environments.")
   (xdoc::p
    "If two lists of function definitions are related,
     their corresponding scopes are either both errors or none.")
   (xdoc::p
    "Two related function scopes and two related function environments
     have the same disjointness status.")
   (xdoc::p
    "Adding related function definitions to related function environments
     yields either two errors or no errors."))

  (defruled funinfo-renamevarp-of-funinfo-for-fundef
    (implies (not (resulterrp (fundef-renamevar old new)))
             (funinfo-renamevarp (funinfo-for-fundef old)
                                 (funinfo-for-fundef new)))
    :enable (funinfo-for-fundef
             fundef-renamevar
             funinfo-renamevarp))

  (defruled funscope-renamevarp-of-update
    (implies (and (funscopep old-scope)
                  (funscopep new-scope)
                  (funinfop old-info)
                  (funinfop new-info)
                  (identifierp fun)
                  (funscope-renamevarp old-scope new-scope)
                  (funinfo-renamevarp old-info new-info))
             (funscope-renamevarp (omap::update fun old-info old-scope)
                                  (omap::update fun new-info new-scope)))
    :induct (omap::omap-induction2 old-scope new-scope)
    :enable (funscope-renamevarp)
    :hints ('(:cases ((equal fun (mv-nth 0 (omap::head old-scope)))
                      (<< fun (mv-nth 0 (omap::head old-scope)))))))

  (defruled funscope-renamevarp-of-funscope-for-fundefs
    (implies (not (resulterrp (fundef-list-renamevar old-funs new-funs)))
             (b* ((old-scope1 (funscope-for-fundefs old-funs))
                  (new-scope1 (funscope-for-fundefs new-funs)))
               (implies (and (not (resulterrp old-scope1))
                             (not (resulterrp new-scope1)))
                        (funscope-renamevarp old-scope1 new-scope1))))
    :enable (funscope-for-fundefs
             fundef-list-renamevar
             funscope-renamevarp-of-update
             funinfo-renamevarp-of-funinfo-for-fundef
             funscopep-when-funscope-resultp-and-not-resulterrp)
    :expand (fundef-renamevar (car old-funs) (car new-funs)))

  (defruled funenv-renamevarp-of-add-funs
    (implies (and (funenv-renamevarp old-env new-env)
                  (not (resulterrp (fundef-list-renamevar old-funs new-funs))))
             (b* ((old-env1 (add-funs old-funs old-env))
                  (new-env1 (add-funs new-funs new-env)))
               (implies (and (not (resulterrp old-env1))
                             (not (resulterrp new-env1)))
                        (funenv-renamevarp old-env1 new-env1))))
    :enable (funenv-renamevarp
             add-funs
             funscope-renamevarp-of-funscope-for-fundefs))

  (defruled funinfo-renamevarp-when-funscope-renamevarp
    (implies (and (funscopep old-scope)
                  (funscopep new-scope)
                  (funscope-renamevarp old-scope new-scope))
             (b* ((old-fun+info (omap::in fun old-scope))
                  (new-fun+info (omap::in fun new-scope)))
               (implies (and (consp old-fun+info)
                             (consp new-fun+info))
                        (funinfo-renamevarp (cdr old-fun+info)
                                            (cdr new-fun+info)))))
    :enable funscope-renamevarp)

  (defruled same-in-when-funscope-renamevarp
    (implies (and (funscopep old-scope)
                  (funscopep new-scope)
                  (funscope-renamevarp old-scope new-scope))
             (equal (consp (omap::in fun old-scope))
                    (consp (omap::in fun new-scope))))
    :enable funscope-renamevarp)

  (defruled same-funscope-keys-when-renamevar
    (implies (and (funscopep old)
                  (funscopep new)
                  (funscope-renamevarp old new))
             (equal (omap::keys old)
                    (omap::keys new)))
    :enable funscope-renamevarp)

  (defruled funenv-renamevarp-of-cdr
    (implies (funenv-renamevarp old-env new-env)
             (funenv-renamevarp (cdr old-env) (cdr new-env)))
    :enable funenv-renamevarp)

  (defruled funinfo+funenv-renamevarp-of-find-fun
    (implies (funenv-renamevarp old-env new-env)
             (b* ((old-info+env (find-fun fun old-env))
                  (new-info+env (find-fun fun new-env))
                  (old-info (funinfo+funenv->info old-info+env))
                  (new-info (funinfo+funenv->info new-info+env))
                  (old-env1 (funinfo+funenv->env old-info+env))
                  (new-env1 (funinfo+funenv->env new-info+env)))
               (implies (and (not (resulterrp old-info+env))
                             (not (resulterrp new-info+env)))
                        (and (funinfo-renamevarp old-info new-info)
                             (funenv-renamevarp old-env1 new-env1)))))
    :use (:instance lemma
          (old-env (funenv-fix old-env))
          (new-env (funenv-fix new-env)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (funenvp old-env)
                     (funenvp new-env)
                     (funenv-renamevarp old-env new-env))
                (b* ((old-info+env (find-fun fun old-env))
                     (new-info+env (find-fun fun new-env))
                     (old-info (funinfo+funenv->info old-info+env))
                     (new-info (funinfo+funenv->info new-info+env))
                     (old-env1 (funinfo+funenv->env old-info+env))
                     (new-env1 (funinfo+funenv->env new-info+env)))
                  (implies (and (not (resulterrp old-info+env))
                                (not (resulterrp new-info+env)))
                           (and (funinfo-renamevarp old-info new-info)
                                (funenv-renamevarp old-env1 new-env1)))))
       :enable (find-fun
                funinfo-renamevarp-when-funscope-renamevarp
                funenv-renamevarp-of-cdr
                funenv-renamevarp
                same-in-when-funscope-renamevarp))))

  (defruled same-funscope-for-fundefs-error-when-renamevar
    (implies (not (resulterrp (fundef-list-renamevar old-funs new-funs)))
             (b* ((old-scope1 (funscope-for-fundefs old-funs))
                  (new-scope1 (funscope-for-fundefs new-funs)))
               (equal (resulterrp old-scope1)
                      (resulterrp new-scope1))))
    :enable (funscope-for-fundefs
             fundef-list-renamevar
             funscopep-when-funscope-resultp-and-not-resulterrp
             funscope-renamevarp-of-funscope-for-fundefs
             not-resulterrp-when-funscopep)
    :expand (fundef-renamevar (car old-funs) (car new-funs))
    :hints ('(:use (:instance same-in-when-funscope-renamevarp
                    (old-scope (funscope-for-fundefs (cdr old-funs)))
                    (new-scope (funscope-for-fundefs (cdr new-funs)))
                    (fun (fundef->name (car new-funs)))))))

  (defruled same-ensure-funscope-disjoint-when-renamevar
    (implies (and (funscope-renamevarp old-funscope new-funscope)
                  (funenv-renamevarp old-funenv new-funenv))
             (equal (ensure-funscope-disjoint old-funscope old-funenv)
                    (ensure-funscope-disjoint new-funscope new-funenv)))
    :use (:instance lemma
          (old-funscope (funscope-fix old-funscope))
          (new-funscope (funscope-fix new-funscope))
          (old-funenv (funenv-fix old-funenv))
          (new-funenv (funenv-fix new-funenv)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (funscopep old-funscope)
                     (funscopep new-funscope)
                     (funenvp old-funenv)
                     (funenvp new-funenv)
                     (funscope-renamevarp old-funscope new-funscope)
                     (funenv-renamevarp old-funenv new-funenv))
                (equal (ensure-funscope-disjoint old-funscope old-funenv)
                       (ensure-funscope-disjoint new-funscope new-funenv)))
       :enable (ensure-funscope-disjoint
                funenv-renamevarp
                same-funscope-keys-when-renamevar))))

  (defruled same-add-funs-error-when-renamevar
    (implies (and (funenv-renamevarp old-funenv new-funenv)
                  (not (resulterrp (fundef-list-renamevar old-funs new-funs))))
             (b* ((old-funenv1 (add-funs old-funs old-funenv))
                  (new-funenv1 (add-funs new-funs new-funenv)))
               (equal (resulterrp old-funenv1)
                      (resulterrp new-funenv1))))
    :enable (add-funs
             same-funscope-for-fundefs-error-when-renamevar
             funscope-renamevarp-of-funscope-for-fundefs
             not-resulterrp-when-funenvp
             funscopep-when-funscope-resultp-and-not-resulterrp)
    :use (:instance same-ensure-funscope-disjoint-when-renamevar
          (old-funscope (funscope-for-fundefs old-funs))
          (new-funscope (funscope-for-fundefs new-funs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-var/vars-value/values-when-renamevar
  :short "Theorems about reading variables and variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reading corresponding variables from related computation states
     yields the same value, if both readings suceed."))

  (defruled read-var-value-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (not (resulterrp (var-renamevar old-var new-var ren))))
             (b* ((old-val (read-var-value old-var old-cstate))
                  (new-val (read-var-value new-var new-cstate)))
               (implies (and (not (resulterrp old-val))
                             (not (resulterrp new-val)))
                        (equal old-val new-val))))
    :enable (read-var-value
             cstate-renamevarp
             var-renamevar
             lstate-renamevarp
             lstate-match-renamevarp-rewrite))

  (defruled read-vars-values-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (not (resulterrp (var-list-renamevar old-vars new-vars ren))))
             (b* ((old-vals (read-vars-values old-vars old-cstate))
                  (new-vals (read-vars-values new-vars new-cstate)))
               (implies (and (not (resulterrp old-vals))
                             (not (resulterrp new-vals)))
                        (equal old-vals new-vals))))
    :enable (read-vars-values
             var-list-renamevar
             read-var-value-when-renamevar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection write-var/vars-value/values-when-renamevar
  :short "Theorems about writing variables and variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "Writing the same values
     in corresponding variables of related computation states
     yields related computation states."))

  (defruled write-var-value-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (not (resulterrp (var-renamevar old-var new-var ren)))
                  (identifierp old-var)
                  (identifierp new-var))
             (b* ((old-cstate1 (write-var-value old-var val old-cstate))
                  (new-cstate1 (write-var-value new-var val new-cstate)))
               (implies (and (not (resulterrp old-cstate1))
                             (not (resulterrp new-cstate1)))
                        (cstate-renamevarp old-cstate1 new-cstate1 ren))))
    :enable (write-var-value
             cstate-renamevarp
             lstate-renamevarp
             lemma
             var-renamevar
             old-var-in-renaming-old-when-in-renaming
             new-var-in-renaming-new-when-in-renaming)

    :prep-lemmas
    ((defruled lemma
       (implies (and (lstatep old-lstate)
                     (lstatep new-lstate)
                     (lstate-renamevarp old-lstate new-lstate ren)
                     (identifierp old-var)
                     (identifierp new-var)
                     (not (resulterrp (var-renamevar old-var new-var ren)))
                     (valuep val))
                (b* ((old-lstate1
                      (omap::update old-var val old-lstate))
                     (new-lstate1
                      (omap::update new-var val new-lstate)))
                  (lstate-match-renamevarp old-lstate1 new-lstate1 ren)))
       :enable lstate-match-renamevarp
       :use (:instance lemma-lemma
             (old-var1 (mv-nth 0 (lstate-match-renamevarp-witness
                                  (omap::update old-var val old-lstate)
                                  (omap::update new-var val new-lstate)
                                  ren)))
             (new-var1 (mv-nth 1 (lstate-match-renamevarp-witness
                                  (omap::update old-var val old-lstate)
                                  (omap::update new-var val new-lstate)
                                  ren))))

       :prep-lemmas
       ((defruled lemma-lemma
          (implies (and (lstatep old-lstate)
                        (lstatep new-lstate)
                        (lstate-renamevarp old-lstate new-lstate ren)
                        (identifierp old-var)
                        (identifierp new-var)
                        (not (resulterrp (var-renamevar old-var new-var ren))))
                   (b* ((old-lstate1 (omap::update old-var val old-lstate))
                        (new-lstate1 (omap::update new-var val new-lstate)))
                     (implies (member-equal (cons old-var1 new-var1)
                                            (renaming->list ren))
                              (equal (cdr (omap::in old-var1 old-lstate1))
                                     (cdr (omap::in new-var1 new-lstate1))))))
          :enable (lstate-renamevarp
                   lstate-match-renamevarp-rewrite
                   var-renamevar)
          :use (:instance renaming-pair-equality
                (pair1 (cons old-var new-var))
                (pair2 (cons old-var1 new-var1))))))))

  (defruled write-vars-values-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (not (resulterrp (var-list-renamevar old-vars new-vars ren)))
                  (identifier-listp old-vars)
                  (identifier-listp new-vars))
             (b* ((old-cstate1 (write-vars-values old-vars vals old-cstate))
                  (new-cstate1 (write-vars-values new-vars vals new-cstate)))
               (implies (and (not (resulterrp old-cstate1))
                             (not (resulterrp new-cstate1)))
                        (cstate-renamevarp old-cstate1 new-cstate1 ren))))
    :enable (write-vars-values
             var-list-renamevar
             write-var-value-when-renamevar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection add-var/vars-value/values-when-renamevar
  :short "Theorems about adding variables and variable renamings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Adding corresponding variables with the same value
     to related computation states yields related computation states."))

  (defruled add-var-value-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (identifierp old-var)
                  (identifierp new-var))
             (b* ((ren1 (add-var-to-var-renaming old-var new-var ren))
                  (old-cstate1 (add-var-value old-var val old-cstate))
                  (new-cstate1 (add-var-value new-var val new-cstate)))
               (implies (and (not (resulterrp ren1))
                             (not (resulterrp old-cstate1))
                             (not (resulterrp new-cstate1)))
                        (cstate-renamevarp old-cstate1 new-cstate1 ren1))))
    :enable (add-var-value
             cstate-renamevarp
             lstate-renamevarp
             lemma
             renaming-old/new-of-add-var-to-var-renaming)

    :prep-lemmas
    ((defruled lemma
       (implies (and (lstatep old-lstate)
                     (lstatep new-lstate)
                     (lstate-renamevarp old-lstate new-lstate ren)
                     (identifierp old-var)
                     (identifierp new-var)
                     (valuep val))
                (b* ((ren1 (add-var-to-var-renaming old-var new-var ren))
                     (old-lstate1 (omap::update old-var val old-lstate))
                     (new-lstate1 (omap::update new-var val new-lstate)))
                  (implies (not (resulterrp ren1))
                           (lstate-match-renamevarp old-lstate1
                                                    new-lstate1
                                                    ren1))))
       :enable lstate-match-renamevarp
       :use (:instance lemma-lemma
             (old-var1
              (mv-nth 0 (lstate-match-renamevarp-witness
                         (omap::update old-var val old-lstate)
                         (omap::update new-var val new-lstate)
                         (add-var-to-var-renaming old-var new-var ren))))
             (new-var1
              (mv-nth 1 (lstate-match-renamevarp-witness
                         (omap::update old-var val old-lstate)
                         (omap::update new-var val new-lstate)
                         (add-var-to-var-renaming old-var new-var ren)))))

       :prep-lemmas
       ((defruled lemma-lemma
          (implies (and (lstatep old-lstate)
                        (lstatep new-lstate)
                        (lstate-renamevarp old-lstate new-lstate ren)
                        (identifierp old-var)
                        (identifierp new-var))
                   (b* ((ren1 (add-var-to-var-renaming old-var new-var ren))
                        (old-lstate1 (omap::update old-var val old-lstate))
                        (new-lstate1 (omap::update new-var val new-lstate)))
                     (implies (and (not (resulterrp ren1))
                                   (member-equal (cons old-var1 new-var1)
                                                 (renaming->list ren1)))
                              (equal (cdr (omap::in old-var1 old-lstate1))
                                     (cdr (omap::in new-var1 new-lstate1))))))
          :enable (lstate-renamevarp
                   lstate-match-renamevarp-rewrite
                   add-var-to-var-renaming
                   lemma-lemma-lemma)

          :prep-lemmas
          ((defruled lemma-lemma-lemma
             (implies (and (identifier-identifier-alistp list)
                           (member-equal (cons a b) list))
                      (and (member-equal a (strip-cars list))
                           (member-equal b (strip-cdrs list)))))))))))

  (defruled add-vars-values-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (identifier-listp old-vars)
                  (identifier-listp new-vars))
             (b* ((ren1 (add-vars-to-var-renaming old-vars new-vars ren))
                  (old-cstate1 (add-vars-values old-vars vals old-cstate))
                  (new-cstate1 (add-vars-values new-vars vals new-cstate)))
               (implies (and (not (resulterrp ren1))
                             (not (resulterrp old-cstate1))
                             (not (resulterrp new-cstate1)))
                        (cstate-renamevarp old-cstate1 new-cstate1 ren1))))
    :enable (add-vars-values
             add-vars-to-var-renaming
             add-var-value-when-renamevar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection restrict-vars-when-renamevar
  :short "Theorems about restricting variables and variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee restrict-vars) is used, in the Yul dynamic semantics,
     to model the execution of blocks and the execution of loops.
     These theorems about @(tsee restrict-vars) apply to these two cases,
     as explained below.")
   (xdoc::p
    "In the execution of a block,
     there are three computation states of interest:
     (i) the state before the block;
     (ii) the state after executing the statements of the block; and
     (iii) the state after the block,
     obtained from the second one by restricting it
     to the variables present in the first one.
     Consider the execution of two blocks related by variable renaming:
     then there are corresponding first, second, and third states.
     If the first states are related,
     and the second states are related,
     and the keys of each second state is a superset of
     the keys of the first state,
     then the third states are related too.
     The theorem @('cstate-renamevarp-of-restrict-vars-1') below says this.
     It does not mention block execution,
     but only the three states (for old and new execution),
     because all we need for this property to hold
     are the hypotheses in the theorem.
     This theorem is used later to prove properties
     of the execution of blocks.
     This theorem is proved via a preliminary one for local states.")
   (xdoc::p
    "In the execution of a loop,
     there are four computation states of interest:
     (i) the state before the loop;
     (ii) the state after executing the initialization block;
     (ii) the state after execution the loop iterations; and
     (iv) the state after the loop.
     The theorem @('cstate-renamevarp-of-restrict-vars-2') below
     is similar to the ones explained above (for blocks),
     but it involves additional states.
     It is also proved via a preliminary one for local states."))

  (defrule lstate-renamevarp-of-restrict-1
    (implies (and (lstatep old-lstate)
                  (lstatep new-lstate)
                  (lstate-renamevarp old-lstate new-lstate ren)
                  (lstatep old-lstate1)
                  (lstatep new-lstate1)
                  (lstate-renamevarp old-lstate1 new-lstate1 ren1)
                  (set::subset (omap::keys old-lstate)
                               (omap::keys old-lstate1))
                  (set::subset (omap::keys new-lstate)
                               (omap::keys new-lstate1))
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (b* ((old-lstate2 (omap::restrict (omap::keys old-lstate)
                                               old-lstate1))
                  (new-lstate2 (omap::restrict (omap::keys new-lstate)
                                               new-lstate1)))
               (lstate-renamevarp old-lstate2 new-lstate2 ren)))
    :enable (lstate-renamevarp
             set::subset-transitive)
    :use lemma

    :prep-lemmas
    ((defruled lemma
       (implies (and (lstatep old-lstate)
                     (lstatep new-lstate)
                     (lstate-renamevarp old-lstate new-lstate ren)
                     (lstatep old-lstate1)
                     (lstatep new-lstate1)
                     (lstate-renamevarp old-lstate1 new-lstate1 ren1)
                     (set::subset (omap::keys old-lstate)
                                  (omap::keys old-lstate1))
                     (set::subset (omap::keys new-lstate)
                                  (omap::keys new-lstate1))
                     (subsetp-equal (renaming->list ren)
                                    (renaming->list ren1)))
                (b* ((old-lstate2 (omap::restrict (omap::keys old-lstate)
                                                  old-lstate1))
                     (new-lstate2 (omap::restrict (omap::keys new-lstate)
                                                  new-lstate1)))
                  (lstate-match-renamevarp old-lstate2 new-lstate2 ren)))
       :enable (lstate-match-renamevarp)
       :use (:instance lemma-lemma
             (old-var
              (mv-nth 0 (lstate-match-renamevarp-witness
                         (omap::restrict (omap::keys old-lstate) old-lstate1)
                         (omap::restrict (omap::keys new-lstate) new-lstate1)
                         ren)))
             (new-var
              (mv-nth 1 (lstate-match-renamevarp-witness
                         (omap::restrict (omap::keys old-lstate) old-lstate1)
                         (omap::restrict (omap::keys new-lstate) new-lstate1)
                         ren))))

       :prep-lemmas
       ((defruled lemma-lemma
          (implies (and (lstatep old-lstate)
                        (lstatep new-lstate)
                        (lstate-renamevarp old-lstate new-lstate ren)
                        (lstatep old-lstate1)
                        (lstatep new-lstate1)
                        (lstate-renamevarp old-lstate1 new-lstate1 ren1)
                        (set::subset (omap::keys old-lstate)
                                     (omap::keys old-lstate1))
                        (set::subset (omap::keys new-lstate)
                                     (omap::keys new-lstate1))
                        (subsetp-equal (renaming->list ren)
                                       (renaming->list ren1)))
                   (b* ((old-lstate2 (omap::restrict (omap::keys old-lstate)
                                                     old-lstate1))
                        (new-lstate2 (omap::restrict (omap::keys new-lstate)
                                                     new-lstate1)))
                     (implies (member-equal (cons old-var new-var)
                                            (renaming->list ren))
                              (equal (cdr (omap::in old-var old-lstate2))
                                     (cdr (omap::in new-var new-lstate2))))))
          :enable (lstate-renamevarp
                   lstate-match-renamevarp-rewrite
                   omap::in-of-restrict-2
                   old-var-in-renaming-old-when-in-renaming)
          :disable acl2::subsetp-member
          :use ((:instance acl2::subsetp-member
                 (a (cons old-var new-var))
                 (x (renaming->list ren))
                 (y (renaming->list ren1)))
                same-defined-when-lstate-renamevarp)
          :cases ((member-equal (cons old-var new-var)
                                (renaming->list ren1))))))))

  (defruled cstate-renamevarp-of-restrict-vars-1
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (cstate-renamevarp old-cstate1 new-cstate1 ren1)
                  (set::subset (omap::keys (cstate->local old-cstate))
                               (omap::keys (cstate->local old-cstate1)))
                  (set::subset (omap::keys (cstate->local new-cstate))
                               (omap::keys (cstate->local new-cstate1)))
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (b* ((old-cstate2
                   (restrict-vars (omap::keys (cstate->local old-cstate))
                                  old-cstate1))
                  (new-cstate2
                   (restrict-vars (omap::keys (cstate->local new-cstate))
                                  new-cstate1)))
               (cstate-renamevarp old-cstate2 new-cstate2 ren)))
    :enable (cstate-renamevarp
             restrict-vars
             lstate-renamevarp-of-restrict-1))

  (defrule lstate-renamevarp-of-restrict-2
    (implies (and (lstatep old-lstate)
                  (lstatep new-lstate)
                  (lstate-renamevarp old-lstate new-lstate ren)
                  (lstatep old-lstate1)
                  (lstatep new-lstate1)
                  (lstate-renamevarp old-lstate1 new-lstate1 ren1)
                  (lstatep old-lstate2)
                  (lstatep new-lstate2)
                  (lstate-renamevarp old-lstate2 new-lstate2 ren1)
                  (set::subset (omap::keys old-lstate)
                               (omap::keys old-lstate1))
                  (set::subset (omap::keys new-lstate)
                               (omap::keys new-lstate1))
                  (equal (omap::keys old-lstate2)
                         (omap::keys old-lstate1))
                  (equal (omap::keys new-lstate2)
                         (omap::keys new-lstate1))
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (b* ((old-lstate3 (omap::restrict (omap::keys old-lstate)
                                               old-lstate2))
                  (new-lstate3 (omap::restrict (omap::keys new-lstate)
                                               new-lstate2)))
               (lstate-renamevarp old-lstate3 new-lstate3 ren)))
    :enable (lstate-renamevarp
             set::subset-transitive)
    :use lemma

    :prep-lemmas
    ((defruled lemma
       (implies (and (lstatep old-lstate)
                     (lstatep new-lstate)
                     (lstate-renamevarp old-lstate new-lstate ren)
                     (lstatep old-lstate1)
                     (lstatep new-lstate1)
                     (lstate-renamevarp old-lstate1 new-lstate1 ren1)
                     (lstatep old-lstate2)
                     (lstatep new-lstate2)
                     (lstate-renamevarp old-lstate2 new-lstate2 ren1)
                     (set::subset (omap::keys old-lstate)
                                  (omap::keys old-lstate1))
                     (set::subset (omap::keys new-lstate)
                                  (omap::keys new-lstate1))
                     (equal (omap::keys old-lstate2)
                            (omap::keys old-lstate1))
                     (equal (omap::keys new-lstate2)
                            (omap::keys new-lstate1))
                     (subsetp-equal (renaming->list ren)
                                    (renaming->list ren1)))
                (b* ((old-lstate3 (omap::restrict (omap::keys old-lstate)
                                                  old-lstate2))
                     (new-lstate3 (omap::restrict (omap::keys new-lstate)
                                                  new-lstate2)))
                  (lstate-match-renamevarp old-lstate3 new-lstate3 ren)))
       :enable (lstate-match-renamevarp)
       :use (:instance lemma-lemma
             (old-var
              (mv-nth 0 (lstate-match-renamevarp-witness
                         (omap::restrict (omap::keys old-lstate) old-lstate2)
                         (omap::restrict (omap::keys new-lstate) new-lstate2)
                         ren)))
             (new-var
              (mv-nth 1 (lstate-match-renamevarp-witness
                         (omap::restrict (omap::keys old-lstate) old-lstate2)
                         (omap::restrict (omap::keys new-lstate) new-lstate2)
                         ren))))

       :prep-lemmas
       ((defruled lemma-lemma
          (implies (and (lstatep old-lstate)
                        (lstatep new-lstate)
                        (lstate-renamevarp old-lstate new-lstate ren)
                        (lstatep old-lstate1)
                        (lstatep new-lstate1)
                        (lstate-renamevarp old-lstate1 new-lstate1 ren1)
                        (lstatep old-lstate2)
                        (lstatep new-lstate2)
                        (lstate-renamevarp old-lstate2 new-lstate2 ren1)
                        (set::subset (omap::keys old-lstate)
                                     (omap::keys old-lstate1))
                        (set::subset (omap::keys new-lstate)
                                     (omap::keys new-lstate1))
                        (equal (omap::keys old-lstate2)
                               (omap::keys old-lstate1))
                        (equal (omap::keys new-lstate2)
                               (omap::keys new-lstate1))
                        (subsetp-equal (renaming->list ren)
                                       (renaming->list ren1)))
                   (b* ((old-lstate3 (omap::restrict (omap::keys old-lstate)
                                                     old-lstate2))
                        (new-lstate3 (omap::restrict (omap::keys new-lstate)
                                                     new-lstate2)))
                     (implies (member-equal (cons old-var new-var)
                                            (renaming->list ren))
                              (equal (cdr (omap::in old-var old-lstate3))
                                     (cdr (omap::in new-var new-lstate3))))))
          :enable (lstate-renamevarp
                   lstate-match-renamevarp-rewrite
                   omap::in-of-restrict-2
                   old-var-in-renaming-old-when-in-renaming)
          :disable acl2::subsetp-member
          :use ((:instance acl2::subsetp-member
                 (a (cons old-var new-var))
                 (x (renaming->list ren))
                 (y (renaming->list ren1)))
                same-defined-when-lstate-renamevarp)
          :cases ((member-equal (cons old-var new-var)
                                (renaming->list ren1))))))))

  (defruled cstate-renamevarp-of-restrict-vars-2
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (cstate-renamevarp old-cstate1 new-cstate1 ren1)
                  (cstate-renamevarp old-cstate2 new-cstate2 ren1)
                  (set::subset (omap::keys (cstate->local old-cstate))
                               (omap::keys (cstate->local old-cstate1)))
                  (set::subset (omap::keys (cstate->local new-cstate))
                               (omap::keys (cstate->local new-cstate1)))
                  (equal (omap::keys (cstate->local old-cstate2))
                         (omap::keys (cstate->local old-cstate1)))
                  (equal (omap::keys (cstate->local new-cstate2))
                         (omap::keys (cstate->local new-cstate1)))
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (b* ((old-cstate3
                   (restrict-vars (omap::keys (cstate->local old-cstate))
                                  old-cstate2))
                  (new-cstate3
                   (restrict-vars (omap::keys (cstate->local new-cstate))
                                  new-cstate2)))
               (cstate-renamevarp old-cstate3 new-cstate3 ren)))
    :enable (cstate-renamevarp
             restrict-vars
             lstate-renamevarp-of-restrict-2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection init-local-when-renamevar
  :short "Theorems about local state initialization and variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting with no variables,
     if old and new local states are initialized with corresponding variables,
     and with identical values for each pair of corresponding input variables,
     the resulting computation states are related by variable renaming.
     This theorem serves to establish the relation between computation states
     at the beginning of function execution."))

  (defruled init-local-when-renamevar
    (b* ((ren0 (add-vars-to-var-renaming old-in-vars
                                         new-in-vars
                                         (renaming nil)))
         (ren (add-vars-to-var-renaming old-out-vars
                                        new-out-vars
                                        ren0))
         (old-cstate1 (init-local old-in-vars vals old-out-vars old-cstate))
         (new-cstate1 (init-local new-in-vars vals new-out-vars new-cstate)))
      (implies (and (not (resulterrp ren0))
                    (not (resulterrp ren))
                    (not (resulterrp old-cstate1))
                    (not (resulterrp new-cstate1))
                    (identifier-listp old-in-vars)
                    (identifier-listp new-in-vars)
                    (identifier-listp old-out-vars)
                    (identifier-listp new-out-vars))
               (cstate-renamevarp old-cstate1 new-cstate1 ren)))
    :enable (init-local
             same-len-when-add-vars-to-var-renaming)
    :disable ((:e cstate-renamevarp))
    :use (cstate-renamevarp-of-nil
          (:instance add-vars-values-when-renamevar
           (old-cstate (change-cstate old-cstate :local nil))
           (new-cstate (change-cstate new-cstate :local nil))
           (old-vars old-in-vars)
           (new-vars new-in-vars)
           (ren (renaming nil)))
          (:instance add-vars-values-when-renamevar
           (old-cstate (add-vars-values old-in-vars
                                        vals
                                        (change-cstate old-cstate :local nil)))
           (new-cstate (add-vars-values new-in-vars
                                        vals
                                        (change-cstate new-cstate :local nil)))
           (old-vars old-out-vars)
           (new-vars new-out-vars)
           (ren (add-vars-to-var-renaming old-in-vars
                                          new-in-vars
                                          (renaming nil)))
           (vals (repeat (len old-out-vars) (value 0)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection path/paths-renamevar-theorems
  :short "Theorems about variable renaming for paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two paths or lists of paths are related by variable renaming,
     extracting their underlying variables causes no errors.
     This is what the first two theorems below say.")
   (xdoc::p
    "If two paths or lists of paths are related by variable renaming,
     so are the underlying variables.
     This is what the last two theorems below say."))

  (defruled path-to-var-not-error-when-path-renamevar
    (implies (not (resulterrp (path-renamevar old new ren)))
             (and (not (resulterrp (path-to-var old)))
                  (not (resulterrp (path-to-var new)))))
    :enable (path-renamevar
             path-to-var
             not-resulterrp-when-identifierp))

  (defruled paths-to-vars-not-error-when-path-list-renamevar
    (implies (not (resulterrp (path-list-renamevar old new ren)))
             (and (not (resulterrp (paths-to-vars old)))
                  (not (resulterrp (paths-to-vars new)))))
    :enable (path-list-renamevar
             paths-to-vars
             identifierp-when-identifier-resultp-and-not-resulterrp
             identifier-listp-when-identifier-list-resultp-and-not-resulterrp
             not-resulterrp-when-identifier-listp
             path-to-var-not-error-when-path-renamevar))

  (defruled var-renamevar-not-error-when-path-renamevar
    (implies (not (resulterrp (path-renamevar old new ren)))
             (not (resulterrp (var-renamevar (path-to-var old)
                                             (path-to-var new)
                                             ren))))
    :enable (path-renamevar
             path-to-var))

  (defruled var-list-renamevar-not-error-when-path-list-renamevar
    (implies (not (resulterrp (path-list-renamevar old new ren)))
             (not (resulterrp (var-list-renamevar (paths-to-vars old)
                                                  (paths-to-vars new)
                                                  ren))))
    :enable (path-list-renamevar
             paths-to-vars
             var-list-renamevar
             var-renamevar-not-error-when-path-renamevar
             paths-to-vars-not-error-when-path-list-renamevar
             path-to-var-not-error-when-path-renamevar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection cstate-renamevarp-with-larger-renaming
  :short "Theorems about computation states and variable renamings,
          not involving dynamic semantic operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two computation states are related by variable renaming,
     they are also related by a larger variable renaming.
     This is proved by first proving a similar theorem for local states.")
   (xdoc::p
    "The motivation for this theorem is that,
     when a list of statements (in a block) is executed,
     execution may not reach the end of the statemnts.
     However, statically, when we consider that list of statements,
     we extend the variable renaming
     according to the whole list of statements.
     Since we want to show that execution preserves
     the variable renaming relation between computation states,
     we need to able to relate the final states
     with the final variable renamings,
     which may be larger due to execution ending before the end.
     So this theorem enables us to bridge this gap."))

  (defruled lstate-match-renamevarp-of-larger
    (implies (and (lstatep old-lstate)
                  (lstatep new-lstate)
                  (lstate-renamevarp old-lstate new-lstate ren)
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (lstate-match-renamevarp old-lstate new-lstate ren1))
    :enable lstate-match-renamevarp
    :use (:instance lemma-lemma
          (old-var (mv-nth 0 (lstate-match-renamevarp-witness
                              old-lstate new-lstate ren1)))
          (new-var (mv-nth 1 (lstate-match-renamevarp-witness
                              old-lstate new-lstate ren1))))

    :prep-lemmas

    ((defruled lemma-lemma
       (implies (and (lstatep old-lstate)
                     (lstatep new-lstate)
                     (lstate-renamevarp old-lstate new-lstate ren)
                     (subsetp-equal (renaming->list ren)
                                    (renaming->list ren1)))
                (implies (member-equal (cons old-var new-var)
                                       (renaming->list ren1))
                         (equal (cdr (omap::in old-var old-lstate))
                                (cdr (omap::in new-var new-lstate)))))
       :enable (lstate-renamevarp
                lstate-match-renamevarp-rewrite
                old-var-in-renaming-old-when-in-renaming
                omap::set-in-keys-to-in
                set::subset-in)
       :use ((:instance lemma1
              (a old-var)
              (b new-var))
             (:instance lemma2
              (a old-var)
              (b new-var)))
       :cases ((member-equal (cons old-var new-var) (renaming->list ren))
               (set::in old-var (omap::keys old-lstate))
               (set::in new-var (omap::keys new-lstate)))

       :prep-lemmas

       ((defruled lemma1
          (implies (and (subsetp-equal (renaming->list ren)
                                       (renaming->list ren1))
                        (member-equal (cons a b) (renaming->list ren1))
                        (not (member-equal (cons a b) (renaming->list ren))))
                   (not (set::in a (renaming-old ren))))
          :enable (acl2::member-strip-cars-find-cdr-membership
                   renaming-old)
          :use (:instance renaming-pair-equality
                (ren ren1)
                (pair1 (cons a b))
                (pair2 (cons a (acl2::member-strip-cars-find-cdr
                                a (renaming->list ren))))))

        (defruled lemma2
          (implies (and (subsetp-equal (renaming->list ren)
                                       (renaming->list ren1))
                        (member-equal (cons a b) (renaming->list ren1))
                        (not (member-equal (cons a b) (renaming->list ren))))
                   (not (set::in b (renaming-new ren))))
          :enable (acl2::member-strip-cdrs-find-car-membership
                   renaming-new)
          :use (:instance renaming-pair-equality
                (ren ren1)
                (pair1 (cons a b))
                (pair2 (cons (acl2::member-strip-cdrs-find-car
                              b (renaming->list ren)) b))))))))

  (defruled lstate-renamevarp-of-larger
    (implies (and (lstatep old-lstate)
                  (lstatep new-lstate)
                  (lstate-renamevarp old-lstate new-lstate ren)
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (lstate-renamevarp old-lstate new-lstate ren1))
    :enable (lstate-renamevarp
             set::subset-transitive)
    :use lstate-match-renamevarp-of-larger
    :prep-lemmas
    ((defrule lemma
       (implies (subsetp-equal (renaming->list ren)
                               (renaming->list ren1))
                (and (set::subset (renaming-old ren)
                                  (renaming-old ren1))
                     (set::subset (renaming-new ren)
                                  (renaming-new ren1))))
       :enable (renaming-old
                renaming-new
                acl2::subsetp-equal-of-strip-cars
                acl2::subsetp-equal-of-strip-cdrs
                set::subset-of-mergesort-and-mergesort))))

  (defruled cstate-renamevarp-of-larger
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (subsetp-equal (renaming->list ren)
                                 (renaming->list ren1)))
             (cstate-renamevarp old-cstate new-cstate ren1))
    :enable (cstate-renamevarp
             lstate-renamevarp-of-larger)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection vars-of-cstate-after-exec
  :short "Theorems about the variables in a computation state
          after execution of certain kinds of constructs."

  (local (include-book "../language/static-soundness"))

  (defruled keys-of-cstate->local-of-exec-statement-list
    (b* ((outcome (exec-statement-list stmts cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (set::subset (omap::keys (cstate->local cstate))
                            (omap::keys (cstate->local
                                         (soutcome->cstate outcome))))))
    :use cstate-to-vars-of-exec-statement-list
    :enable cstate-to-vars)

  (defruled keys-of-cstate->local-of-exec-for-iterations
    (b* ((outcome (exec-for-iterations test update body cstate funenv limit)))
      (implies (not (resulterrp outcome))
               (equal (omap::keys (cstate->local cstate))
                      (omap::keys (cstate->local (soutcome->cstate outcome))))))
    :use cstate-to-vars-of-exec-for-iterations
    :enable cstate-to-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection resulterr-limitp-theorems
  :short "Theorems about @(tsee resulterr-limitp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are mainly about certain dynamic semantic operations
     never returning  limit errors.
     There is also one theorem to simplify @(tsee resulterr-limitp)
     when applied to @(tsee resulterr).
     There is also a theorem to show that an error is not a limit error,
     based on looking at the keyword (assuming it is constant)."))

  (defruled resulterr-limitp-of-resulterr-of-info
    (implies (and (resulterrp error)
                  (error-info-wfp error))
             (equal (resulterr-limitp
                     (resulterr (cons more (fty::resulterr->info error))))
                    (resulterr-limitp error)))
    :enable (resulterr-limitp
             resulterr-limitp-aux
             error-info-wfp))

  (defruled not-resulterr-limitp-of-const
    (implies (and (syntaxp (quotep kwd))
                  (not (equal kwd :limit)))
             (not (resulterr-limitp
                   (resulterr (list (list fn (cons kwd more)))))))
    :enable (resulterr-limitp
             resulterr-limitp-aux))

  (defruled not-resulterr-limitp-of-eval-literal
    (not (resulterr-limitp (eval-literal lit)))
    :enable (resulterr-limitp
             resulterr-limitp-aux
             eval-literal
             eval-plain-string-literal
             eval-hex-string-literal))

  (defruled not-resulterr-limitp-of-soutcome
    (not (resulterr-limitp (soutcome cstate mode)))
    :enable resulterr-limitp)

  (defruled not-resulterr-limitp-of-path-to-var
    (implies (resulterrp (path-to-var path))
             (not (resulterr-limitp (path-to-var path))))
    :enable (resulterr-limitp
             resulterr-limitp-aux
             path-to-var
             not-resulterrp-when-identifierp))

  (defruled not-resulterr-limitp-of-paths-to-vars
    (implies (resulterrp (paths-to-vars paths))
             (not (resulterr-limitp (paths-to-vars paths))))
    :enable (paths-to-vars
             not-resulterr-limitp-of-path-to-var
             resulterr-limitp-of-resulterr-of-info
             identifierp-when-identifier-resultp-and-not-resulterrp
             identifier-listp-when-identifier-list-resultp-and-not-resulterrp
             not-resulterrp-when-identifier-listp))

  (defruled not-resulterr-limitp-of-read-var-value
    (b* ((result (read-var-value var cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (read-var-value
             not-resulterr-limitp-of-const
             resulterr-limitp-of-resulterr-of-info
             not-resulterrp-when-valuep))

  (defruled not-resulterr-limitp-of-read-vars-values
    (b* ((result (read-vars-values vars cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (read-vars-values
             not-resulterr-limitp-of-read-var-value
             resulterr-limitp-of-resulterr-of-info
             valuep-when-value-resultp-and-not-resulterrp
             value-listp-when-value-list-resultp-and-not-resulterrp
             not-resulterrp-when-value-listp))

  (defruled not-resulterr-limitp-of-write-var-value
    (b* ((result (write-var-value var val cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (resulterr-limitp
             resulterr-limitp-aux
             write-var-value))

  (defruled not-resulterr-limitp-of-write-vars-values
    (b* ((result (write-vars-values vars vals cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (write-vars-values
             not-resulterr-limitp-of-write-var-value
             resulterr-limitp-of-resulterr-of-info
             not-resulterr-limitp-of-const))

  (defruled not-resulterr-limitp-of-add-var-value
    (b* ((result (add-var-value var val cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (resulterr-limitp
             resulterr-limitp-aux
             add-var-value))

  (defruled not-resulterr-limitp-of-add-vars-values
    (b* ((result (add-vars-values vars vals cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (add-vars-values
             not-resulterr-limitp-of-add-var-value
             resulterr-limitp-of-resulterr-of-info
             not-resulterr-limitp-of-const))

  (defruled not-resulterr-limitp-of-find-fun
    (b* ((result (find-fun fun env)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (find-fun
             resulterr-limitp
             resulterr-limitp-aux))

  (defruled not-resulterr-limitp-of-init-local
    (b* ((result (init-local in-vars in-vals out-vars cstate)))
      (implies (resulterrp result)
               (not (resulterr-limitp result))))
    :enable (init-local
             resulterr-limitp-of-resulterr-of-info
             not-resulterr-limitp-of-add-var-value
             not-resulterr-limitp-of-add-vars-values)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-when-renamevar-restrict-vars-lemmas
  :short "Theorems about restricting variables
          in parallel executions related by variable renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see restrict-vars-when-renamevar) for background and motivation.
     The following two lemmas are make use of the theorems there
     to show that, during the execution of certain constructs,
     the variable renaming relation between computation states is preserved.
     These lemmas are directly used in the main theorems."))

  (defruled exec-when-renamevar-restrict-vars-lemma-1
    (implies
     (and (not (resulterrp
                (statement-list-renamevar old-stmts new-stmts ren)))
          (not (resulterrp
                (exec-statement-list old-stmts
                                     old-cstate
                                     (add-funs (statements-to-fundefs old-stmts)
                                               old-funenv)
                                     (+ -1 limit))))
          (not (resulterrp
                (exec-statement-list new-stmts
                                     new-cstate
                                     (add-funs (statements-to-fundefs new-stmts)
                                               new-funenv)
                                     (+ -1 limit))))
          (cstate-renamevarp old-cstate new-cstate ren)
          (cstate-renamevarp
           (soutcome->cstate
            (exec-statement-list old-stmts
                                 old-cstate
                                 (add-funs (statements-to-fundefs old-stmts)
                                           old-funenv)
                                 (+ -1 limit)))
           (soutcome->cstate
            (exec-statement-list new-stmts
                                 new-cstate
                                 (add-funs (statements-to-fundefs new-stmts)
                                           new-funenv)
                                 (+ -1 limit)))
           (statement-list-renamevar old-stmts new-stmts ren)))
     (cstate-renamevarp
      (restrict-vars
       (omap::keys (cstate->local old-cstate))
       (soutcome->cstate
        (exec-statement-list old-stmts
                             old-cstate
                             (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv)
                             (+ -1 limit))))
      (restrict-vars
       (omap::keys (cstate->local new-cstate))
       (soutcome->cstate
        (exec-statement-list new-stmts
                             new-cstate
                             (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)
                             (+ -1 limit))))
      ren))
    :enable (keys-of-cstate->local-of-exec-statement-list
             subsetp-equal-of-statement-list-renamevar
             cstate-renamevarp-of-restrict-vars-1))

  (defruled exec-when-renamevar-restrict-vars-lemma-2
    (implies
     (and
      (not (resulterrp (statement-list-renamevar old-stmts new-stmts ren)))
      (not
       (resulterrp
        (exec-statement-list old-stmts
                             old-cstate
                             (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv)
                             (+ -1 limit))))
      (not
       (resulterrp
        (exec-statement-list new-stmts
                             new-cstate
                             (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)
                             (+ -1 limit))))
      (cstate-renamevarp old-cstate new-cstate ren)
      (cstate-renamevarp
       (soutcome->cstate
        (exec-statement-list old-stmts
                             old-cstate
                             (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv)
                             (+ -1 limit)))
       (soutcome->cstate
        (exec-statement-list new-stmts
                             new-cstate
                             (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)
                             (+ -1 limit)))
       (statement-list-renamevar old-stmts new-stmts ren))
      (not
       (resulterrp
        (exec-for-iterations old-test
                             old-update
                             old-body
                             (soutcome->cstate
                              (exec-statement-list
                               old-stmts
                               old-cstate
                               (add-funs (statements-to-fundefs old-stmts)
                                         old-funenv)
                               (+ -1 limit)))
                             (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv)
                             (+ -1 limit))))
      (not
       (resulterrp
        (exec-for-iterations new-test
                             new-update
                             new-body
                             (soutcome->cstate
                              (exec-statement-list
                               new-stmts
                               new-cstate
                               (add-funs (statements-to-fundefs new-stmts)
                                         new-funenv)
                               (+ -1 limit)))
                             (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)
                             (+ -1 limit))))
      (cstate-renamevarp
       (soutcome->cstate
        (exec-for-iterations old-test
                             old-update
                             old-body
                             (soutcome->cstate
                              (exec-statement-list
                               old-stmts
                               old-cstate
                               (add-funs (statements-to-fundefs old-stmts)
                                         old-funenv)
                               (+ -1 limit)))
                             (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv)
                             (+ -1 limit)))
       (soutcome->cstate
        (exec-for-iterations new-test
                             new-update
                             new-body
                             (soutcome->cstate
                              (exec-statement-list
                               new-stmts
                               new-cstate
                               (add-funs (statements-to-fundefs new-stmts)
                                         new-funenv)
                               (+ -1 limit)))
                             (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)
                             (+ -1 limit)))
       (statement-list-renamevar
        old-stmts
        new-stmts
        ren)))
     (cstate-renamevarp
      (restrict-vars
       (omap::keys (cstate->local old-cstate))
       (soutcome->cstate
        (exec-for-iterations old-test
                             old-update
                             old-body
                             (soutcome->cstate
                              (exec-statement-list
                               old-stmts
                               old-cstate
                               (add-funs (statements-to-fundefs old-stmts)
                                         old-funenv)
                               (+ -1 limit)))
                             (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv)
                             (+ -1 limit))))
      (restrict-vars
       (omap::keys (cstate->local new-cstate))
       (soutcome->cstate
        (exec-for-iterations new-test
                             new-update
                             new-body
                             (soutcome->cstate
                              (exec-statement-list
                               new-stmts
                               new-cstate
                               (add-funs (statements-to-fundefs new-stmts)
                                         new-funenv)
                               (+ -1 limit)))
                             (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)
                             (+ -1 limit))))
      ren))
    :enable (keys-of-cstate->local-of-exec-for-iterations
             subsetp-equal-of-statement-list-renamevar
             set::subset-transitive)
    :use ((:instance cstate-renamevarp-of-restrict-vars-2
           (old-cstate1
            (soutcome->cstate
             (exec-statement-list old-stmts
                                  old-cstate
                                  (add-funs (statements-to-fundefs old-stmts)
                                            old-funenv)
                                  (+ -1 limit))))
           (new-cstate1
            (soutcome->cstate
             (exec-statement-list new-stmts
                                  new-cstate
                                  (add-funs (statements-to-fundefs new-stmts)
                                            new-funenv)
                                  (+ -1 limit))))
           (old-cstate2
            (soutcome->cstate
             (exec-for-iterations old-test
                                  old-update
                                  old-body
                                  (soutcome->cstate
                                   (exec-statement-list
                                    old-stmts
                                    old-cstate
                                    (add-funs (statements-to-fundefs old-stmts)
                                              old-funenv)
                                    (+ -1 limit)))
                                  (add-funs (statements-to-fundefs old-stmts)
                                            old-funenv)
                                  (+ -1 limit))))
           (new-cstate2
            (soutcome->cstate
             (exec-for-iterations new-test
                                  new-update
                                  new-body
                                  (soutcome->cstate
                                   (exec-statement-list
                                    new-stmts
                                    new-cstate
                                    (add-funs (statements-to-fundefs new-stmts)
                                              new-funenv)
                                    (+ -1 limit)))
                                  (add-funs (statements-to-fundefs new-stmts)
                                            new-funenv)
                                  (+ -1 limit))))
           (ren1 (statement-list-renamevar old-stmts new-stmts ren)))
          (:instance keys-of-cstate->local-of-exec-statement-list
           (stmts old-stmts)
           (cstate old-cstate)
           (funenv (add-funs (statements-to-fundefs old-stmts)
                             old-funenv))
           (limit (1- limit)))
          (:instance keys-of-cstate->local-of-exec-statement-list
           (stmts new-stmts)
           (cstate new-cstate)
           (funenv (add-funs (statements-to-fundefs new-stmts)
                             new-funenv))
           (limit (1- limit))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-when-renamevar
  :short "Main theorems of the proof that
          variable renaming preserves the execution behavior."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a custom induction schema,
     which takes into account the recursive structure
     of all the functions involved in the proof.
     We introduce it locally.")
   (xdoc::p
    "Then we prove the theorems by mutual induction,
     using the flag macro from the custom induction schema.
     These theorems are also necessarily local,
     because the induction schema is local.
     Thus, we then restate the theorems non-locally.")
   (xdoc::p
    "We use computed hints to use separate hints
     for different cases of the induction.
     This makes the proof and its dependencies more clear."))

  (local

   (defines induction

     (define expression-induct ((old-expr expressionp)
                                (new-expr expressionp)
                                (old-cstate cstatep)
                                (new-cstate cstatep)
                                (old-funenv funenvp)
                                (new-funenv funenvp)
                                (ren renamingp)
                                (limit natp))
       (b* (((when (zp limit)) nil))
         (expression-case
          old-expr
          :path nil
          :literal nil
          :funcall (b* (((unless (expression-case new-expr :funcall)) nil)
                        (new-expr.get (expression-funcall->get new-expr)))
                     (funcall-induct old-expr.get
                                     new-expr.get
                                     old-cstate
                                     new-cstate
                                     old-funenv
                                     new-funenv
                                     ren
                                     (1- limit)))))
       :measure (nfix limit))

     (define expression-list-induct ((old-exprs expression-listp)
                                     (new-exprs expression-listp)
                                     (old-cstate cstatep)
                                     (new-cstate cstatep)
                                     (old-funenv funenvp)
                                     (new-funenv funenvp)
                                     (ren renamingp)
                                     (limit natp))
       (b* (((when (zp limit)) nil)
            ((when (endp old-exprs)) nil)
            ((when (endp new-exprs)) nil)
            (old-outcome (exec-expression (car old-exprs)
                                          old-cstate
                                          old-funenv
                                          (1- limit)))
            (new-outcome (exec-expression (car new-exprs)
                                          new-cstate
                                          new-funenv
                                          (1- limit)))
            ((when (or (resulterrp old-outcome)
                       (resulterrp new-outcome)))
             (expression-induct (car old-exprs)
                                (car new-exprs)
                                old-cstate
                                new-cstate
                                old-funenv
                                new-funenv
                                ren
                                (1- limit)))
            ((eoutcome old-outcome) old-outcome)
            ((eoutcome new-outcome) new-outcome))
         (list (expression-induct (car old-exprs)
                                  (car new-exprs)
                                  old-cstate
                                  new-cstate
                                  old-funenv
                                  new-funenv
                                  ren
                                  (1- limit))
               (expression-list-induct (cdr old-exprs)
                                       (cdr new-exprs)
                                       old-outcome.cstate
                                       new-outcome.cstate
                                       old-funenv
                                       new-funenv
                                       ren
                                       (1- limit))))
       :measure (nfix limit))

     (define funcall-induct ((old-funcall funcallp)
                             (new-funcall funcallp)
                             (old-cstate cstatep)
                             (new-cstate cstatep)
                             (old-funenv funenvp)
                             (new-funenv funenvp)
                             (ren renamingp)
                             (limit natp))
       (b* (((when (zp limit)) nil)
            ((unless (equal (funcall->name old-funcall)
                            (funcall->name new-funcall)))
             nil)
            (fun (funcall->name old-funcall))
            (old-outcome (exec-expression-list (rev (funcall->args old-funcall))
                                               old-cstate
                                               old-funenv
                                               (1- limit)))
            (new-outcome (exec-expression-list (rev (funcall->args new-funcall))
                                               new-cstate
                                               new-funenv
                                               (1- limit)))
            ((when (or (resulterrp old-outcome)
                       (resulterrp new-outcome)))
             (expression-list-induct (rev (funcall->args old-funcall))
                                     (rev (funcall->args new-funcall))
                                     old-cstate
                                     new-cstate
                                     old-funenv
                                     new-funenv
                                     ren
                                     (1- limit)))
            ((eoutcome old-outcome) old-outcome)
            ((eoutcome new-outcome) new-outcome)
            ((unless (equal old-outcome.values
                            new-outcome.values))
             (expression-list-induct (rev (funcall->args old-funcall))
                                     (rev (funcall->args new-funcall))
                                     old-cstate
                                     new-cstate
                                     old-funenv
                                     new-funenv
                                     ren
                                     (1- limit)))
            (args old-outcome.values))
         (list (expression-list-induct (rev (funcall->args old-funcall))
                                       (rev (funcall->args new-funcall))
                                       old-cstate
                                       new-cstate
                                       old-funenv
                                       new-funenv
                                       ren
                                       (1- limit))
               (function-induct fun
                                args
                                old-outcome.cstate
                                new-outcome.cstate
                                old-funenv
                                new-funenv
                                ren
                                (1- limit))))
       :measure (nfix limit))

     (define function-induct ((fun identifierp)
                              (args value-listp)
                              (old-cstate cstatep)
                              (new-cstate cstatep)
                              (old-funenv funenvp)
                              (new-funenv funenvp)
                              (ren renamingp)
                              (limit natp))
       (declare (ignore ren))
       (b* (((when (zp limit)) nil)
            ((ok (funinfo+funenv old-info+env)) (find-fun fun old-funenv))
            ((ok (funinfo+funenv new-info+env)) (find-fun fun new-funenv))
            ((funinfo old-funinfo) old-info+env.info)
            ((funinfo new-funinfo) new-info+env.info)
            ((ok old-cstate) (init-local old-funinfo.inputs
                                         args
                                         old-funinfo.outputs
                                         old-cstate))
            ((ok new-cstate) (init-local new-funinfo.inputs
                                         args
                                         new-funinfo.outputs
                                         new-cstate))
            ((ok ren1) (add-vars-to-var-renaming old-funinfo.inputs
                                                 new-funinfo.inputs
                                                 (renaming nil)))
            ((ok ren1) (add-vars-to-var-renaming old-funinfo.outputs
                                                 new-funinfo.outputs
                                                 ren1)))
         (block-induct old-funinfo.body
                       new-funinfo.body
                       old-cstate
                       new-cstate
                       old-info+env.env
                       new-info+env.env
                       ren1
                       (1- limit)))
       :measure (nfix limit))

     (define statement-induct ((old-stmt statementp)
                               (new-stmt statementp)
                               (old-cstate cstatep)
                               (new-cstate cstatep)
                               (old-funenv funenvp)
                               (new-funenv funenvp)
                               (ren renamingp)
                               (limit natp))
       (b* (((when (zp limit)) nil))
         (statement-case
          old-stmt
          :block (b* (((unless (statement-case new-stmt :block)) nil)
                      (new-stmt.get (statement-block->get new-stmt)))
                   (block-induct old-stmt.get
                                 new-stmt.get
                                 old-cstate
                                 new-cstate
                                 old-funenv
                                 new-funenv
                                 ren
                                 (1- limit)))
          :variable-single (b* (((unless
                                     (statement-case new-stmt :variable-single))
                                 nil)
                                (new-stmt.init
                                 (statement-variable-single->init new-stmt))
                                ((unless (and old-stmt.init
                                              new-stmt.init))
                                 nil))
                             (expression-induct old-stmt.init
                                                new-stmt.init
                                                old-cstate
                                                new-cstate
                                                old-funenv
                                                new-funenv
                                                ren
                                                (1- limit)))
          :variable-multi (b* (((unless (statement-case new-stmt :variable-multi))
                                nil)
                               (new-stmt.init
                                (statement-variable-multi->init new-stmt))
                               ((unless (and old-stmt.init
                                             new-stmt.init))
                                nil))
                            (funcall-induct old-stmt.init
                                            new-stmt.init
                                            old-cstate
                                            new-cstate
                                            old-funenv
                                            new-funenv
                                            ren
                                            (1- limit)))
          :assign-single (b* (((unless (statement-case new-stmt :assign-single))
                               nil)
                              (new-stmt.value
                               (statement-assign-single->value new-stmt))
                              ((unless (and old-stmt.value
                                            new-stmt.value))
                               nil))
                           (expression-induct old-stmt.value
                                              new-stmt.value
                                              old-cstate
                                              new-cstate
                                              old-funenv
                                              new-funenv
                                              ren
                                              (1- limit)))
          :assign-multi (b* (((unless (statement-case new-stmt :assign-multi))
                              nil)
                             (new-stmt.value
                              (statement-assign-multi->value new-stmt))
                             ((unless (and old-stmt.value
                                           new-stmt.value))
                              nil))
                          (funcall-induct old-stmt.value
                                          new-stmt.value
                                          old-cstate
                                          new-cstate
                                          old-funenv
                                          new-funenv
                                          ren
                                          (1- limit)))
          :funcall (b* (((unless (statement-case new-stmt :funcall)) nil)
                        (new-stmt.get (statement-funcall->get new-stmt)))
                     (funcall-induct old-stmt.get
                                     new-stmt.get
                                     old-cstate
                                     new-cstate
                                     old-funenv
                                     new-funenv
                                     ren
                                     (1- limit)))
          :if (b* (((unless (statement-case new-stmt :if)) nil)
                   (new-stmt.test (statement-if->test new-stmt))
                   (new-stmt.body (statement-if->body new-stmt))
                   (old-outcome (exec-expression old-stmt.test
                                                 old-cstate
                                                 old-funenv
                                                 (1- limit)))
                   (new-outcome (exec-expression new-stmt.test
                                                 new-cstate
                                                 new-funenv
                                                 (1- limit)))
                   ((when (or (resulterrp old-outcome)
                              (resulterrp new-outcome)))
                    (expression-induct old-stmt.test
                                       new-stmt.test
                                       old-cstate
                                       new-cstate
                                       old-funenv
                                       new-funenv
                                       ren
                                       (1- limit)))
                   ((eoutcome old-outcome) old-outcome)
                   ((eoutcome new-outcome) new-outcome))
                (list (expression-induct old-stmt.test
                                         new-stmt.test
                                         old-cstate
                                         new-cstate
                                         old-funenv
                                         new-funenv
                                         ren
                                         (1- limit))
                      (block-induct old-stmt.body
                                    new-stmt.body
                                    old-outcome.cstate
                                    new-outcome.cstate
                                    old-funenv
                                    new-funenv
                                    ren
                                    (1- limit))))
          :for (b* (((unless (statement-case new-stmt :for)) nil)
                    (new-stmt.init (statement-for->init new-stmt))
                    (new-stmt.test (statement-for->test new-stmt))
                    (new-stmt.update (statement-for->update new-stmt))
                    (new-stmt.body (statement-for->body new-stmt))
                    (old-stmts (block->statements old-stmt.init))
                    (new-stmts (block->statements new-stmt.init))
                    ((ok old-funenv1) (add-funs (statements-to-fundefs old-stmts)
                                                old-funenv))
                    ((ok new-funenv1) (add-funs (statements-to-fundefs new-stmts)
                                                new-funenv))
                    ((ok ren1) (statement-list-renamevar old-stmts new-stmts ren))
                    (old-outcome (exec-statement-list old-stmts
                                                      old-cstate
                                                      old-funenv1
                                                      (1- limit)))
                    (new-outcome (exec-statement-list new-stmts
                                                      new-cstate
                                                      new-funenv1
                                                      (1- limit)))
                    ((when (or (resulterrp old-outcome)
                               (resulterrp new-outcome)))
                     (statement-list-induct old-stmts
                                            new-stmts
                                            old-cstate
                                            new-cstate
                                            old-funenv1
                                            new-funenv1
                                            ren
                                            (1- limit)))
                    ((soutcome old-outcome) old-outcome)
                    ((soutcome new-outcome) new-outcome))
                 (list (statement-list-induct old-stmts
                                              new-stmts
                                              old-cstate
                                              new-cstate
                                              old-funenv1
                                              new-funenv1
                                              ren
                                              (1- limit))
                       (for-iterations-induct old-stmt.test
                                              new-stmt.test
                                              old-stmt.update
                                              new-stmt.update
                                              old-stmt.body
                                              new-stmt.body
                                              old-outcome.cstate
                                              new-outcome.cstate
                                              old-funenv1
                                              new-funenv1
                                              ren1
                                              (1- limit))))
          :switch (b* (((unless (statement-case new-stmt :switch)) nil)
                       (new-stmt.target (statement-switch->target new-stmt))
                       (new-stmt.cases (statement-switch->cases new-stmt))
                       (new-stmt.default (statement-switch->default new-stmt))
                       (old-outcome (exec-expression old-stmt.target
                                                     old-cstate
                                                     old-funenv
                                                     (1- limit)))
                       (new-outcome (exec-expression new-stmt.target
                                                     new-cstate
                                                     new-funenv
                                                     (1- limit)))
                       ((when (or (resulterrp old-outcome)
                                  (resulterrp new-outcome)))
                        (expression-induct old-stmt.target
                                           new-stmt.target
                                           old-cstate
                                           new-cstate
                                           old-funenv
                                           new-funenv
                                           ren
                                           (1- limit)))
                       ((eoutcome old-outcome) old-outcome)
                       ((eoutcome new-outcome) new-outcome)
                       ((unless (and (equal old-outcome.values
                                            new-outcome.values)
                                     (consp old-outcome.values)
                                     (consp new-outcome.values)))
                        (expression-induct old-stmt.target
                                           new-stmt.target
                                           old-cstate
                                           new-cstate
                                           old-funenv
                                           new-funenv
                                           ren
                                           (1- limit))))
                    (list (expression-induct old-stmt.target
                                             new-stmt.target
                                             old-cstate
                                             new-cstate
                                             old-funenv
                                             new-funenv
                                             ren
                                             (1- limit))
                          (switch-rest-induct old-stmt.cases
                                              new-stmt.cases
                                              old-stmt.default
                                              new-stmt.default
                                              (car old-outcome.values)
                                              old-outcome.cstate
                                              new-outcome.cstate
                                              old-funenv
                                              new-funenv
                                              ren
                                              (1- limit))))
          :leave nil
          :break nil
          :continue nil
          :fundef nil))
       :measure (nfix limit))

     (define statement-list-induct ((old-stmts statement-listp)
                                    (new-stmts statement-listp)
                                    (old-cstate cstatep)
                                    (new-cstate cstatep)
                                    (old-funenv funenvp)
                                    (new-funenv funenvp)
                                    (ren renamingp)
                                    (limit natp))
       (b* (((when (zp limit)) nil)
            ((when (endp old-stmts)) nil)
            ((when (endp new-stmts)) nil)
            ((ok ren1) (statement-renamevar (car old-stmts) (car new-stmts) ren))
            (old-outcome (exec-statement (car old-stmts)
                                         old-cstate
                                         old-funenv
                                         (1- limit)))
            (new-outcome (exec-statement (car new-stmts)
                                         new-cstate
                                         new-funenv
                                         (1- limit)))
            ((when (or (resulterrp old-outcome)
                       (resulterrp new-outcome)))
             (statement-induct (car old-stmts)
                               (car new-stmts)
                               old-cstate
                               new-cstate
                               old-funenv
                               new-funenv
                               ren
                               (1- limit)))
            ((soutcome old-outcome) old-outcome)
            ((soutcome new-outcome) new-outcome)
            ((when (or (not (mode-case old-outcome.mode :regular))
                       (not (mode-case new-outcome.mode :regular))))
             (statement-induct (car old-stmts)
                               (car new-stmts)
                               old-cstate
                               new-cstate
                               old-funenv
                               new-funenv
                               ren
                               (1- limit))))
         (list (statement-induct (car old-stmts)
                                 (car new-stmts)
                                 old-cstate
                                 new-cstate
                                 old-funenv
                                 new-funenv
                                 ren
                                 (1- limit))
               (statement-list-induct (cdr old-stmts)
                                      (cdr new-stmts)
                                      old-outcome.cstate
                                      new-outcome.cstate
                                      old-funenv
                                      new-funenv
                                      ren1
                                      (1- limit))))
       :measure (nfix limit))

     (define block-induct ((old-block blockp)
                           (new-block blockp)
                           (old-cstate cstatep)
                           (new-cstate cstatep)
                           (old-funenv funenvp)
                           (new-funenv funenvp)
                           (ren renamingp)
                           (limit natp))
       (b* (((when (zp limit)) nil)
            (old-stmts (block->statements old-block))
            (new-stmts (block->statements new-block))
            ((ok old-funenv) (add-funs (statements-to-fundefs old-stmts)
                                       old-funenv))
            ((ok new-funenv) (add-funs (statements-to-fundefs new-stmts)
                                       new-funenv)))
         (statement-list-induct old-stmts
                                new-stmts
                                old-cstate
                                new-cstate
                                old-funenv
                                new-funenv
                                ren
                                (1- limit)))
       :measure (nfix limit))

     (define for-iterations-induct ((old-test expressionp)
                                    (new-test expressionp)
                                    (old-update blockp)
                                    (new-update blockp)
                                    (old-body blockp)
                                    (new-body blockp)
                                    (old-cstate cstatep)
                                    (new-cstate cstatep)
                                    (old-funenv funenvp)
                                    (new-funenv funenvp)
                                    (ren renamingp)
                                    (limit natp))
       (b* (((when (zp limit)) nil)
            (old-outcome (exec-expression old-test
                                          old-cstate
                                          old-funenv
                                          (1- limit)))
            (new-outcome (exec-expression new-test
                                          new-cstate
                                          new-funenv
                                          (1- limit)))
            ((when (or (resulterrp old-outcome)
                       (resulterrp new-outcome)))
             (expression-induct old-test
                                new-test
                                old-cstate
                                new-cstate
                                old-funenv
                                new-funenv
                                ren
                                (1- limit)))
            ((eoutcome old-outcome) old-outcome)
            ((eoutcome new-outcome) new-outcome)
            (old-outcome1 (exec-block old-body
                                      old-outcome.cstate
                                      old-funenv
                                      (1- limit)))
            (new-outcome1 (exec-block new-body
                                      new-outcome.cstate
                                      new-funenv
                                      (1- limit)))
            ((when (or (resulterrp old-outcome1)
                       (resulterrp new-outcome1)))
             (list (expression-induct old-test
                                      new-test
                                      old-cstate
                                      new-cstate
                                      old-funenv
                                      new-funenv
                                      ren
                                      (1- limit))
                   (block-induct old-body
                                 new-body
                                 old-outcome.cstate
                                 new-outcome.cstate
                                 old-funenv
                                 new-funenv
                                 ren
                                 (1- limit))))
            ((soutcome old-outcome1) old-outcome1)
            ((soutcome new-outcome1) new-outcome1)
            (old-outcome2 (exec-block old-update
                                      old-outcome1.cstate
                                      old-funenv
                                      (1- limit)))
            (new-outcome2 (exec-block new-update
                                      new-outcome1.cstate
                                      new-funenv
                                      (1- limit)))
            ((when (or (resulterrp old-outcome2)
                       (resulterrp new-outcome2)))
             (list (expression-induct old-test
                                      new-test
                                      old-cstate
                                      new-cstate
                                      old-funenv
                                      new-funenv
                                      ren
                                      (1- limit))
                   (block-induct old-body
                                 new-body
                                 old-outcome.cstate
                                 new-outcome.cstate
                                 old-funenv
                                 new-funenv
                                 ren
                                 (1- limit))
                   (block-induct old-update
                                 new-update
                                 old-outcome1.cstate
                                 new-outcome1.cstate
                                 old-funenv
                                 new-funenv
                                 ren
                                 (1- limit))))
            ((soutcome old-outcome2) old-outcome2)
            ((soutcome new-outcome2) new-outcome2))
         (list (expression-induct old-test
                                  new-test
                                  old-cstate
                                  new-cstate
                                  old-funenv
                                  new-funenv
                                  ren
                                  (1- limit))
               (block-induct old-body
                             new-body
                             old-outcome.cstate
                             new-outcome.cstate
                             old-funenv
                             new-funenv
                             ren
                             (1- limit))
               (block-induct old-update
                             new-update
                             old-outcome1.cstate
                             new-outcome1.cstate
                             old-funenv
                             new-funenv
                             ren
                             (1- limit))
               (for-iterations-induct old-test
                                      new-test
                                      old-update
                                      new-update
                                      old-body
                                      new-body
                                      old-outcome2.cstate
                                      new-outcome2.cstate
                                      old-funenv
                                      new-funenv
                                      ren
                                      (1- limit))))
       :measure (nfix limit))

     (define switch-rest-induct ((old-cases swcase-listp)
                                 (new-cases swcase-listp)
                                 (old-default block-optionp)
                                 (new-default block-optionp)
                                 (target valuep)
                                 (old-cstate cstatep)
                                 (new-cstate cstatep)
                                 (old-funenv funenvp)
                                 (new-funenv funenvp)
                                 (ren renamingp)
                                 (limit natp))
       (b* (((when (zp limit)) nil)
            ((when (and (endp old-cases)
                        (endp new-cases)
                        old-default
                        new-default))
             (block-induct old-default
                           new-default
                           old-cstate
                           new-cstate
                           old-funenv
                           new-funenv
                           ren
                           (1- limit)))
            ((unless (and (consp old-cases)
                          (consp new-cases)))
             nil)
            (old-block (swcase->body (car old-cases)))
            (new-block (swcase->body (car new-cases))))
         (list (block-induct old-block
                             new-block
                             old-cstate
                             new-cstate
                             old-funenv
                             new-funenv
                             ren
                             (1- limit))
               (switch-rest-induct (cdr old-cases)
                                   (cdr new-cases)
                                   old-default
                                   new-default
                                   target
                                   old-cstate
                                   new-cstate
                                   old-funenv
                                   new-funenv
                                   ren
                                   (1- limit))))
       :measure (nfix limit))

     :flag-local nil))

  (local

   (defthm-induction-flag

     (defthm theorem-for-expression-induct
       (implies (and (not (resulterrp
                           (expression-renamevar old-expr new-expr ren)))
                     (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-expression old-expr
                                                   old-cstate
                                                   old-funenv
                                                   limit))
                     (new-outcome (exec-expression new-expr
                                                   new-cstate
                                                   new-funenv
                                                   limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (eoutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag expression-induct)

     (defthm theorem-for-expression-list-induct
       (implies (and (not (resulterrp
                           (expression-list-renamevar old-exprs new-exprs ren)))
                     (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-expression-list old-exprs
                                                        old-cstate
                                                        old-funenv
                                                        limit))
                     (new-outcome (exec-expression-list new-exprs
                                                        new-cstate
                                                        new-funenv
                                                        limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (eoutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag expression-list-induct)

     (defthm theorem-for-funcall-induct
       (implies (and (not (resulterrp
                           (funcall-renamevar old-funcall new-funcall ren)))
                     (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-funcall old-funcall
                                                old-cstate
                                                old-funenv
                                                limit))
                     (new-outcome (exec-funcall new-funcall
                                                new-cstate
                                                new-funenv
                                                limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (eoutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag funcall-induct)

     (defthm theorem-for-function-induct
       (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-function fun
                                                 args
                                                 old-cstate
                                                 old-funenv
                                                 limit))
                     (new-outcome (exec-function fun
                                                 args
                                                 new-cstate
                                                 new-funenv
                                                 limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (eoutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag function-induct)

     (defthm theorem-for-statement-induct
       (b* ((ren1 (statement-renamevar old-stmt new-stmt ren)))
         (implies (and (not (resulterrp ren1))
                       (cstate-renamevarp old-cstate new-cstate ren)
                       (funenv-renamevarp old-funenv new-funenv))
                  (b* ((old-outcome (exec-statement old-stmt
                                                    old-cstate
                                                    old-funenv
                                                    limit))
                       (new-outcome (exec-statement new-stmt
                                                    new-cstate
                                                    new-funenv
                                                    limit)))
                    (implies (and (not (resulterr-nonlimitp old-outcome))
                                  (not (resulterr-nonlimitp new-outcome)))
                             (soutcome-result-renamevarp old-outcome
                                                         new-outcome
                                                         ren1)))))
       :flag statement-induct)

     (defthm theorem-for-statement-list-induct
       (b* ((ren1 (statement-list-renamevar old-stmts new-stmts ren)))
         (implies (and (not (resulterrp ren1))
                       (cstate-renamevarp old-cstate new-cstate ren)
                       (funenv-renamevarp old-funenv new-funenv))
                  (b* ((old-outcome (exec-statement-list old-stmts
                                                         old-cstate
                                                         old-funenv
                                                         limit))
                       (new-outcome (exec-statement-list new-stmts
                                                         new-cstate
                                                         new-funenv
                                                         limit)))
                    (implies (and (not (resulterr-nonlimitp old-outcome))
                                  (not (resulterr-nonlimitp new-outcome)))
                             (soutcome-result-renamevarp old-outcome
                                                         new-outcome
                                                         ren1)))))
       :flag statement-list-induct)

     (defthm theorem-for-block-induct
       (implies (and (not (resulterrp
                           (block-renamevar old-block new-block ren)))
                     (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-block old-block
                                              old-cstate
                                              old-funenv
                                              limit))
                     (new-outcome (exec-block new-block
                                              new-cstate
                                              new-funenv
                                              limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (soutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag block-induct)

     (defthm theorem-for-for-iterations-induct
       (implies (and (not (resulterrp
                           (expression-renamevar old-test new-test ren)))
                     (not (resulterrp
                           (block-renamevar old-update new-update ren)))
                     (not (resulterrp
                           (block-renamevar old-body new-body ren)))
                     (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-for-iterations old-test
                                                       old-update
                                                       old-body
                                                       old-cstate
                                                       old-funenv
                                                       limit))
                     (new-outcome (exec-for-iterations new-test
                                                       new-update
                                                       new-body
                                                       new-cstate
                                                       new-funenv
                                                       limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (soutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag for-iterations-induct)

     (defthm theorem-for-switch-rest-induct
       (implies (and (not (resulterrp
                           (swcase-list-renamevar old-cases new-cases ren)))
                     (not (resulterrp
                           (block-option-renamevar old-default new-default ren)))
                     (cstate-renamevarp old-cstate new-cstate ren)
                     (funenv-renamevarp old-funenv new-funenv))
                (b* ((old-outcome (exec-switch-rest old-cases
                                                    old-default
                                                    target
                                                    old-cstate
                                                    old-funenv
                                                    limit))
                     (new-outcome (exec-switch-rest new-cases
                                                    new-default
                                                    target
                                                    new-cstate
                                                    new-funenv
                                                    limit)))
                  (implies (and (not (resulterr-nonlimitp old-outcome))
                                (not (resulterr-nonlimitp new-outcome)))
                           (soutcome-result-renamevarp old-outcome
                                                       new-outcome
                                                       ren))))
       :flag switch-rest-induct)

     :hints ((cond

              ((acl2::occur-lst '(acl2::flag-is 'switch-rest-induct) clause)
               '(:in-theory (enable
                             exec-switch-rest
                             resulterr-nonlimitp
                             block-option-renamevar-of-nil-1-forward
                             block-option-renamevar-of-nil-2-forward
                             soutcome-result-renamevarp-to-soutcome-renamevarp
                             soutcome-renamevarp
                             not-resulterr-limitp-of-soutcome
                             soutcome-result-renamevarp-of-errors-not-error
                             swcase-list-renamevar
                             block-option-renamevar-when-nonnil
                             block-option-some->val-when-nonnil
                             resulterrp-of-swcase-renamevar
                             resulterr-limitp-of-resulterr-of-info
                             not-resulterr-limitp-of-eval-literal)
                 :expand ((exec-switch-rest old-cases old-default
                                            target old-cstate old-funenv limit)
                          (exec-switch-rest new-cases new-default
                                            target new-cstate new-funenv limit)))
               ) ; switch-rest-induct

              ((acl2::occur-lst '(acl2::flag-is 'for-iterations-induct) clause)
               '(:in-theory (enable exec-for-iterations
                                    resulterr-nonlimitp
                                    resulterr-limitp-of-resulterr-of-info
                                    eoutcome-renamevarp
                                    soutcome-renamevarp
                                    eoutcome-result-renamevarp
                                    soutcome-result-renamevarp))
               ) ; for-iterations-induct

              ((acl2::occur-lst '(acl2::flag-is 'block-induct) clause)
               '(:in-theory (enable block-renamevar
                                    resulterr-nonlimitp
                                    resulterr-limitp-of-resulterr-of-info
                                    eoutcome-renamevarp
                                    soutcome-renamevarp
                                    eoutcome-result-renamevarp
                                    soutcome-result-renamevarp
                                    funenv-renamevarp-of-add-funs
                                    exec-when-renamevar-restrict-vars-lemma-1
                                    fundef-list-renamevar-of-statement-to-fundefs)
                 :use (:instance same-add-funs-error-when-renamevar
                       (old-funs (statements-to-fundefs (block->statements
                                                         old-block)))
                       (new-funs (statements-to-fundefs (block->statements
                                                         new-block))))
                 :expand ((exec-block old-block old-cstate old-funenv limit)
                          (exec-block new-block new-cstate new-funenv limit)))
               ) ; block-induct

              ((acl2::occur-lst '(acl2::flag-is 'statement-list-induct) clause)
               '(:in-theory (enable statement-list-renamevar
                                    exec-statement-list
                                    soutcome-result-renamevarp
                                    soutcome-renamevarp
                                    resulterr-nonlimitp
                                    cstate-renamevarp-of-larger
                                    resulterr-limitp-of-resulterr-of-info)
                 :expand ((statement-list-renamevar old-stmts new-stmts ren)))
               ) ; statement-list-induct

              ((acl2::occur-lst '(acl2::flag-is 'statement-induct) clause)
               '(:in-theory
                 (enable
                  statement-renamevar
                  exec-statement
                  soutcome-result-renamevarp
                  soutcome-renamevarp
                  cstate-renamevarp-of-larger
                  resulterr-nonlimitp
                  eoutcome-result-renamevarp
                  eoutcome-renamevarp
                  resulterr-limitp-of-resulterr-of-info
                  funenv-renamevarp-of-add-funs
                  exec-when-renamevar-restrict-vars-lemma-1
                  exec-when-renamevar-restrict-vars-lemma-2
                  fundef-list-renamevar-of-statement-to-fundefs
                  not-resulterr-limitp-of-const
                  not-resulterr-limitp-of-paths-to-vars
                  not-resulterr-limitp-of-write-vars-values
                  write-vars-values-when-renamevar
                  var-list-renamevar-not-error-when-path-list-renamevar
                  identifier-listp-when-identifier-list-resultp-and-not-resulterrp
                  not-resulterr-limitp-of-path-to-var
                  not-resulterr-limitp-of-write-var-value
                  write-var-value-when-renamevar
                  var-renamevar-not-error-when-path-renamevar
                  identifierp-when-identifier-resultp-and-not-resulterrp
                  not-resulterr-limitp-of-add-vars-values
                  add-vars-values-when-renamevar
                  same-len-when-add-vars-to-var-renaming
                  funcall-option-renamevar
                  funcall-option-some->val
                  not-resulterr-limitp-of-add-var-value
                  expression-option-renamevar
                  add-var-value-when-renamevar
                  expression-option-some->val)
                 :use ((:instance same-add-funs-error-when-renamevar
                        (old-funs (statements-to-fundefs
                                   (block->statements
                                    (statement-for->init old-stmt))))
                        (new-funs (statements-to-fundefs
                                   (block->statements
                                    (statement-for->init new-stmt))))))
                 :expand ((exec-statement old-stmt old-cstate old-funenv limit)
                          (exec-statement new-stmt new-cstate new-funenv limit)
                          (statement-renamevar old-stmt new-stmt ren)))
               ) ; statement-induct

              ((acl2::occur-lst '(acl2::flag-is 'function-induct) clause)
               '(:in-theory
                 (e/d (resulterr-nonlimitp
                       resulterr-limitp-of-resulterr-of-info
                       eoutcome-result-renamevarp
                       eoutcome-renamevarp
                       not-resulterr-limitp-of-find-fun
                       not-resulterr-limitp-of-init-local
                       funinfo-renamevarp
                       init-local-when-renamevar
                       soutcome-result-renamevarp
                       soutcome-renamevarp
                       not-resulterr-limitp-of-read-vars-values
                       value-listp-when-value-list-resultp-and-not-resulterrp
                       var-list-renamevar-when-add-vars-to-var-renaming)
                      ((:e renaming)))
                 :use ((:instance funinfo+funenv-renamevarp-of-find-fun
                        (old-env old-funenv)
                        (new-env new-funenv))
                       (:instance read-vars-values-when-renamevar
                        (old-cstate
                         (soutcome->cstate
                          (exec-block
                           (funinfo->body
                            (funinfo+funenv->info (find-fun fun old-funenv)))
                           (init-local
                            (funinfo->inputs
                             (funinfo+funenv->info (find-fun fun old-funenv)))
                            args
                            (funinfo->outputs
                             (funinfo+funenv->info (find-fun fun old-funenv)))
                            old-cstate)
                           (funinfo+funenv->env (find-fun fun old-funenv))
                           (+ -1 limit))))
                        (new-cstate
                         (soutcome->cstate
                          (exec-block
                           (funinfo->body
                            (funinfo+funenv->info (find-fun fun new-funenv)))
                           (init-local
                            (funinfo->inputs
                             (funinfo+funenv->info (find-fun fun new-funenv)))
                            args
                            (funinfo->outputs
                             (funinfo+funenv->info (find-fun fun new-funenv)))
                            new-cstate)
                           (funinfo+funenv->env (find-fun fun new-funenv))
                           (+ -1 limit))))
                        (ren
                         (add-vars-to-var-renaming
                          (funinfo->outputs
                           (funinfo+funenv->info (find-fun fun old-funenv)))
                          (funinfo->outputs
                           (funinfo+funenv->info (find-fun fun new-funenv)))
                          (add-vars-to-var-renaming
                           (funinfo->inputs
                            (funinfo+funenv->info (find-fun fun old-funenv)))
                           (funinfo->inputs
                            (funinfo+funenv->info (find-fun fun new-funenv)))
                           (renaming nil))))
                        (old-vars
                         (funinfo->outputs
                          (funinfo+funenv->info (find-fun fun old-funenv))))
                        (new-vars
                         (funinfo->outputs
                          (funinfo+funenv->info (find-fun fun new-funenv))))))
                 :expand ((exec-function fun args old-cstate old-funenv limit)
                          (exec-function fun args new-cstate new-funenv limit)))
               ) ; function-induct

              ((acl2::occur-lst '(acl2::flag-is 'funcall-induct) clause)
               '(:in-theory (enable funcall-renamevar
                                    eoutcome-result-renamevarp
                                    eoutcome-renamevarp
                                    resulterr-nonlimitp
                                    expression-list-renamevar-of-rev-not-error
                                    resulterr-limitp-of-resulterr-of-info)
                 :expand
                 ((exec-funcall old-funcall old-cstate old-funenv limit)
                  (exec-funcall new-funcall new-cstate new-funenv limit)))
               ) ; funcall-induct

              ((acl2::occur-lst '(acl2::flag-is 'expression-list-induct) clause)
               '(:in-theory (enable expression-list-renamevar
                                    exec-expression-list
                                    eoutcome-result-renamevarp
                                    eoutcome-renamevarp
                                    resulterr-nonlimitp
                                    resulterr-limitp-of-resulterr-of-info))
               ) ; expression-list-induct

              ((acl2::occur-lst '(acl2::flag-is 'expression-induct) clause)
               '(:in-theory (enable expression-renamevar
                                    exec-expression
                                    exec-literal
                                    not-resulterr-limitp-of-eval-literal
                                    eoutcome-result-renamevarp
                                    eoutcome-renamevarp
                                    resulterr-nonlimitp
                                    resulterr-limitp-of-resulterr-of-info
                                    exec-path
                                    not-resulterr-limitp-of-path-to-var
                                    var-renamevar-not-error-when-path-renamevar
                                    not-resulterr-limitp-of-read-var-value)
                 :use (:instance read-var-value-when-renamevar
                       (old-var (path-to-var (expression-path->get old-expr)))
                       (new-var (path-to-var (expression-path->get new-expr)))
                       (ren ren)))
               ) ; expression-induct

              )) ; hints

     ))

  (defruled exec-expression-when-renamevar
    (implies (and (not (resulterrp
                        (expression-renamevar old-expr new-expr ren)))
                  (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-expression old-expr
                                                old-cstate
                                                old-funenv
                                                limit))
                  (new-outcome (exec-expression new-expr
                                                new-cstate
                                                new-funenv
                                                limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (eoutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren)))))

  (defruled exec-expression-list-when-renamevar
    (implies (and (not (resulterrp
                        (expression-list-renamevar old-exprs new-exprs ren)))
                  (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-expression-list old-exprs
                                                     old-cstate
                                                     old-funenv
                                                     limit))
                  (new-outcome (exec-expression-list new-exprs
                                                     new-cstate
                                                     new-funenv
                                                     limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (eoutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren)))))

  (defruled exec-funcall-when-renamevar
    (implies (and (not (resulterrp
                        (funcall-renamevar old-funcall new-funcall ren)))
                  (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-funcall old-funcall
                                             old-cstate
                                             old-funenv
                                             limit))
                  (new-outcome (exec-funcall new-funcall
                                             new-cstate
                                             new-funenv
                                             limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (eoutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren)))))

  (defruled exec-function-when-renamevar
    (implies (and (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-function fun
                                              args
                                              old-cstate
                                              old-funenv
                                              limit))
                  (new-outcome (exec-function fun
                                              args
                                              new-cstate
                                              new-funenv
                                              limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (eoutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren)))))

  (defruled exec-statement-when-renamevar
    (b* ((ren1 (statement-renamevar old-stmt new-stmt ren)))
      (implies (and (not (resulterrp ren1))
                    (cstate-renamevarp old-cstate new-cstate ren)
                    (funenv-renamevarp old-funenv new-funenv))
               (b* ((old-outcome (exec-statement old-stmt
                                                 old-cstate
                                                 old-funenv
                                                 limit))
                    (new-outcome (exec-statement new-stmt
                                                 new-cstate
                                                 new-funenv
                                                 limit)))
                 (implies (and (not (resulterr-nonlimitp old-outcome))
                               (not (resulterr-nonlimitp new-outcome)))
                          (soutcome-result-renamevarp old-outcome
                                                      new-outcome
                                                      ren1))))))

  (defruled exec-statement-list-when-renamevar
    (b* ((ren1 (statement-list-renamevar old-stmts new-stmts ren)))
      (implies (and (not (resulterrp ren1))
                    (cstate-renamevarp old-cstate new-cstate ren)
                    (funenv-renamevarp old-funenv new-funenv))
               (b* ((old-outcome (exec-statement-list old-stmts
                                                      old-cstate
                                                      old-funenv
                                                      limit))
                    (new-outcome (exec-statement-list new-stmts
                                                      new-cstate
                                                      new-funenv
                                                      limit)))
                 (implies (and (not (resulterr-nonlimitp old-outcome))
                               (not (resulterr-nonlimitp new-outcome)))
                          (soutcome-result-renamevarp old-outcome
                                                      new-outcome
                                                      ren1))))))

  (defruled exec-block-when-renamevar
    (implies (and (not (resulterrp
                        (block-renamevar old-block new-block ren)))
                  (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-block old-block
                                           old-cstate
                                           old-funenv
                                           limit))
                  (new-outcome (exec-block new-block
                                           new-cstate
                                           new-funenv
                                           limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (soutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren)))))

  (defruled exec-for-iterations-when-renamevar
    (implies (and (not (resulterrp
                        (expression-renamevar old-test new-test ren)))
                  (not (resulterrp
                        (block-renamevar old-update new-update ren)))
                  (not (resulterrp
                        (block-renamevar old-body new-body ren)))
                  (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-for-iterations old-test
                                                    old-update
                                                    old-body
                                                    old-cstate
                                                    old-funenv
                                                    limit))
                  (new-outcome (exec-for-iterations new-test
                                                    new-update
                                                    new-body
                                                    new-cstate
                                                    new-funenv
                                                    limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (soutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren)))))

  (defruled exec-switch-rest-when-renamevar
    (implies (and (not (resulterrp
                        (swcase-list-renamevar old-cases new-cases ren)))
                  (not (resulterrp
                        (block-option-renamevar old-default new-default ren)))
                  (cstate-renamevarp old-cstate new-cstate ren)
                  (funenv-renamevarp old-funenv new-funenv))
             (b* ((old-outcome (exec-switch-rest old-cases
                                                 old-default
                                                 target
                                                 old-cstate
                                                 old-funenv
                                                 limit))
                  (new-outcome (exec-switch-rest new-cases
                                                 new-default
                                                 target
                                                 new-cstate
                                                 new-funenv
                                                 limit)))
               (implies (and (not (resulterr-nonlimitp old-outcome))
                             (not (resulterr-nonlimitp new-outcome)))
                        (soutcome-result-renamevarp old-outcome
                                                    new-outcome
                                                    ren))))))
