; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")
(include-book "literal-evaluation")
(include-book "modes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; To generate additional theorems.
(local
 (fty::deflist value-list
   :elt-type value
   :true-listp t
   :elementp-of-nil nil
   :pred value-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (language)
  :short "Dynamic semantics of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the dynamic semantics of Yul
     by formalizing the Yul computation state
     and by defining ACL2 functions that manipulate the computation state
     via execution of the Yul abstract syntax.
     The formalization also involves a function environment
     that includes the Yul functions in scope,
     and that is manipulated along with the computation state.")
   (xdoc::p
    "This is based on the semi-formal specification in
     [Yul: Specification of Yul: Formal Specification],
     which defines an interpreter for Yul.")
   (xdoc::p
    "We formalize a big-step interpretive semantics,
     which consists of mutually recursive execution functions.
     To ensure their termination, as required by ACL2,
     these functions take a limit argument
     that is decremented at each recursive call.
     This is an artificial limit,
     that has no counterpart in the run-time data of an executing Yul program.
     Formal proofs need to deal with this limit,
     e.g. the termination of a Yul program is proved
     by showing that there is a suitable limit that does not run out."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funinfo
  :short "Fixtype of function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is all the information about a function definition,
     except for its name."))
  ((inputs identifier-list)
   (outputs identifier-list)
   (body block))
  :tag :funinfo
  :pred funinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funinfo-result
  :short "Fixtype of errors and function information."
  :ok funinfo
  :pred funinfo-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo-for-fundef ((fundef fundefp))
  :returns (funinfo funinfop)
  :short "Function information for a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This just takes the inputs, outputs, and body of the function definition
     and forms function information with them."))
  (make-funinfo :inputs (fundef->inputs fundef)
                :outputs (fundef->outputs fundef)
                :body (fundef->body fundef))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap funscope
  :short "Fixtype of function scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a finite map from identifiers (function names)
     to function information:
     it models the function definitions in a scope."))
  :key-type identifier
  :val-type funinfo
  :pred funscopep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funscope-result
  :short "Fixtype of errors and function scopes."
  :ok funscope
  :pred funscope-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-for-fundefs ((fundefs fundef-listp))
  :returns (funscope funscope-resultp)
  :short "Function scope for a list of function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the list and form a function scope for the functions.
     It is an error if there are two functions with the same name."))
  (b* (((when (endp fundefs)) nil)
       ((okf scope) (funscope-for-fundefs (cdr fundefs)))
       (fundef (car fundefs))
       (fun (fundef->name fundef))
       (fun+info (omap::assoc fun scope))
       ((when (consp fun+info)) (reserrf (list :duplicate-function fun))))
    (omap::update fun (funinfo-for-fundef fundef) scope))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-funscope-for-fundefs
    (implies (reserrp funscope)
             (error-info-wfp funscope))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist funenv
  :short "Fixtype of function environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a list of function scopes,
     which represents a stack;
     the stack grows leftward, i.e.
     push is @(tsee cons), pop is @(tsee cdr), and top is @(tsee car).
     A function scope is pushed when entering a block,
     and it is popped when exiting the block.
     This needs to be a stack because Yul functions are statically scoped:
     when a function later in the stack calls a function earlier in the stack,
     the stack must be shrunk so that the called function
     has access only to the functions that are statically in scope,
     not the functions in inner blocks that the caller has access to.")
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification]
     does not explicitly mention any notion of function environments,
     but their presence is implicit in the description of
     the scope of function definitions."))
  :elt-type funscope
  :true-listp t
  :elementp-of-nil t
  :pred funenvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funenv-result
  :short "Fixtype of errors and function environments."
  :ok funenv
  :pred funenv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funinfo+funenv
  :short "Fixtype of pairs consisting of
          function information and a function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as (non-error) results of @(tsee find-fun):
     see that function's documentation."))
  ((info funinfo)
   (env funenv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funinfo+funenv-result
  :short "Fixtype of errors and
          pairs consisting of
          function information and a function environment."
  :ok funinfo+funenv
  :pred funinfo+funenv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-fun ((fun identifierp) (funenv funenvp))
  :returns (info funinfo+funenv-resultp)
  :short "Find a function in the function environment by name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We search through the scopes, from innermost to outermost.
     It is an expected invariant that the scopes in a function environment
     have disjoint function names
     (we may formalize and prove this invariant at some point):
     thus, the search order would not matter
     if we only needed the function information;
     however, as explained below, we also return a function environment,
     and therefore the innermost-to-outermost search order is important.")
   (xdoc::p
    "If we find @('fun'), we return not only its information,
     but also the current function environment,
     which is the initial function environment
     with zero or more scopes popped;
     the scope where @('fun') is found is not popped,
     i.e. it is returned as the top scope.
     This resulting function environment represents
     the functions in scope for @('fun').
     In @(tsee exec-function), which takes a @('fun') as argument,
     we call @('find-fun') to retrieve the information about @('fun')
     so that we can execute its body:
     thus, it is convenient for @('find-fun') to return
     the function environment for @('fun'),
     which must be indeed passed to @(tsee exec-block) on the @('fun')'s body.")
   (xdoc::p
    "It is an error if @('fun') is not found in the environment."))
  (b* (((when (endp funenv))
        (reserrf (list :function-not-found (identifier-fix fun))))
       (funscope (funscope-fix (car funenv)))
       (fun+info (omap::assoc (identifier-fix fun) funscope))
       ((when (consp fun+info))
        (make-funinfo+funenv :info (cdr fun+info) :env funenv)))
    (find-fun fun (cdr funenv)))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-find-fun
    (implies (reserrp info)
             (error-info-wfp info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ensure-funscope-disjoint ((funscope funscopep) (funenv funenvp))
  :returns (_ reserr-optionp)
  :short "Ensure that a function scope is disjoint from a function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, ensure that the function names in the scope
     are disjoint from all the function names in the environment's scopes.
     This is used to ensure that there is no function shadowing:
     see @(tsee add-funs)."))
  (b* (((when (endp funenv)) nil)
       (overlap (set::intersect (omap::keys (funscope-fix funscope))
                                (omap::keys (funscope-fix (car funenv)))))
       ((unless (set::emptyp overlap))
        (reserrf (list :duplicate-functions overlap))))
    (ensure-funscope-disjoint funscope (cdr funenv)))
  :hooks (:fix)
  ///

  (defrule ensure-funscope-disjoint-of-empty-funscope-not-error
    (not (reserrp (ensure-funscope-disjoint nil funenv))))

  (defret error-info-wfp-of-ensure-funscope-disjoint
    (implies (reserrp _)
             (error-info-wfp _))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-funs ((fundefs fundef-listp) (funenv funenvp))
  :returns (new-funenv funenv-resultp)
  :short "Add functions to the function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We create a function scope for the given list of function definitions
     and we push that onto the function environment.
     We ensure that the new functions have different names from
     the functions already in the environment.
     This ACL2 function is used for all the function definitions in a block;
     see @(tsee exec-block)."))
  (b* (((okf funscope) (funscope-for-fundefs fundefs))
       ((okf &) (ensure-funscope-disjoint funscope funenv)))
    (cons funscope (funenv-fix funenv)))
  :hooks (:fix)
  :prepwork
  ((local
    (in-theory
     (enable funscopep-when-funscope-resultp-and-not-reserrp))))
  ///

  (defrule add-funs-of-no-fundefs
    (equal (add-funs nil funenv)
           (cons nil (funenv-fix funenv))))

  (defret error-info-wfp-of-add-funs
    (implies (reserrp new-funenv)
             (error-info-wfp new-funenv))
    :hints
    (("Goal"
      :in-theory
      (enable
       not-reserrp-when-funenvp
       funscopep-when-funscope-resultp-and-not-reserrp
       funenvp-when-funenv-resultp-and-not-reserrp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap lstate
  :short "Fixtype of local states."
  :long
  (xdoc::topstring
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification] introduces
     the notion of local state object as
     a finite map from identifiers to values."))
  :key-type identifier
  :val-type value
  :pred lstatep

  ///

  (defrule lstatep-of-restrict
    (implies (lstatep map)
             (lstatep (omap::restrict keys map)))
    :enable omap::restrict)

  (defrule identifier-setp-of-keys-when-lstatep
    (implies (lstatep map)
             (identifier-setp (omap::keys map)))
    :enable omap::keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cstate
  :short "Fixtype of computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     this consists of a local state object and a global state object.
     The latter is generic in generic Yul.
     For now, for simplicity, we ignore the global state completely,
     but we plan to add that at some point."))
  ((local lstate))
  :tag :cstate
  :pred cstatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult cstate-result
  :short "Fixtype of errors and computation states."
  :ok cstate
  :pred cstate-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-var-value ((var identifierp) (cstate cstatep))
  :returns (val value-resultp)
  :short "Read a variable value from the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the variable does not exist."))
  (b* ((lstate (cstate->local cstate))
       (var-val (omap::assoc (identifier-fix var) lstate))
       ((unless (consp var-val))
        (reserrf (list :variable-not-found (identifier-fix var)))))
    (value-fix (cdr var-val)))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-read-var-value
    (implies (reserrp val)
             (error-info-wfp val))
    :hints (("Goal" :in-theory (enable not-reserrp-when-valuep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-vars-values ((vars identifier-listp) (cstate cstatep))
  :returns (vals
            value-list-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               valuep-when-value-resultp-and-not-reserrp
               value-listp-when-value-list-resultp-and-not-reserrp))))
  :short "Lift @(tsee read-var-value) to lists."
  (b* (((when (endp vars)) nil)
       ((okf val) (read-var-value (car vars) cstate))
       ((okf vals) (read-vars-values (cdr vars) cstate)))
    (cons val vals))
  :hooks (:fix)
  ///

  (defret len-of-read-vars-values
    (implies (not (reserrp vals))
             (equal (len vals)
                    (len vars))))

  (defret error-info-wfp-of-read-vars-values
    (implies (reserrp vals)
             (error-info-wfp vals))
    :hints (("Goal"
             :in-theory
             (enable not-reserrp-when-value-listp
                     valuep-when-value-resultp-and-not-reserrp
                     value-listp-when-value-list-resultp-and-not-reserrp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-var-value ((var identifierp) (val valuep) (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Write a variable value to the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the variable does not exist."))
  (b* ((lstate (cstate->local cstate))
       (var-val (omap::assoc (identifier-fix var) lstate))
       ((unless (consp var-val))
        (reserrf (list :variable-not-found (identifier-fix var))))
       (new-lstate (omap::update (identifier-fix var)
                                 (value-fix val)
                                 lstate))
       (new-cstate (change-cstate cstate :local new-lstate)))
    new-cstate)
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-write-var-value
    (implies (reserrp new-cstate)
             (error-info-wfp new-cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-vars-values ((vars identifier-listp)
                           (vals value-listp)
                           (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Lift @(tsee write-var-value) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if there are extra values or extra variables.
     Their number must be the same.
     We make this a run-time check because
     it is part of the conditions to be checked
     by the defensive dynamic semantics."))
  (b* (((when (endp vars))
        (if (endp vals)
            (cstate-fix cstate)
          (reserrf (list :extra-values (value-list-fix vals)))))
       ((when (endp vals))
        (reserrf (list :extra-variables (identifier-list-fix vars))))
       ((okf cstate) (write-var-value (car vars) (car vals) cstate)))
    (write-vars-values (cdr vars) (cdr vals) cstate))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-write-vars-values
    (implies (reserrp new-cstate)
             (error-info-wfp new-cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var-value ((var identifierp) (val valuep) (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Add a variable with a value to the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the variable already exists."))
  (b* ((lstate (cstate->local cstate))
       (var-val (omap::assoc (identifier-fix var) lstate))
       ((when (consp var-val))
        (reserrf (list :variable-already-exists (identifier-fix var))))
       (new-lstate (omap::update (identifier-fix var)
                                 (value-fix val)
                                 lstate))
       (new-cstate (change-cstate cstate :local new-lstate)))
    new-cstate)
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-add-var-value
    (implies (reserrp new-cstate)
             (error-info-wfp new-cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-vars-values ((vars identifier-listp)
                         (vals value-listp)
                         (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Lift @(tsee add-var-value) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if there are extra values or extra variables.
     Their number must be the same.
     We make this a run-time check because
     it is part of the conditions to be checked
     by the defensive dynamic semantics."))
  (b* (((when (endp vars))
        (if (endp vals)
            (cstate-fix cstate)
          (reserrf (list :extra-values (value-list-fix vals)))))
       ((when (endp vals))
        (reserrf (list :extra-variables (identifier-list-fix vars))))
       ((okf cstate) (add-var-value (car vars) (car vals) cstate)))
    (add-vars-values (cdr vars) (cdr vals) cstate))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-add-vars-values
    (implies (reserrp new-cstate)
             (error-info-wfp new-cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-vars ((vars identifier-setp) (cstate cstatep))
  :returns (new-cstate cstatep)
  :short "Restrict the variables in the local state to a specified set."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when a block is exited:
     any new variable declared in the block is discarded,
     by retaining only the variables
     present in the local state before the block;
     any of the retained variables must retain their values from the block
     (i.e. the block may modify them)."))
  (b* ((lstate (cstate->local cstate))
       (new-lstate (omap::restrict (identifier-set-fix vars) lstate)))
    (change-cstate cstate :local new-lstate))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-restrict-vars
    (implies (reserrp new-cstate)
             (error-info-wfp new-cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-local ((in-vars identifier-listp)
                    (in-vals value-listp)
                    (out-vars identifier-listp)
                    (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Initialize the local state of a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used at the beginning of the execution of a function call.
     The local state is set to consist of
     the input and output variables of the function,
     which are passed as the @('in-vars') and @('out-vars') parameters.
     The input variables are initialized with the input values,
     passed as the @('in-vals') parameters;
     note that we implicitly check that the number of input variables
     matches the number of input values.
     The output variables are initialized to 0."))
  (declare (ignore cstate))
  (b* ((cstate (change-cstate cstate :local nil))
       ((okf cstate) (add-vars-values in-vars in-vals cstate))
       ((okf cstate) (add-vars-values out-vars
                                     (repeat (len out-vars) (value 0))
                                     cstate)))
    cstate)
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-init-local
    (implies (reserrp new-cstate)
             (error-info-wfp new-cstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod eoutcome
  :short "Fixtype of expression outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     the execution of an expression results in
     not only zero of more values,
     but also possibly updated global and local states.
     [Yul: Specification of Yul: Formal Specification]
     does not have an explicit name for this notion,
     which in our formalization consists of
     a computation state and a list of values.
     We call this an expression outcome."))
  ((cstate cstate)
   (values value-list))
  :tag :eoutcome
  :pred eoutcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult eoutcome-result
  :short "Fixtype of errors and expression outcomes."
  :ok eoutcome
  :pred eoutcome-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod soutcome
  :short "Fixtype of statement outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     the execution of a statement results in
     not only possibly updated global and local states,
     but also a mode.
     [Yul: Specification of Yul: Formal Specification]
     does not have an explicit name for this notion,
     which in our formalization consists of
     a computation state and a mode.
     We call this a statement outcome."))
  ((cstate cstate)
   (mode mode))
  :tag :soutcome
  :pred soutcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult soutcome-result
  :short "Fixtype of errors and statement outcomes."
  :ok soutcome
  :pred soutcome-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-to-var ((path pathp))
  :returns (var identifier-resultp)
  :short "Extract a variable from a path."
  :long
  (xdoc::topstring
   (xdoc::p
    "As in the static semantics, also in the dynamic semantics
     we require a path to consist of a single identifier.
     This ACL2 function makes that check, returning the identifier.
     This is the variable denoted by the path."))
  (b* ((idens (path->get path))
       ((unless (consp idens))
        (reserrf (list :empty-path (path-fix path))))
       ((unless (endp (cdr idens)))
        (reserrf (list :non-singleton-path (path-fix path))))
       (var (car idens)))
    var)
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-path-to-var
    (implies (reserrp var)
             (error-info-wfp var))
    :hints (("Goal" :in-theory (enable not-reserrp-when-identifierp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define paths-to-vars ((paths path-listp))
  :returns
  (vars
   identifier-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      identifierp-when-identifier-resultp-and-not-reserrp
      identifier-listp-when-identifier-list-resultp-and-not-reserrp))))
  :short "Extract variables from paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee path-to-var) to lists."))
  (b* (((when (endp paths)) nil)
       ((okf var) (path-to-var (car paths)))
       ((okf vars) (paths-to-vars (cdr paths))))
    (cons var vars))
  :hooks (:fix)
  ///

  (defret len-of-paths-to-vars
    (implies (not (reserrp vars))
             (equal (len vars)
                    (len paths))))

  (defret error-info-wfp-of-paths-to-vars
    (implies (reserrp vars)
             (error-info-wfp vars))
    :hints
    (("Goal"
      :in-theory
      (enable
       not-reserrp-when-identifier-listp
       identifierp-when-identifier-resultp-and-not-reserrp
       identifier-listp-when-identifier-list-resultp-and-not-reserrp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-path ((path pathp) (cstate cstatep))
  :returns (outcome eoutcome-resultp)
  :short "Execute a path."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look up the variable in the computation state.
     This always returns a single value,
     and does not change the computation state."))
  (b* (((okf var) (path-to-var path))
       ((okf val) (read-var-value var cstate)))
    (make-eoutcome :cstate cstate :values (list val)))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-exec-path
    (implies (reserrp outcome)
             (error-info-wfp outcome))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-literal ((lit literalp) (cstate cstatep))
  :returns (outcome eoutcome-resultp)
  :short "Execute a literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing a literal
     returns a single value
     and does not change the computation state."))
  (b* (((okf val) (eval-literal lit)))
    (make-eoutcome :cstate cstate :values (list val)))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-exec-literal
    (implies (reserrp outcome)
             (error-info-wfp outcome))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec
  :short "Mutually recursive execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing expressions involves executing function calls,
     which involves executing the statements in function bodies,
     which involves executing the expressions in the statements."))

  (define exec-expression ((expr expressionp)
                           (cstate cstatep)
                           (funenv funenvp)
                           (limit natp))
    :returns (outcome eoutcome-resultp)
    :short "Execute an expression."
    (b* (((when (zp limit)) (reserrf (list :limit (expression-fix expr)))))
      (expression-case
       expr
       :path (exec-path expr.get cstate)
       :literal (exec-literal expr.get cstate)
       :funcall (exec-funcall expr.get cstate funenv (1- limit))))
    :measure (nfix limit))

  (define exec-expression-list ((exprs expression-listp)
                                (cstate cstatep)
                                (funenv funenvp)
                                (limit natp))
    :returns (outcome eoutcome-resultp)
    :short "Execute a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Lists of expressions are evaluated left-to-right.
       Lists of expressions are used as arguments of function calls.
       Each expression in the list must return exactly one result.
       The returned expression outcome,
       if all the expressions are successfuly evaluated,
       includes a list of values, one for each expression, in the same order."))
    (b* (((when (zp limit)) (reserrf (list :limit (expression-list-fix exprs))))
         ((when (endp exprs)) (make-eoutcome :cstate (cstate-fix cstate)
                                             :values nil))
         ((okf (eoutcome outcome))
          (exec-expression (car exprs) cstate funenv (1- limit)))
         ((unless (equal (len outcome.values) 1))
          (reserrf (list :not-single-value outcome.values)))
         (val (car outcome.values))
         ((okf (eoutcome outcome))
          (exec-expression-list (cdr exprs) outcome.cstate funenv (1- limit))))
      (make-eoutcome :cstate outcome.cstate :values (cons val outcome.values)))
    :measure (nfix limit))

  (define exec-funcall ((call funcallp)
                        (cstate cstatep)
                        (funenv funenvp)
                        (limit natp))
    :returns (outcome eoutcome-resultp)
    :short "Execute a function call."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate the argument expressions,
       and then we delegate the rest to @(tsee exec-function).
       The expressions are evaluated in reverse,
       consistently with the formal interpreter
       in [Yul: Specification of Yul: Formal Specification]."))
    (b* (((when (zp limit)) (reserrf (list :limit (funcall-fix call))))
         ((funcall call) call)
         ((okf (eoutcome outcome))
          (exec-expression-list (rev call.args) cstate funenv (1- limit))))
      (exec-function call.name outcome.values outcome.cstate funenv (1- limit)))
    :measure (nfix limit))

  (define exec-function ((fun identifierp)
                         (args value-listp)
                         (cstate cstatep)
                         (funenv funenvp)
                         (limit natp))
    :returns (outcome eoutcome-resultp)
    :short "Execution a function on some values."
    :long
    (xdoc::topstring
     (xdoc::p
      "The code in this ACL2 function
       could be inlined into @(tsee exec-funcall),
       but it seems useful to have a separate ACL2 function
       that takes values directly as arguments,
       in case we want to formally talk about function calls.")
     (xdoc::p
      "We find the function in the function environment,
       also obtaining the (generally smaller) function environment
       for executing the function.
       We initialize the local state with the function's inputs and outputs.
       We run the function body on the resulting computation state
       and on the function environment for executing the function.
       We read the final values of the function output variables
       and return them as result.
       We also restore the local state prior to the function call.")
     (xdoc::p
      "As a defensive check, we ensure that the function's body
       terminates regularly or via @('leave'),
       not via @('break') or @('continue')."))
    (b* (((when (zp limit)) (reserrf (list :limit
                                           (identifier-fix fun)
                                           (value-list-fix args))))
         ((okf (funinfo+funenv info+env)) (find-fun fun funenv))
         ((funinfo info) info+env.info)
         (lstate-before (cstate->local cstate))
         ((okf cstate) (init-local info.inputs args info.outputs cstate))
         ((okf (soutcome outcome))
          (exec-block info.body cstate info+env.env (1- limit)))
         ((when (mode-case outcome.mode :break))
          (reserrf (list :break-from-function (identifier-fix fun))))
         ((when (mode-case outcome.mode :continue))
          (reserrf (list :continue-from-function (identifier-fix fun))))
         ((okf vals) (read-vars-values info.outputs outcome.cstate))
         (cstate (change-cstate outcome.cstate
                                :local lstate-before)))
      (make-eoutcome :cstate cstate :values vals))
    :measure (nfix limit))

  (define exec-statement ((stmt statementp)
                          (cstate cstatep)
                          (funenv funenvp)
                          (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "Executing a block statement reduces to the execution of the block,
       which is handled by a separate ACL2 function.")
     (xdoc::p
      "In a single variable declaration with an initializing expression,
       the expression must yield exactly one value;
       if there is no initializing expression, the default value is 0.
       In a multiple variable declaration with an initializing function call,
       the funcion call may yield any number of values,
       which must match the number of variables
       (this is checked in @(tsee add-vars-values)),
       which must be two or more;
       if there is no initializing function call,
       the default value is 0 for each variable.
       In both kinds of assignments,
       we extend the computation state with the new variable(s).")
     (xdoc::p
      "For a single variable assignment,
       we ensure that the path is a singleton,
       we execute the expression, which must return a single value,
       and we write to the variable.
       For a multiple variable assignment,
       we ensure that each path is a singleton
       and that there are at least two variables,
       we execute the function call,
       which must return the same number of values as the variables
       (this is checked in @(tsee write-vars-values),
       and we write to the variables.")
     (xdoc::p
      "For a function call statement,
       we execute the function call (for side effects),
       which must return no values.")
     (xdoc::p
      "For a conditional, we first execute the condition.
       Given that our current model of Yul does not include boolean,
       and also based on discussions on Gitter,
       we consider 0 to be false and any non-0 value to be true.
       If the condition is true, we execute the body;
       otherwise we terminate regularly.")
     (xdoc::p
      "A @('leave'), @('break'), or @('continue') statement
       leaves the computation state unchanged
       and returns the corresponding mode.")
     (xdoc::p
      "For a switch statement, we execute the target,
       ensuring it returns a single value.
       Then we delegate the rest to a separate ACL2 function.")
     (xdoc::p
      "For a loop statement,
       we start by saving (the names of) the variables before the loop,
       similarly to @(tsee exec-block).
       The initialization block of a loop statement
       is not treated like other blocks:
       its scope extends to the rest of the loop statement.
       Thus, instead of executing the initialization block as a block,
       we take the statements in the block,
       extend the function environment with any function declared there,
       and execute the statements,
       which may result in new and updated variables.
       We defensively stop with an error if the initialization block
       terminates with @('break') or @('continue');
       if it terminates with @('leave'), we also terminate with @('leave'),
       removing extra variables and restoring the function environment.
       We delegate the execution of the loop iterations
       to another ACL2 function.
       We take the result of that ACL2 function,
       and remove the variables added by the loop
       (similarly to @(tsee exec-block)).")
     (xdoc::p
      "A function definition
       does not change the computation state
       and terminates regularly.
       It is like a no-op when it is encountered as a statement.
       The function definitions in a block
       are incorporated into the function environment of the computation state
       prior to starting to execute the statements in the block."))
    (b* (((when (zp limit)) (reserrf (list :limit (statement-fix stmt)))))
      (statement-case
       stmt
       :block (exec-block stmt.get cstate funenv (1- limit))
       :variable-single
       (expression-option-case
        stmt.init
        :some
        (b* (((okf (eoutcome outcome))
              (exec-expression stmt.init.val cstate funenv (1- limit)))
             ((unless (equal (len outcome.values) 1))
              (reserrf (list :not-single-value outcome.values)))
             ((okf cstate)
              (add-var-value stmt.name (car outcome.values) outcome.cstate)))
          (make-soutcome :cstate cstate :mode (mode-regular)))
        :none
        (b* (((okf cstate) (add-var-value stmt.name (value 0) cstate)))
          (make-soutcome :cstate cstate :mode (mode-regular))))
       :variable-multi
       (if (>= (len stmt.names) 2)
           (funcall-option-case
            stmt.init
            :some
            (b* (((okf (eoutcome outcome))
                  (exec-funcall stmt.init.val cstate funenv (1- limit)))
                 ((okf cstate)
                  (add-vars-values stmt.names outcome.values outcome.cstate)))
              (make-soutcome :cstate cstate :mode (mode-regular)))
            :none
            (b* (((okf cstate) (add-vars-values stmt.names
                                               (repeat (len stmt.names)
                                                       (value 0))
                                               cstate)))
              (make-soutcome :cstate cstate :mode (mode-regular))))
         (reserrf (list :non-multiple-variables stmt.names)))
       :assign-single
       (b* (((okf var) (path-to-var stmt.target))
            ((okf (eoutcome outcome))
             (exec-expression stmt.value cstate funenv (1- limit)))
            ((unless (equal (len outcome.values) 1))
             (reserrf (list :not-single-value outcome.values)))
            ((okf cstate)
             (write-var-value var (car outcome.values) outcome.cstate)))
         (make-soutcome :cstate cstate :mode (mode-regular)))
       :assign-multi
       (b* (((unless (>= (len stmt.targets) 2))
             (reserrf (list :non-multiple-variables stmt.targets)))
            ((okf vars) (paths-to-vars stmt.targets))
            ((okf (eoutcome outcome))
             (exec-funcall stmt.value cstate funenv (1- limit)))
            ((okf cstate)
             (write-vars-values vars outcome.values outcome.cstate)))
         (make-soutcome :cstate cstate :mode (mode-regular)))
       :funcall
       (b* (((okf (eoutcome outcome))
             (exec-funcall stmt.get cstate funenv (1- limit)))
            ((when (consp outcome.values))
             (reserrf (list :funcall-statement-returns outcome.values))))
         (make-soutcome :cstate outcome.cstate :mode (mode-regular)))
       :if
       (b* (((okf (eoutcome outcome))
             (exec-expression stmt.test cstate funenv (1- limit)))
            ((unless (equal (len outcome.values) 1))
             (reserrf (list :if-test-not-single-value outcome.values)))
            (val (car outcome.values)))
         (if (equal val (value 0))
             (make-soutcome :cstate outcome.cstate :mode (mode-regular))
           (exec-block stmt.body outcome.cstate funenv (1- limit))))
       :for
       (b* ((vars-before (omap::keys (cstate->local cstate)))
            (stmts (block->statements stmt.init))
            ((okf funenv) (add-funs (statements-to-fundefs stmts) funenv))
            ((okf (soutcome outcome))
             (exec-statement-list stmts cstate funenv (1- limit)))
            ((when (mode-case outcome.mode :break))
             (reserrf (list :break-from-for-init (statement-fix stmt))))
            ((when (mode-case outcome.mode :continue))
             (reserrf (list :continue-from-for-init (statement-fix stmt))))
            ((when (mode-case outcome.mode :leave))
             (b* ((cstate (restrict-vars vars-before outcome.cstate)))
               (make-soutcome :cstate cstate :mode (mode-leave))))
            ((okf (soutcome outcome))
             (exec-for-iterations stmt.test
                                  stmt.update
                                  stmt.body
                                  outcome.cstate
                                  funenv
                                  (1- limit)))
            ((when (mode-case outcome.mode :break))
             (reserrf (list :break-from-for (statement-fix stmt))))
            ((when (mode-case outcome.mode :continue))
             (reserrf (list :continue-from-for (statement-fix stmt))))
            (cstate (restrict-vars vars-before outcome.cstate)))
         (make-soutcome :cstate cstate :mode outcome.mode))
       :switch
       (b* (((okf (eoutcome outcome))
             (exec-expression stmt.target cstate funenv (1- limit)))
            ((unless (equal (len outcome.values) 1))
             (reserrf (list :not-single-value outcome.values))))
         (exec-switch-rest stmt.cases
                           stmt.default
                           (car outcome.values)
                           outcome.cstate
                           funenv
                           (1- limit)))
       :leave (make-soutcome :cstate (cstate-fix cstate)
                             :mode (mode-leave))
       :break (make-soutcome :cstate (cstate-fix cstate)
                             :mode (mode-break))
       :continue (make-soutcome :cstate (cstate-fix cstate)
                                :mode (mode-continue))
       :fundef (make-soutcome :cstate (cstate-fix cstate)
                              :mode (mode-regular))))
    :measure (nfix limit))

  (define exec-statement-list ((stmts statement-listp)
                               (cstate cstatep)
                               (funenv funenvp)
                               (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute a list of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "The statements are executed one after the other,
       threading the computation state through.
       As soon as a statement terminates non-regularly,
       we stop executing the statements and return that non-regular mode.
       Otherwise, the statement list is executed to completion regularly."))
    (b* (((when (zp limit)) (reserrf (list :limit (statement-list-fix stmts))))
         ((when (endp stmts)) (make-soutcome :cstate (cstate-fix cstate)
                                             :mode (mode-regular)))
         ((okf (soutcome outcome))
          (exec-statement (car stmts) cstate funenv (1- limit)))
         ((unless (mode-case outcome.mode :regular)) outcome))
      (exec-statement-list (cdr stmts) outcome.cstate funenv (1- limit)))
    :measure (nfix limit))

  (define exec-block ((block blockp)
                      (cstate cstatep)
                      (funenv funenvp)
                      (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute a block."
    :long
    (xdoc::topstring
     (xdoc::p
      "We save (the names of) the variables just before the block,
       so that we can restrict the computation state after the block
       to only those variables, as explained in @(tsee restrict-vars).
       We extend the function environment with the functions in the block.
       We execute the block's statements.
       We return the resulting outcome,
       but we remove all the variables added by the block."))
    (b* (((when (zp limit)) (reserrf (list :limit (block-fix block))))
         (vars-before (omap::keys (cstate->local cstate)))
         (stmts (block->statements block))
         ((okf funenv) (add-funs (statements-to-fundefs stmts) funenv))
         ((okf (soutcome outcome))
          (exec-statement-list stmts cstate funenv (1- limit)))
         (cstate (restrict-vars vars-before outcome.cstate)))
      (make-soutcome :cstate cstate :mode outcome.mode))
    :measure (nfix limit))

  (define exec-for-iterations ((test expressionp)
                               (update blockp)
                               (body blockp)
                               (cstate cstatep)
                               (funenv funenvp)
                               (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute the iterations of a loop statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "We execute the test, ensuring it returns one value.
       As also explained for @('if') (see @(tsee exec-statement)),
       we consider 0 to be false and any non-0 value to be true.")
     (xdoc::p
      "If the test is false, we terminate regularly.")
     (xdoc::p
      "If the test is true, we first execute the body.
       If it terminates with @('break'),
       we turn that into a regular termination:
       we break out of the loop gracefully, no more iterations will happen.
       If the body terminates with @('leave'),
       we terminate in the same way.
       If the body terminates with @('continue') or regularly,
       we continue the iteration,
       by executing the update block.
       If the update block terminates with @('leave'),
       we terminate the loop in the same way.
       If the update block terminates with @('break') or @('continue'),
       we defensively return an error.
       If the update block terminates regularly,
       we recursively call this ACL2 function,
       to continue iterating."))
    (b* (((when (zp limit)) (reserrf (list :limit
                                           (expression-fix test)
                                           (block-fix update)
                                           (block-fix body))))
         ((okf (eoutcome outcome))
          (exec-expression test cstate funenv (1- limit)))
         ((unless (equal (len outcome.values) 1))
          (reserrf (list :for-test-not-single-value outcome.values)))
         ((when (equal (car outcome.values) (value 0)))
          (make-soutcome :cstate outcome.cstate :mode (mode-regular)))
         ((okf (soutcome outcome))
          (exec-block body outcome.cstate funenv (1- limit)))
         ((when (mode-case outcome.mode :break))
          (make-soutcome :cstate outcome.cstate :mode (mode-regular)))
         ((when (mode-case outcome.mode :leave))
          (make-soutcome :cstate outcome.cstate :mode outcome.mode))
         ((okf (soutcome outcome))
          (exec-block update outcome.cstate funenv (1- limit)))
         ((when (mode-case outcome.mode :break))
          (reserrf (list :break-from-for-update (block-fix update))))
         ((when (mode-case outcome.mode :continue))
          (reserrf (list :continue-from-for-update (block-fix update))))
         ((when (mode-case outcome.mode :leave))
          (make-soutcome :cstate outcome.cstate :mode outcome.mode)))
      (exec-for-iterations test update body outcome.cstate funenv (1- limit)))
    :measure (nfix limit))

  (define exec-switch-rest ((cases swcase-listp)
                            (default block-optionp)
                            (target valuep)
                            (cstate cstatep)
                            (funenv funenvp)
                            (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute the rest of a switch statement,
            after evaluating the target."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through the cases, until we find a match,
       in which case we return the result of executing the corresponding block.
       If we reach the end of the list,
       we execute the default block, if present.
       If the default block is absent, we terminate regularly."))
    (b* (((when (zp limit)) (reserrf (list :limit
                                           (swcase-list-fix cases)
                                           (block-option-fix default))))
         ((when (endp cases))
          (block-option-case
           default
           :some (exec-block default.val cstate funenv (1- limit))
           :none (make-soutcome :cstate (cstate-fix cstate)
                                :mode (mode-regular))))
         ((swcase case) (car cases))
         ((okf caseval) (eval-literal case.value))
         ((when (value-equiv target caseval))
          (exec-block case.body cstate funenv (1- limit))))
      (exec-switch-rest (cdr cases) default target cstate funenv (1- limit)))
    :measure (nfix limit))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards exec-expression)

  (fty::deffixequiv-mutual exec)

  (std::defret-mutual error-info-wfp-of-exec
    (defret error-info-wfp-of-exec-expression
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-expression)
    (defret error-info-wfp-of-exec-expression-list
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-expression-list)
    (defret error-info-wfp-of-exec-funcall
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-funcall)
    (defret error-info-wfp-of-exec-function
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-function)
    (defret error-info-wfp-of-exec-statement
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-statement)
    (defret error-info-wfp-of-exec-statement-list
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-statement-list)
    (defret error-info-wfp-of-exec-block
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-block)
    (defret error-info-wfp-of-exec-for-iterations
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-for-iterations)
    (defret error-info-wfp-of-exec-switch-rest
      (implies (reserrp outcome)
               (error-info-wfp outcome))
      :fn exec-switch-rest)
    :hints (("Goal" :in-theory (enable not-reserrp-when-soutcomep
                                       not-reserrp-when-eoutcomep
                                       exec-expression
                                       exec-expression-list
                                       exec-funcall
                                       exec-function
                                       exec-statement
                                       exec-statement-list
                                       exec-block
                                       exec-for-iterations
                                       exec-switch-rest))))

  (defruled statement-kind-when-mode-regular
    (b* ((outcome (exec-statement stmt cstate funenv limit)))
      (implies (and (soutcomep outcome)
                    (mode-case (soutcome->mode outcome) :regular))
               (and (not (equal (statement-kind stmt) :leave))
                    (not (equal (statement-kind stmt) :break))
                    (not (equal (statement-kind stmt) :continue)))))
    :enable exec-statement))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-top-block ((block blockp) (limit natp))
  :returns (cstate cstate-resultp)
  :short "Execute the top block."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for the top-level block.
     Starting with the empty computation state
     and the empty function environment,
     we execute the block, propagating errors.
     Since the top-level block is not inside a function or loop,
     we defensively check that the execution terminates regularly,
     returning an error if it does not.
     In case of success, we return the final computation state."))
  (b* ((cstate (make-cstate :local nil))
       (funenv nil)
       ((okf (soutcome outcome)) (exec-block block cstate funenv limit))
       ((unless (equal outcome.mode (mode-regular)))
        (reserrf (list :top-block-move outcome.mode))))
    outcome.cstate)
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-exec-top-block
    (implies (reserrp cstate)
             (error-info-wfp cstate))))
