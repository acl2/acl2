; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")
(include-book "literal-evaluation")

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
     via execution of the Yul abstract syntax.")
   (xdoc::p
    "This is based on the formal specification in
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
  :pred lstatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule lstatep-of-restrict
  (implies (lstatep map)
           (lstatep (omap::restrict keys map)))
  :enable omap::restrict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule identifier-setp-of-keys-when-lstatep
  (implies (lstatep map)
           (identifier-setp (omap::keys map)))
  :enable omap::keys)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funinfo
  :short "Fixtype of function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is all the information about a function definition,
     except for its name.
     This is used for the values of function states (see @(tsee fstate)."))
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

(fty::defomap fstate
  :short "Fixtype of function states."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a finite map from identifiers (function names)
     to function information:
     it models the function definitions currently in scope;
     this changes as blocks are entered and exited.
     [Yul: Specification of Yul: Formal Specification]
     does not explicitly mention this,
     but its presence is implicit in the description of
     the scope of function definitions."))
  :key-type identifier
  :val-type funinfo
  :pred fstatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cstate
  :short "Fixtype of computational states."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     this consists of a local state object and a global state object.
     The latter is generic in generic Yul.
     For now, for simplicity, we ignore the global state completely,
     but we plan to add that at some point.
     We also include the function state,
     whose motivation is discussed in @(tsee fstate)."))
  ((local lstate)
   (functions fstate))
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
       (var-val (omap::in (identifier-fix var) lstate))
       ((unless (consp var-val))
        (err (list :variable-not-found (identifier-fix var)))))
    (value-fix (cdr var-val)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-vars-values ((vars identifier-listp) (cstate cstatep))
  :returns (vals
            value-list-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               valuep-when-value-resultp-and-not-resulterrp
               value-listp-when-value-list-resultp-and-not-resulterrp))))
  :short "Lift @(tsee read-var-value) to lists."
  (b* (((when (endp vars)) nil)
       ((ok val) (read-var-value (car vars) cstate))
       ((ok vals) (read-vars-values (cdr vars) cstate)))
    (cons val vals))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-var-value ((var identifierp) (val valuep) (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Write a variable value to the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the variable does not exist."))
  (b* ((lstate (cstate->local cstate))
       (var-val (omap::in (identifier-fix var) lstate))
       ((unless (consp var-val))
        (err (list :variable-not-found (identifier-fix var))))
       (new-lstate (omap::update (identifier-fix var)
                                 (value-fix val)
                                 lstate))
       (new-cstate (change-cstate cstate :local new-lstate)))
    new-cstate)
  :hooks (:fix))

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
          (err (list :extra-values (value-list-fix vals)))))
       ((when (endp vals))
        (err (list :extra-variables (identifier-list-fix vars))))
       ((ok cstate) (write-var-value (car vars) (car vals) cstate)))
    (write-vars-values (cdr vars) (cdr vals) cstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var-value ((var identifierp) (val valuep) (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Add a variable with a value to the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the variable already exists."))
  (b* ((lstate (cstate->local cstate))
       (var-val (omap::in (identifier-fix var) lstate))
       ((when (consp var-val))
        (err (list :variable-already-exists (identifier-fix var))))
       (new-lstate (omap::update (identifier-fix var)
                                 (value-fix val)
                                 lstate))
       (new-cstate (change-cstate cstate :local new-lstate)))
    new-cstate)
  :hooks (:fix))

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
          (err (list :extra-values (value-list-fix vals)))))
       ((when (endp vals))
        (err (list :extra-variables (identifier-list-fix vars))))
       ((ok cstate) (add-var-value (car vars) (car vals) cstate)))
    (add-vars-values (cdr vars) (cdr vals) cstate))
  :hooks (:fix))

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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-fun ((fun identifierp) (cstate cstatep))
  :returns (info funinfo-resultp)
  :short "Obtain information about a function from the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is an error if the function does not exist."))
  (b* ((fstate (cstate->functions cstate))
       (fun-info (omap::in (identifier-fix fun) fstate))
       ((unless (consp fun-info))
        (err (list :function-not-found (identifier-fix fun)))))
    (cdr fun-info))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-fun ((fun identifierp) (info funinfop) (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Add a function to the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "An error is returned if the function already exists.")
   (xdoc::p
    "This is the dynamic counterpart of
     @(tsee add-funtype) in the static semantics."))
  (b* ((fstate (cstate->functions cstate))
       (fun-info (omap::in (identifier-fix fun) fstate))
       ((when (consp fun-info))
        (err (list :function-already-exists (identifier-fix fun))))
       (new-fstate
        (omap::update (identifier-fix fun) (funinfo-fix info) fstate))
       (new-cstate (change-cstate cstate :functions new-fstate)))
    new-cstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-funs-in-statement-list ((stmts statement-listp) (cstate cstatep))
  :returns (new-cstate cstate-resultp)
  :short "Add all the functions in a block to the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Just before executing a block,
     all the function definitions in the block
     are added to computation states.
     This is because,
     as explained in [Yul: Specification of Yul: Scoping Rules],
     all the functions defined in a block are accessible in the whole block,
     even before they are defined in the block.")
   (xdoc::p
    "This is the dynamic counterpart of
     @(tsee add-funtypes-in-statement-list) in the static semantics."))
  (b* (((when (endp stmts)) (cstate-fix cstate))
       (stmt (car stmts))
       ((unless (statement-case stmt :fundef))
        (add-funs-in-statement-list (cdr stmts) cstate))
       ((fundef fundef) (statement-fundef->get stmt))
       ((ok cstate) (add-fun fundef.name
                             (make-funinfo :inputs fundef.inputs
                                           :outputs fundef.outputs
                                           :body fundef.body)
                             cstate)))
    (add-funs-in-statement-list (cdr stmts) cstate))
  :hooks (:fix))

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
     the input and output variables of the fucntion,
     which are passed as the @('in-vars') and @('out-vars') parameters.
     The input variables are initialized with the input values,
     passed as the @('in-vals') parameters;
     note that we implicitly check that the number of input variables
     matches the number of input values.
     The output variables are initialized to 0."))
  (b* ((cstate (change-cstate cstate :local nil))
       ((ok cstate) (add-vars-values in-vars in-vals cstate))
       ((ok cstate) (add-vars-values out-vars
                                     (repeat (len out-vars) (value 0))
                                     cstate)))
    cstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum mode
  :short "Fixtype of modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification] introduces
     the notion of mode, which indicates how a statement completes execution."))
  (:regular ())
  (:break ())
  (:continue ())
  (:leave ())
  :pred modep)

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
        (err (list :empty-path (path-fix path))))
       ((unless (endp (cdr idens)))
        (err (list :non-singleton-path (path-fix path))))
       (var (car idens)))
    var)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define paths-to-vars ((paths path-listp))
  :returns
  (vars
   identifier-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      identifierp-when-identifier-resultp-and-not-resulterrp
      identifier-listp-when-identifier-list-resultp-and-not-resulterrp))))
  :short "Extract variables from paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee path-to-var) to lists."))
  (b* (((when (endp paths)) nil)
       ((ok var) (path-to-var (car paths)))
       ((ok vars) (paths-to-vars (cdr paths))))
    (cons var vars))
  :hooks (:fix)
  ///

  (defret len-of-paths-to-vars
    (implies (not (resulterrp vars))
             (equal (len vars)
                    (len paths)))))

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
  (b* (((ok var) (path-to-var path))
       ((ok val) (read-var-value var cstate)))
    (make-eoutcome :cstate cstate :values (list val)))
  :hooks (:fix))

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
  (b* (((ok val) (eval-literal lit)))
    (make-eoutcome :cstate cstate :values (list val)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec
  :short "Mutually recursive execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Executing expressions involves executing function calls,
     which involves executing the statements in function bodies,
     which involves executing the expressions in the statements."))

  (define exec-expression ((expr expressionp) (cstate cstatep) (limit natp))
    :returns (outcome eoutcome-resultp)
    :short "Execute an expression."
    (b* (((when (zp limit)) (err (list :limit (expression-fix expr)))))
      (expression-case
       expr
       :path (exec-path expr.get cstate)
       :literal (exec-literal expr.get cstate)
       :funcall (exec-funcall expr.get cstate (1- limit))))
    :measure (nfix limit))

  (define exec-expression-list ((exprs expression-listp)
                                (cstate cstatep)
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
    (b* (((when (zp limit)) (err (list :limit (expression-list-fix exprs))))
         ((when (endp exprs)) (make-eoutcome :cstate (cstate-fix cstate)
                                             :values nil))
         ((ok (eoutcome outcome))
          (exec-expression (car exprs) cstate (1- limit)))
         ((unless (and (consp outcome.values)
                       (endp (cdr outcome.values))))
          (err (list :not-single-value outcome.values)))
         (val (car outcome.values))
         ((ok (eoutcome outcome))
          (exec-expression-list (cdr exprs) outcome.cstate (1- limit))))
      (make-eoutcome :cstate outcome.cstate :values (cons val outcome.values)))
    :measure (nfix limit))

  (define exec-funcall ((call funcallp) (cstate cstatep) (limit natp))
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
    (b* (((when (zp limit)) (err (list :limit (funcall-fix call))))
         ((funcall call) call)
         ((ok (eoutcome outcome))
          (exec-expression-list (rev call.args) cstate (1- limit))))
      (exec-function call.name outcome.values outcome.cstate (1- limit)))
    :measure (nfix limit))

  (define exec-function ((fun identifierp)
                         (args value-listp)
                         (cstate cstatep)
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
      "We initialize the local state with the function's inputs and outputs.
       We run the function body on the resulting computation state.
       We read the final values of the function output variables
       and return them as result.
       We also restore the computation state prior to the function call.")
     (xdoc::p
      "As a defensive check, we ensure that the function's body
       terminates regularly or via @('leave'),
       not via @('break') or @('continue')."))
    (b* (((when (zp limit)) (err (list :limit
                                   (identifier-fix fun)
                                   (value-list-fix args))))
         ((ok (funinfo info)) (get-fun fun cstate))
         ((ok cstate1) (init-local info.inputs args info.outputs cstate))
         ((ok (soutcome outcome))
          (exec-block info.body cstate1 (1- limit)))
         ((when (mode-case outcome.mode :break))
          (err (list :break-from-function (identifier-fix fun))))
         ((when (mode-case outcome.mode :continue))
          (err (list :continue-from-function (identifier-fix fun))))
         ((ok vals) (read-vars-values info.outputs outcome.cstate)))
      (make-eoutcome :cstate (cstate-fix cstate) :values vals))
    :measure (nfix limit))

  (define exec-statement ((stmt statementp) (cstate cstatep) (limit natp))
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
       similarly to @(tsee exec-block);
       we also save the fucntion sate, similarly to @(tsee exec-block).
       The initialization block of a loop statement
       is not treated like other blocks:
       its scope extends to the rest of the loop statement.
       Thus, instead of executing the initialization block as a block,
       we take the statements in the block,
       extend the function state with any function declared there,
       and execute the statements,
       which may result in new and updated variables.
       We defensively stop with an error if the initialization block
       terminates with @('break') or @('continue');
       if it termnates with @('leave'), we also terminate with @('leave'),
       removing extra variables and restoring the function state.
       We delegate the execution of the loop iterations
       to another ACL2 function.
       We take the result of that ACL2 function,
       restore the function state
       (similarly to @(tsee exec-block),
       and remove the variables added by the loop
       (similarly to @(tsee exec-block)).")
     (xdoc::p
      "A function definition
       does not change the computation state
       and terminates regularly.
       It is like a no-op when it is encountered as a statement.
       The function definitions in a block
       are incorporated into the function state of the computation state
       prior to starting to execute the statements in the block."))
    (b* (((when (zp limit)) (err (list :limit (statement-fix stmt)))))
      (statement-case
       stmt
       :block (exec-block stmt.get cstate (1- limit))
       :variable-single
       (expression-option-case
        stmt.init
        :some
        (b* (((ok (eoutcome outcome))
              (exec-expression stmt.init.val cstate (1- limit)))
             ((unless (and (consp outcome.values)
                           (not (consp (cdr outcome.values)))))
              (err (list :not-single-value outcome.values)))
             ((ok cstate)
              (add-var-value stmt.name (car outcome.values) outcome.cstate)))
          (make-soutcome :cstate cstate :mode (mode-regular)))
        :none
        (b* (((ok cstate) (add-var-value stmt.name (value 0) cstate)))
          (make-soutcome :cstate cstate :mode (mode-regular))))
       :variable-multi
       (if (>= (len stmt.names) 2)
           (funcall-option-case
            stmt.init
            :some
            (b* (((ok (eoutcome outcome))
                  (exec-funcall stmt.init.val cstate (1- limit)))
                 ((ok cstate)
                  (add-vars-values stmt.names outcome.values outcome.cstate)))
              (make-soutcome :cstate cstate :mode (mode-regular)))
            :none
            (b* (((ok cstate) (add-vars-values stmt.names
                                               (repeat (len stmt.names)
                                                       (value 0))
                                               cstate)))
              (make-soutcome :cstate cstate :mode (mode-regular))))
         (err (list :non-multiple-variables stmt.names)))
       :assign-single
       (b* (((ok var) (path-to-var stmt.target))
            ((ok (eoutcome outcome))
             (exec-expression stmt.value cstate (1- limit)))
            ((unless (and (consp outcome.values)
                          (not (consp (cdr outcome.values)))))
             (err (list :not-single-value outcome.values)))
            ((ok cstate)
             (write-var-value var (car outcome.values) outcome.cstate)))
         (make-soutcome :cstate cstate :mode (mode-regular)))
       :assign-multi
       (b* (((unless (>= (len stmt.targets) 2))
             (err (list :non-multiple-variables stmt.targets)))
            ((ok vars) (paths-to-vars stmt.targets))
            ((ok (eoutcome outcome))
             (exec-funcall stmt.value cstate (1- limit)))
            ((ok cstate)
             (write-vars-values vars outcome.values outcome.cstate)))
         (make-soutcome :cstate cstate :mode (mode-regular)))
       :funcall
       (b* (((ok (eoutcome outcome))
             (exec-funcall stmt.get cstate (1- limit)))
            ((when (consp outcome.values))
             (err (list :funcall-statement-returns outcome.values))))
         (make-soutcome :cstate outcome.cstate :mode (mode-regular)))
       :if
       (b* (((ok (eoutcome outcome))
             (exec-expression stmt.test cstate (1- limit)))
            ((unless (and (consp outcome.values)
                          (not (consp (cdr outcome.values)))))
             (err (list :if-test-not-single-value outcome.values)))
            (val (car outcome.values)))
         (if (equal val (value 0))
             (make-soutcome :cstate outcome.cstate :mode (mode-regular))
           (exec-block stmt.body outcome.cstate (1- limit))))
       :for
       (b* ((vars-before (omap::keys (cstate->local cstate)))
            (fstate-before (cstate->functions cstate))
            (stmts (block->statements stmt.init))
            ((ok cstate) (add-funs-in-statement-list stmts cstate))
            ((ok (soutcome outcome))
             (exec-statement-list stmts cstate (1- limit)))
            ((when (mode-case outcome.mode :break))
             (err (list :break-from-for-init (statement-fix stmt))))
            ((when (mode-case outcome.mode :continue))
             (err (list :continue-from-for-init (statement-fix stmt))))
            ((when (mode-case outcome.mode :leave))
             (b* ((cstate (change-cstate outcome.cstate
                                         :functions fstate-before))
                  (cstate (restrict-vars vars-before cstate)))
               (make-soutcome :cstate cstate :mode (mode-leave))))
            ((ok (soutcome outcome))
             (exec-for-iterations stmt.test
                                  stmt.update
                                  stmt.body
                                  cstate
                                  (1- limit)))
            ((when (mode-case outcome.mode :break))
             (err (list :break-from-for (statement-fix stmt))))
            ((when (mode-case outcome.mode :continue))
             (err (list :continue-from-for (statement-fix stmt))))
            (cstate (change-cstate outcome.cstate
                                   :functions fstate-before))
            (cstate (restrict-vars vars-before cstate)))
         (make-soutcome :cstate cstate :mode outcome.mode))
       :switch
       (b* (((ok (eoutcome outcome))
             (exec-expression stmt.target cstate (1- limit)))
            ((unless (and (consp outcome.values)
                          (not (consp (cdr outcome.values)))))
             (err (list :not-single-value outcome.values))))
         (exec-switch-rest stmt.cases
                           stmt.default
                           (car outcome.values)
                           outcome.cstate
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
    (b* (((when (zp limit)) (err (list :limit (statement-list-fix stmts))))
         ((when (endp stmts)) (make-soutcome :cstate (cstate-fix cstate)
                                             :mode (mode-regular)))
         ((ok (soutcome outcome))
          (exec-statement (car stmts) cstate (1- limit)))
         ((unless (mode-case outcome.mode :regular)) outcome))
      (exec-statement-list (cdr stmts) outcome.cstate (1- limit)))
    :measure (nfix limit))

  (define exec-block ((block blockp) (cstate cstatep) (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute a block."
    :long
    (xdoc::topstring
     (xdoc::p
      "We save (the names of) the variables just before the block,
       so that we can restrict the computation state after the block
       to only those variables, as explained in @(tsee restrict-vars).
       We also save the function state before the block,
       because we need to restore that after the block.
       We extend the function state with the functions in the block.
       We execute the block's statements.
       We return the resulting outcome,
       but we restore the function state before the block
       and we remove all the variables added by the block."))
    (b* (((when (zp limit)) (err (list :limit (block-fix block))))
         (vars-before (omap::keys (cstate->local cstate)))
         (fstate-before (cstate->functions cstate))
         (stmts (block->statements block))
         ((ok cstate) (add-funs-in-statement-list stmts cstate))
         ((ok (soutcome outcome))
          (exec-statement-list stmts cstate (1- limit)))
         (cstate (change-cstate outcome.cstate :functions fstate-before))
         (cstate (restrict-vars vars-before cstate)))
      (make-soutcome :cstate cstate :mode outcome.mode))
    :measure (nfix limit))

  (define exec-for-iterations ((test expressionp)
                               (update blockp)
                               (body blockp)
                               (cstate cstatep)
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
    (b* (((when (zp limit)) (err (list :limit
                                   (expression-fix test)
                                   (block-fix update)
                                   (block-fix body))))
         ((ok (eoutcome outcome))
          (exec-expression test cstate (1- limit)))
         ((unless (and (consp outcome.values)
                       (not (consp (cdr outcome.values)))))
          (err (list :for-test-not-single-value outcome.values)))
         ((when (equal (car outcome.values) (value 0)))
          (make-soutcome :cstate outcome.cstate :mode (mode-regular)))
         ((ok (soutcome outcome))
          (exec-block body outcome.cstate (1- limit)))
         ((when (mode-case outcome.mode :break))
          (make-soutcome :cstate outcome.cstate :mode (mode-regular)))
         ((when (mode-case outcome.mode :leave))
          (make-soutcome :cstate outcome.cstate :mode outcome.mode))
         ((ok (soutcome outcome))
          (exec-block update outcome.cstate (1- limit)))
         ((when (mode-case outcome.mode :break))
          (err (list :break-from-for-update (block-fix update))))
         ((when (mode-case outcome.mode :continue))
          (err (list :continue-from-for-update (block-fix update))))
         ((when (mode-case outcome.mode :leave))
          (make-soutcome :cstate outcome.cstate :mode outcome.mode)))
      (exec-for-iterations test update body outcome.cstate (1- limit)))
    :measure (nfix limit))

  (define exec-switch-rest ((cases swcase-listp)
                            (default block-optionp)
                            (target valuep)
                            (cstate cstatep)
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
    (b* (((when (zp limit)) (err (list :limit
                                   (swcase-list-fix cases)
                                   (block-option-fix default))))
         ((when (endp cases))
          (block-option-case default
                             :some (exec-block default.val cstate (1- limit))
                             :none (make-soutcome :cstate (cstate-fix cstate)
                                                  :mode (mode-regular))))
         ((swcase case) (car cases))
         ((ok caseval) (eval-literal case.value))
         ((when (value-equiv target caseval))
          (exec-block case.body cstate (1- limit))))
      (exec-switch-rest (cdr cases) default target cstate (1- limit)))
    :measure (nfix limit))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards exec-expression)

  (fty::deffixequiv-mutual exec))
