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
  :parents (yul)
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

(define exec-path ((path pathp) (cstate cstatep))
  :returns (outcome eoutcome-resultp)
  :short "Execute a path."
  :long
  (xdoc::topstring
   (xdoc::p
    "To execute a path, we require, as in the static semantics,
     the path to consist of a single identifier.
     We look up the variable in the computation state.
     This always returns a single value,
     and does not change the computation state."))
  (b* ((idens (path->get path))
       ((unless (consp idens))
        (err (list :empty-path (path-fix path))))
       ((unless (endp (cdr idens)))
        (err (list :non-singleton-path (path-fix path))))
       (var (car idens))
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
         ((ok outcome) (exec-expression (car exprs) cstate (1- limit)))
         (cstate (eoutcome->cstate outcome))
         (vals (eoutcome->values outcome))
         ((unless (and (consp vals) (endp (cdr vals))))
          (err (list :not-single-value vals)))
         (val (car vals))
         ((ok outcome) (exec-expression-list (cdr exprs) cstate (1- limit)))
         (cstate (eoutcome->cstate outcome))
         (vals (eoutcome->values outcome)))
      (make-eoutcome :cstate cstate :values (cons val vals)))
    :measure (nfix limit))

  (define exec-funcall ((call funcallp) (cstate cstatep) (limit natp))
    :returns (outcome eoutcome-resultp)
    :short "Execute a function call."
    :long
    (xdoc::topstring
     (xdoc::p
      "We evaluate the argument expressions,
       and then we delegate the rest to @(tsee exec-function)."))
    (b* (((when (zp limit)) (err (list :limit (funcall-fix call))))
         ((funcall call) call)
         ((ok outcome) (exec-expression-list call.args cstate (1- limit)))
         (cstate (eoutcome->cstate outcome))
         (vals (eoutcome->values outcome)))
      (exec-function call.name vals cstate (1- limit)))
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
       We also restore the computation state prior to the function call."))
    (b* (((when (zp limit)) (err (list :limit
                                   (identifier-fix fun)
                                   (value-list-fix args))))
         ((ok (funinfo info)) (get-fun fun cstate))
         ((ok cstate1) (init-local info.inputs args info.outputs cstate))
         ((ok cstate1) (exec-block info.body cstate1 (1- limit)))
         ((ok vals) (read-vars-values info.outputs cstate1)))
      (make-eoutcome :cstate (cstate-fix cstate) :values vals))
    :measure (nfix limit))

  (define exec-statement ((stmt statementp) (cstate cstatep) (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "A @('leave'), @('break'), or @('continue') statement
       leaves the computation state unchanged
       and returns the corresponding mode.")
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
       :block (err :todo)
       :variable-single (err :todo)
       :variable-multi (err :todo)
       :assign-single (err :todo)
       :assign-multi (err :todo)
       :funcall (err :todo)
       :if (err :todo)
       :for (err :todo)
       :switch (err :todo)
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
         ((ok outcome) (exec-statement (car stmts) cstate (1- limit)))
         (mode (soutcome->mode outcome))
         ((unless (mode-case mode :regular)) outcome)
         (cstate (soutcome->cstate outcome)))
      (exec-statement-list (cdr stmts) cstate (1- limit)))
    :measure (nfix limit))

  (define exec-block ((block blockp) (cstate cstatep) (limit natp))
    :returns (outcome soutcome-resultp)
    :short "Execute a block."
    (b* (((when (zp limit)) (err (list :limit (block-fix block)))))
      (err (list :todo (cstate-fix cstate))))
    :measure (nfix limit))

  ;; exec-swcase

  ;; exec-swcase-list

  :prepwork ((set-bogus-mutual-recursion-ok t)) ; TODO: remove

  :verify-guards nil ; done below
  ///
  (verify-guards exec-expression)

  (fty::deffixequiv-mutual exec))
