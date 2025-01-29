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

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/nat-result" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-safety-checking
  :parents (static-semantics)
  :short "Static safety checking of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is (the main) part of the Yul static semantics.
     It consists of checks that ensure the safety of execution,
     i.e. that certain situations never happen during execution,
     such as reading or writing a non-existent variable.
     Our formal "
    (xdoc::seetopic "dynamic-semantics" "dynamic semantics")
    " of Yul defensively checks these conditions,
     returning error values when the conditions are not satisfied.
     The static safety checks formalized here
     ensure that those error values are never returned by the dynamic semantics,
     as proved in @(see static-soundness).")
   (xdoc::p
    "The static safety of the Yul constructs is checked with respect to
     (i) a set of variable names (identifiers) and
     (ii) an omap from function names (identifiers)
     to function input/output information.
     These are essentially symbol tables for variables and functions:
     they describe the variables and functions in scope.")
   (xdoc::p
    "These symbol tables for variables consists of
     the variables that are not only visible, but also accessible,
     according to [Yul: Specification of Yul: Scoping Rules]:
     a variable is visible in the rest of the block in which it is declared,
     including sub-blocks,
     but it is not accessible in
     function definitions in the block or sub-blocks.
     Variables that are visible but inaccessible
     are not represented in these symbol tables for variables.")
   (xdoc::p
    "The Yul static semantics requires that
     visible but inaccessible variables are not shadowed
     [Yul: Specification of Yul: Scoping Rules].
     However, this requirement is not needed for safety,
     as evidenced by the fact that
     the static soundness proof in @(see static-soundness)
     does not make use of that requirement.
     In fact, we do not include that requirement in the static safety checks
     formalized here.
     This requirement is formalized separately
     in @(see static-shadowing-checking)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funtype
  :short "Fixtype of function types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given that for now we do not model any types,
     the notion of ``type'' of a function
     boils down to its number of inputs and number of outputs."))
  ((in nat)
   (out nat))
  :tag :funtype
  :pred funtypep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funtype-result
  :short "Fixtype of errors and function types."
  :ok funtype
  :pred funtype-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap funtable
  :short "Fixtype of function tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are symbol tables for functions.
     A table is a finite map from function names (identifiers)
     to function types (as defined above)."))
  :key-type identifier
  :val-type funtype
  :pred funtablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funtable-result
  :short "Fixtype of errors and function tables."
  :ok funtable
  :pred funtable-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-funtype ((name identifierp) (funtab funtablep))
  :returns (funty? funtype-resultp)
  :short "Look up a function in a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lookup is by name.
     If a function is found, we return its type.
     Otherwise we return an error."))
  (b* ((pair (omap::assoc (identifier-fix name) (funtable-fix funtab))))
    (if (consp pair)
        (cdr pair)
      (reserrf (list :function-not-found (identifier-fix name)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funtype-for-fundef ((fundef fundefp))
  :returns (funtype funtypep)
  :short "Function type for a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just the number of inputs and outputs of the function."))
  (make-funtype :in (len (fundef->inputs fundef))
                :out (len (fundef->outputs fundef)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funtable-for-fundefs ((fundefs fundef-listp))
  :returns (funtab funtable-resultp)
  :short "Function table for a list of function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the list and form a function table for the functions.
     It is an error if there are two functions with the same name."))
  (b* (((when (endp fundefs)) nil)
       ((okf funtab) (funtable-for-fundefs (cdr fundefs)))
       (fundef (car fundefs))
       (fun (fundef->name fundef))
       ((when (consp (omap::assoc fun funtab)))
        (reserrf (list :duplicate-function fun))))
    (omap::update fun (funtype-for-fundef fundef) funtab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-funtypes ((fundefs fundef-listp) (funtab funtablep))
  :returns (new-funtab funtable-resultp)
  :short "Add functions to a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first construct a function table for the function definitions,
     and then we use that to update the given function table,
     ensuring that the two tables have disjoint functions."))
  (b* ((funtab (funtable-fix funtab))
       ((okf funtab1) (funtable-for-fundefs fundefs))
       (overlap (set::intersect (omap::keys funtab1)
                                (omap::keys funtab)))
       ((unless (set::emptyp overlap))
        (reserrf (list :duplicate-functions overlap))))
    (omap::update* funtab1 funtab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-var ((var identifierp) (varset identifier-setp))
  :returns (yes/no booleanp)
  :short "Check if a variable is in a variable table."
  (set::in (identifier-fix var) (identifier-set-fix varset))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var ((var identifierp) (varset identifier-setp))
  :returns (varset? identifier-set-resultp)
  :short "Add a variable to a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a variable with the same name is already in the table,
     an error is returned.")
   (xdoc::p
    "If this function does not return an error,
     it is equivalent to @(tsee set::insert)."))
  (b* ((var (identifier-fix var))
       (varset (identifier-set-fix varset)))
    (if (set::in var varset)
        (reserrf (list :duplicate-variable var))
      (set::insert var varset)))
  :hooks (:fix)
  ///

  (defruled add-var-to-set-insert
    (b* ((varset1 (add-var var varset)))
      (implies (not (reserrp varset1))
               (equal varset1
                      (set::insert (identifier-fix var)
                                   (identifier-set-fix varset)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-vars ((vars identifier-listp)
                  (varset identifier-setp))
  :returns (varset? identifier-set-resultp)
  :short "Add (a list of) variables to a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are added, one after the other.
     Duplicates in the list will cause an error.")
   (xdoc::p
    "This lifts @(tsee add-var) to lists.")
   (xdoc::p
    "If this function does not return an error,
     it is equivalent to @('set::list-insert')."))
  (b* (((when (endp vars)) (identifier-set-fix varset))
       ((okf varset) (add-var (car vars) varset)))
    (add-vars (cdr vars) varset))
  :hooks (:fix)
  ///

  (defruled add-vars-to-set-list-insert
    (b* ((varset1 (add-vars vars varset)))
      (implies (not (reserrp varset1))
               (equal varset1
                      (set::list-insert (identifier-list-fix vars)
                                        (identifier-set-fix varset)))))
    :enable (set::list-insert
             add-var-to-set-insert)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-path ((path pathp) (varset identifier-setp))
  :returns (_ reserr-optionp)
  :short "Check if a path is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "As a structural condition,
     a path must consists of one or more identifiers.
     More importantly, it must refer to an existing variable.
     It is not yet clear how paths with more than one identifier
     come about in generic Yul:
     variable declarations are for single identifiers
     (whether one single identifier,
     or two or more single identifiers),
     so it seems that singleton paths would always suffice to reference them
     in expressions and statements.
     For now we only regard singleton paths as safe,
     provided they are part of the accessible variables.")
   (xdoc::p
    "We may move the non-emptiness requirement
     into an invariant of @(tsee path),
     but for now we state it as part of the static semantics."))
  (b* ((idens (path->get path))
       ((unless (consp idens))
        (reserrf (list :empty-path (path-fix path))))
       ((unless (endp (cdr idens)))
        (reserrf (list :non-singleton-path (path-fix path))))
       (var (car idens))
       ((unless (check-var var varset))
        (reserrf (list :variable-not-found var))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-path-list ((paths path-listp) (varset identifier-setp))
  :returns (_ reserr-optionp)
  :short "Check if a list of paths is safe."
  (b* (((when (endp paths)) nil)
       ((okf &) (check-safe-path (car paths) varset)))
    (check-safe-path-list (cdr paths) varset))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-literal ((lit literalp))
  :returns (_ reserr-optionp)
  :short "Check if a literal is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Restrictions on the Grammar],
     literals cannot be larger than their types,
     and the largest type is that of 256-bit words.
     For now we do not model types (i.e. we assume one type),
     so we limit the size to 256 bits.
     To check this constraint,
     we just evaluate the literal
     and ensure that the evaluation does not return an error:
     this captures exactly the static constraints on literals.")
   (xdoc::p
    "We do not impose other restrictions on plain strings here,
     such as that a string surrounded by double quotes
     cannot contain (unescaped) double quotes.
     Those are simply syntactic restrictions."))
  (b* (((okf &) (eval-literal lit)))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-safe-expressions
  :short "Check if expressions are safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are checked in the context of
     a variable table and a function table."))

  (define check-safe-expression ((expr expressionp)
                                 (varset identifier-setp)
                                 (funtab funtablep))
    :returns (results? nat-resultp)
    :short "Check if an expression is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful, return the number of values that the expression yields.
       Otherwise, return an error.")
     (xdoc::p
      "A path always yields one result.")
     (xdoc::p
      "A literal's safety is independent from the variables in scope.
       A literal always returns one result."))
    (expression-case
     expr
     :path (b* (((okf &) (check-safe-path expr.get varset)))
             1)
     :literal (b* (((okf &) (check-safe-literal expr.get)))
                1)
     :funcall (check-safe-funcall expr.get varset funtab))
    :measure (expression-count expr))

  (define check-safe-expression-list ((exprs expression-listp)
                                      (varset identifier-setp)
                                      (funtab funtablep))
    :returns (number? nat-resultp)
    :short "Check if a list of expressions is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful, return the number of expressions.
       The caller can obtain this number directly from the list of expressions,
       but in the future this ACL2 function
       will likely return the list of types of the expressions,
       so we prefer to have already that kind of structure here.")
     (xdoc::p
      "We check each expression in turn.
       Each expression must return exactly one result."))
    (b* (((when (endp exprs)) 0)
         ((okf n) (check-safe-expression (car exprs) varset funtab))
         ((unless (= n 1))
          (reserrf (list :multi-value-argument (expression-fix (car exprs)))))
         ((okf n) (check-safe-expression-list (cdr exprs) varset funtab)))
      (1+ n))
    :measure (expression-list-count exprs))

  (define check-safe-funcall ((call funcallp)
                              (varset identifier-setp)
                              (funtab funtablep))
    :returns (results? nat-resultp)
    :short "Check if a function call is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "We look up the function in the function table,
       which is passed as parameter.
       We ensure that the number of inputs matches,
       and we return the number of outputs.
       Each argument expression must return a single result."))
    (b* (((funcall call) call)
         ((okf funty) (get-funtype call.name funtab))
         ((okf n) (check-safe-expression-list call.args varset funtab))
         ((unless (= n (funtype->in funty)))
          (reserrf (list :mismatched-formals-actuals
                         :required (funtype->in funty)
                         :supplied n))))
      (funtype->out funty))
    :measure (funcall-count call))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards check-safe-expression
    :hints
    (("Goal"
      :in-theory (enable acl2::natp-when-nat-resultp-and-not-reserrp))))

  (fty::deffixequiv-mutual check-safe-expressions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-variable-single ((name identifierp)
                                    (init expression-optionp)
                                    (varset identifier-setp)
                                    (funtab funtablep))
  :returns (varset? identifier-set-resultp)
  :short "Check if a single variable declaration is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee check-safe-statement):
     see that function's documentation for background.")
   (xdoc::p
    "The name of the variable must be an identifier
     that is not already in the variable table.
     The expression is checked if present,
     and it must return exactly one result."))
  (b* ((name (identifier-fix name))
       (init (expression-option-fix init))
       ((okf varset-new) (add-var name varset))
       ((when (not init)) varset-new)
       ((okf results) (check-safe-expression init varset funtab))
       ((unless (= results 1))
        (reserrf (list :declare-single-var-mismatch name results))))
    varset-new)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-variable-multi ((names identifier-listp)
                                   (init funcall-optionp)
                                   (varset identifier-setp)
                                   (funtab funtablep))
  :returns (varset? identifier-set-resultp)
  :short "Check if a multiple variable declaration is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee check-safe-statement):
     see that function's documentation for background.")
   (xdoc::p
    "The name of the variables must be identifiers
     that are not already in the variable table.
     They must also be distinct and at least two.
     The expression is checked if present,
     and it must return the same number of results
     as the number of variables."))
  (b* ((names (identifier-list-fix names))
       (init (funcall-option-fix init))
       ((okf varset-new) (add-vars names varset))
       ((unless (>= (len names) 2))
        (reserrf (list :declare-zero-one-var names)))
       ((when (not init)) varset-new)
       ((okf results) (check-safe-funcall init varset funtab))
       ((unless (= results (len names)))
        (reserrf (list :declare-multi-var-mismatch names results))))
    varset-new)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-assign-single ((target pathp)
                                  (value expressionp)
                                  (varset identifier-setp)
                                  (funtab funtablep))
  :returns (_ reserr-optionp)
  :short "Check if a single assignment is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee check-safe-expression),
     for now we require the path to be a singleton;
     see discussion there about non-singleton paths.")
   (xdoc::p
    "We check the expression, and and ensure that it returns one result."))
  (b* (((okf &) (check-safe-path target varset))
       ((okf results) (check-safe-expression value varset funtab))
       ((unless (= results 1))
        (reserrf (list :assign-single-var-mismatch (path-fix target) results))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-assign-multi ((targets path-listp)
                                 (value funcallp)
                                 (varset identifier-setp)
                                 (funtab funtablep))
  :returns (_ reserr-optionp)
  :short "Check if a multiple assignment is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee check-safe-expression),
     for now we require each path to be a singleton;
     see discussion there about non-singleton paths.")
   (xdoc::p
    "We check the function call, and ensure that it returns
     a number of results equal to the number of variables.
     The variables must be two or more."))
  (b* (((okf &) (check-safe-path-list targets varset))
       ((unless (>= (len targets) 2))
        (reserrf (list :assign-zero-one-path (path-list-fix targets))))
       ((okf results) (check-safe-funcall value varset funtab))
       ((unless (= results (len targets)))
        (reserrf (list :assign-single-var-mismatch
                       (path-list-fix targets) results))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod vars+modes
  :short "Fixtype of pairs consisting of a variable table and a set of modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of this fixtype capture the information calculated
     by the successful check of statements.
     The variable table captures the updated variable table.
     The set of modes captures the possible ways in which
     the statement may terminate."))
  ((vars identifier-set)
   (modes mode-set))
  :tag :vars+modes
  :pred vars+modes-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vars+modes-result
  :short "Fixtype of errors and
          pairs consisting of a variable table and a set of modes."
  :ok vars+modes
  :pred vars+modes-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-safe-statements/blocks/cases/fundefs
  :short "Check if statements, blocks, cases, and function definitions
          are safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are checked in the context of
     a variable table for visible and accessible variables @('varset'),
     and a function table @('funtab').")
   (xdoc::p
    "A successful check returns
     a set of possible modes in which execution may complete.
     The set of modes is used to check the conditions on
     the occurrence of @('leave'), @('break'), and @('continue') statements
     described in [Yul: Specification of Yul: Restrictions on the Grammar].
     The conditions there are phrased in terms of occurrences of constructs,
     but it is more convenient, in this formal static semantics,
     to check these conditions by putting restrictions on
     the possible modes statically calculated
     for statements and related constructs.
     This formulation is also more easily related to the dynamic semantics.
     At some point we may also formalize the conditions on
     the occurrence of @('leave'), @('break'), and @('continue') statements
     described in [Yul: Specification of Yul: Restrictions on the Grammar],
     and show that they are equivalent to our formulation here."))

  (define check-safe-statement ((stmt statementp)
                                (varset identifier-setp)
                                (funtab funtablep))
    :returns (varsmodes vars+modes-resultp)
    :short "Check if a statement is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "If checking is successful, we return an updated variable table
       and a set of possible termination modes.")
     (xdoc::p
      "The variable table is updated only via variable declarations,
       while the other kinds of statements leave the table unchanged.
       The table may be changed in blocks nested in the statement,
       but those changes do not surface outside those blocks.")
     (xdoc::p
      "A block is checked via a separate ACL2 function,
       which returns a set of modes.
       These are joined with the starting variable table,
       which is unchanged as expained above.")
     (xdoc::p
      "We use separate ACL2 functions to check declarations and assignments,
       as their checking does not involve the mutual recursion.
       Declarations and assignments always terminate in regular mode.")
     (xdoc::p
      "For a function call used as a statement,
       we check the function call and ensure it returns no results.
       A function call always terminates in regular mode.")
     (xdoc::p
      "For an @('if') statement,
       we check the test, which must return one result,
       and we check the body block.
       An @('if') statement may terminate in regular mode
       (when the test is false)
       or in any of the modes in which the block may terminate
       (when the test is true).")
     (xdoc::p
      "For a @('for') statement, we treat the initialization block specially,
       because the scope of the initialization block
       extends to the whole statement, as explained
       in [Yul: Specification of Yul: Scoping Rules].
       We extract the statements from the block
       and we process them as if they preceded the rest of the @('for'):
       we collect the function definitions in the statements,
       and then we check the statements,
       updating the variable table and obtaining the possible termination modes.
       We ensure that no termination in @('break') or @('continue') is possible,
       because that is not allowed,
       even if the @('for') is in the body of an outer @('for'):
       the current, innermost @('for') is the one
       that could be broken or continued,
       but that can only be done in the body;
       thus, the initialization block may only terminate
       in regular or @('leave') mode.
       We use the updated variable and function tables
       to check the other components of the @('for'),
       i.e. test, update block, and body block.
       We ensure that the update block cannot terminate
       in @('break') or @('continue') mode,
       for the same reason explained above for the initialization block,
       which therefore leaves regular and @('leave') mode
       as the only termination possibilities for the update block.
       The body is allowed to terminate in any mode.
       The possible termination modes of the @('for') loop
       are determined as follows:
       regular mode is always possible,
       which happens when the test is false or if the loop breaks;
       @('leave') mode is possible when it is possible for any of the
       initialization, update, or body block;
       @('break') and @('continue') modes are not possible,
       because those could only occur in the body,
       which causes regular loop termination of the loop for @('break')
       or continuation of the loop for @('continue').")
     (xdoc::p
      "For a @('switch') statement,
       we check the expression, ensuring it returns a single result.
       We ensure that there is at least one (literal or default) case
       [Yul: Specification of Yul: Restrictions on the Grammar].
       The documentation also requires that the default case be absent
       when the literal cases are exhaustive;
       but that requires knowledge of the type of the target expression,
       which for now we do not have, so we leave out that check for now.
       We also need to check that all the literals are distinct,
       which could be taken to mean as
       either syntactically or semantically distinct:
       for instance, the literals @('1') and @('0x1') are
       syntactically different but semantically equal.
       The Yul team has clarified that it should be semantic difference.
       For now we check syntactic difference for simplicity,
       but we plan to tighten that to check semantic difference.
       Every (literal or default) block is then checked,
       along with the literals.
       The possible termination modes are those of the cases
       and those of the default block.")
     (xdoc::p
      "The treatment of @('leave'), @('break'), and @('continue')
       is straightforward: they terminate with the corresponding mode,
       and the variable table is unchanged.")
     (xdoc::p
      "For a function definition, the function table is not updated:
       as explained in @(tsee add-funtypes),
       the function definitions in a block are collected,
       and used to extend the function table,
       before processing the statements in a block.
       The function definition is checked by a separate ACL2 function,
       which returns nothing in case of success,
       so here we return the outside variable table unchanged:
       a function definition does not modify the variable table.
       At run time, a function definition is essentially a no-op,
       so the termination mode is always regular."))
    (statement-case
     stmt
     :block
     (b* (((okf modes) (check-safe-block stmt.get varset funtab)))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes modes))
     :variable-single
     (b* (((okf varset) (check-safe-variable-single stmt.name
                                                    stmt.init
                                                    varset
                                                    funtab)))
       (make-vars+modes :vars varset
                        :modes (set::insert (mode-regular) nil)))
     :variable-multi
     (b* (((okf varset) (check-safe-variable-multi stmt.names
                                                   stmt.init
                                                   varset
                                                   funtab)))
       (make-vars+modes :vars varset
                        :modes (set::insert (mode-regular) nil)))
     :assign-single
     (b* (((okf &) (check-safe-assign-single stmt.target
                                             stmt.value
                                             varset
                                             funtab)))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes (set::insert (mode-regular) nil)))
     :assign-multi
     (b* (((okf &) (check-safe-assign-multi stmt.targets
                                            stmt.value
                                            varset
                                            funtab)))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes (set::insert (mode-regular) nil)))
     :funcall
     (b* (((okf results) (check-safe-funcall stmt.get varset funtab))
          ((unless (= results 0))
           (reserrf (list :discarded-values stmt.get))))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes (set::insert (mode-regular) nil)))
     :if
     (b* (((okf results) (check-safe-expression stmt.test varset funtab))
          ((unless (= results 1))
           (reserrf (list :multi-valued-if-test stmt.test)))
          ((okf modes) (check-safe-block stmt.body
                                         varset
                                         funtab)))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes (set::insert (mode-regular) modes)))
     :for
     (b* ((stmts (block->statements stmt.init))
          ((okf funtab) (add-funtypes (statements-to-fundefs stmts) funtab))
          ((okf varsmodes) (check-safe-statement-list stmts varset funtab))
          (varset1 (vars+modes->vars varsmodes))
          (init-modes (vars+modes->modes varsmodes))
          ((when (set::in (mode-break) init-modes))
           (reserrf (list :break-in-loop-init stmt.init)))
          ((when (set::in (mode-continue) init-modes))
           (reserrf (list :continue-in-loop-init stmt.init)))
          ((okf results) (check-safe-expression stmt.test varset1 funtab))
          ((unless (= results 1))
           (reserrf (list :multi-valued-for-test stmt.test)))
          ((okf update-modes) (check-safe-block stmt.update
                                                varset1
                                                funtab))
          ((when (set::in (mode-break) update-modes))
           (reserrf (list :break-in-loop-update stmt.update)))
          ((when (set::in (mode-continue) update-modes))
           (reserrf (list :continue-in-loop-update stmt.update)))
          ((okf body-modes) (check-safe-block stmt.body
                                              varset1
                                              funtab))
          (modes (if (or (set::in (mode-leave) init-modes)
                         (set::in (mode-leave) update-modes)
                         (set::in (mode-leave) body-modes))
                     (set::insert (mode-leave) (set::insert (mode-regular) nil))
                   (set::insert (mode-regular) nil))))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes modes))
     :switch
     (b* (((okf results) (check-safe-expression stmt.target varset funtab))
          ((unless (= results 1))
           (reserrf (list :multi-valued-switch-target stmt.target)))
          ((unless (or (consp stmt.cases) stmt.default))
           (reserrf (list :no-cases-in-switch (statement-fix stmt))))
          ((unless (no-duplicatesp-equal (swcase-list->value-list stmt.cases)))
           (reserrf (list :duplicate-switch-cases (statement-fix stmt))))
          ((okf cases-modes) (check-safe-swcase-list stmt.cases
                                                     varset
                                                     funtab))
          ((okf default-modes) (check-safe-block-option stmt.default
                                                        varset
                                                        funtab)))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes (set::union cases-modes default-modes)))
     :leave
     (make-vars+modes :vars (identifier-set-fix varset)
                      :modes (set::insert (mode-leave) nil))
     :break
     (make-vars+modes :vars (identifier-set-fix varset)
                      :modes (set::insert (mode-break) nil))
     :continue
     (make-vars+modes :vars (identifier-set-fix varset)
                      :modes (set::insert (mode-continue) nil))
     :fundef
     (b* (((okf &) (check-safe-fundef stmt.get funtab)))
       (make-vars+modes :vars (identifier-set-fix varset)
                        :modes (set::insert (mode-regular) nil))))
    :measure (statement-count stmt)
    :normalize nil) ; without this, MAKE-FLAG (generated by DEFINES) fails

  (define check-safe-statement-list ((stmts statement-listp)
                                     (varset identifier-setp)
                                     (funtab funtablep))
    :returns (varsmodes vars+modes-resultp)
    :short "Check if a list of statements is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the statements, one after the other,
       threading through the variable table.")
     (xdoc::p
      "If the list of statements is empty, the termination mode is regular.
       Otherwise, we have
       a set of possible termination modes for the first statement,
       and a set of possible termination modes for the remaining sets.
       If the first set includes regular mode,
       we take the union of the two sets;
       otherwise, we just return the first set
       because execution of the list of statements ends there.
       Note that we still check the safety of the remaining statements,
       even when they are not reachable."))
    (b* (((when (endp stmts))
          (make-vars+modes :vars (identifier-set-fix varset)
                           :modes (set::insert (mode-regular) nil)))
         ((okf varsmodes) (check-safe-statement (car stmts)
                                                varset
                                                funtab))
         (varset (vars+modes->vars varsmodes))
         (first-modes (vars+modes->modes varsmodes))
         ((okf varsmodes) (check-safe-statement-list (cdr stmts)
                                                     varset
                                                     funtab))
         (varset (vars+modes->vars varsmodes))
         (rest-modes (vars+modes->modes varsmodes))
         (modes (if (set::in (mode-regular) first-modes)
                    (set::union first-modes rest-modes)
                  first-modes)))
      (make-vars+modes :vars varset
                       :modes modes))
    :measure (statement-list-count stmts))

  (define check-safe-block ((block blockp)
                            (varset identifier-setp)
                            (funtab funtablep))
    :returns (modes mode-set-resultp)
    :short "Check if a block is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful,
       return the set of possible termination modes of the block.")
     (xdoc::p
      "As explained in @(tsee add-funtypes),
       all the functions defined in a block are visible in the whole block,
       so we first collect them from the statements that form the block,
       updating the function table with them,
       and then we check the statements that form the block,
       discarding the final variable table."))
    (b* ((stmts (block->statements block))
         ((okf funtab) (add-funtypes (statements-to-fundefs stmts) funtab))
         ((okf varsmodes) (check-safe-statement-list stmts varset funtab)))
      (vars+modes->modes varsmodes))
    :measure (block-count block))

  (define check-safe-block-option ((block? block-optionp)
                                   (varset identifier-setp)
                                   (funtab funtablep))
    :returns (modes mode-set-resultp)
    :short "Check if an optional block is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no block,
       the check succeeds and we return just regular mode.
       If there is a block, we check it."))
    (block-option-case
     block?
     :none (set::insert (mode-regular) nil)
     :some (check-safe-block (block-option-some->val block?)
                             varset
                             funtab))
    :measure (block-option-count block?))

  (define check-safe-swcase ((case swcasep)
                             (varset identifier-setp)
                             (funtab funtablep))
    :returns (modes mode-set-resultp)
    :short "Check if a case is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check its literal and its block.
       We return the termination modes of the block."))
    (b* (((swcase case) case)
         ((okf &) (check-safe-literal case.value)))
      (check-safe-block case.body
                        varset
                        funtab))
    :measure (swcase-count case))

  (define check-safe-swcase-list ((cases swcase-listp)
                                  (varset identifier-setp)
                                  (funtab funtablep))
    :returns (modes mode-set-resultp)
    :short "Check if a list of cases is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return the empty set for the empty list of cases:
       having no cases contributes no termination modes.
       If the list of cases is not empty,
       we return the union of the termination modes of the first case
       with the union of the termination modes for the remaining cases."))
    (b* (((when (endp cases)) nil)
         ((okf first-modes) (check-safe-swcase (car cases)
                                               varset
                                               funtab))
         ((okf rest-modes) (check-safe-swcase-list (cdr cases)
                                                   varset
                                                   funtab)))
      (set::union first-modes rest-modes))
    :measure (swcase-list-count cases))

  (define check-safe-fundef ((fundef fundefp)
                             (funtab funtablep))
    :returns (_ reserr-optionp)
    :short "Check if a function definition is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "This ACL2 function takes as input less contextual information
       than its mutually recursive companions.
       The reason is that such contextual information is always set
       when a funtion definition is checked.
       In particular, there is no variable table to pass.")
     (xdoc::p
      "This ACL2 function does not need to return anything.
       Any variable table internal to the function's body
       does not surface outside the function's body.
       Also recall that the function definition itself
       is added to the function table prior to checking it;
       see @(tsee add-funtypes).")
     (xdoc::p
      "To check the function definition, we construct an initial variable table
       from the inputs and outputs of the function.
       Note that the construction will detect and reject any duplicates.
       Then we check the function's body,
       ensuring that it does not end with @('break') or @('continue'),
       (i.e. only with @('leave') or regularly)."))
    (b* (((fundef fundef) fundef)
         ((okf varset) (add-vars fundef.inputs nil))
         ((okf varset) (add-vars fundef.outputs varset))
         ((okf modes) (check-safe-block fundef.body
                                        varset
                                        funtab))
         ((when (set::in (mode-break) modes))
          (reserrf (list :break-from-function (fundef-fix fundef))))
         ((when (set::in (mode-continue) modes))
          (reserrf (list :continue-from-function (fundef-fix fundef)))))
      nil)
    :measure (fundef-count fundef))

  :prepwork
  ((local
    (in-theory (enable mode-setp-when-mode-set-resultp-and-not-reserrp))))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards check-safe-statement
    :hints
    (("Goal"
      :in-theory
      (enable identifier-setp-when-identifier-set-resultp-and-not-reserrp))))

  (fty::deffixequiv-mutual check-safe-statements/blocks/cases/fundefs)

  (defrule check-safe-block-option-when-blockp
    (implies (blockp block)
             (equal (check-safe-block-option block varset funtab)
                    (check-safe-block block varset funtab)))
    :enable block-option-some->val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-fundef-list ((fundefs fundef-listp) (funtab funtablep))
  :returns (_ reserr-optionp)
  :short "Check if a list of function definitions is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not really add anything
     compared to @(tsee check-safe-statement-list),
     in the sense that checking the safety of a list of function definitions
     is the same as checking the safety of them as a list of statements.
     However, it is convenient to define a dedicated ACL2 function
     to check the safety of lists of function definitions directly,
     and that does not return any information if the safety checks succeed.
     (This ACL2 function is used in the "
    (xdoc::seetopic "static-soundness" "static soundness proof")
    ".)")
   (xdoc::p
    "We prove that if a list of statements passes the safety checks,
     the list of function definitions extracted from the statements
     passes the safety checks according to this ACL2 function.
     Given that the statement checking functions take variable tables as inputs
     while the function definition checking function do not,
     and given that the statement checking functions modify variable tables
     and thread them through the list of statements,
     we carry out the induction proof on a predicate
     that is universally quantified over variable tables."))
  (b* (((when (endp fundefs)) nil)
       ((okf &) (check-safe-fundef (car fundefs) funtab))
       ((okf &) (check-safe-fundef-list (cdr fundefs) funtab)))
    nil)
  :hooks (:fix)
  ///

  (defruled check-safe-fundef-list-of-statements-to-fundefs
    (implies (not (reserrp
                   (check-safe-statement-list stmts varset funtab)))
             (not (reserrp
                   (check-safe-fundef-list (statements-to-fundefs stmts)
                                           funtab))))
    :use pred-holds
    :enable pred-necc

    :prep-lemmas

    ((defund-sk pred (stmts funtab)
       (forall varset
               (implies
                (not (reserrp
                      (check-safe-statement-list stmts varset funtab)))
                (not (reserrp
                      (check-safe-fundef-list (statements-to-fundefs stmts)
                                              funtab)))))
       :rewrite :direct)

     (defruled base-case
       (implies (not (consp stmts))
                (pred stmts funtab))
       :enable (pred
                statements-to-fundefs
                check-safe-statement-list
                check-safe-fundef-list))


     (defruled step-lemma
       (implies (and (consp stmts)
                     (pred (cdr stmts) funtab)
                     (not (reserrp
                           (check-safe-statement-list stmts varset funtab))))
                (not (reserrp
                      (check-safe-fundef-list (statements-to-fundefs stmts)
                                              funtab))))
       :expand (check-safe-statement-list stmts varset funtab)
       :enable (pred-necc
                check-safe-statement
                statements-to-fundefs
                check-safe-statement-list
                check-safe-fundef-list))

     (defruled step-case
       (implies (and (consp stmts)
                     (pred (cdr stmts) funtab))
                (pred stmts funtab))
       :expand (pred stmts funtab)
       :enable step-lemma)

     (defruled pred-holds
       (pred stmts funtab)
       :induct (len stmts)
       :enable (base-case step-case)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-top-block ((block blockp))
  :returns (_ reserr-optionp)
  :short "Check if the top block is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the safety of the block
     starting with no variables or functions in scope,
     because this is the block at the top level.
     Since the top block is not inside a function or loop,
     it is only allowed to terminate regularly.
     If the checking succeeds, we return nothing (i.e. @('nil')).
     Otherwise, we return an error."))
  (b* (((okf modes) (check-safe-block block nil nil)))
    (if (equal modes (set::insert (mode-regular) nil))
        nil
      (reserrf (list :top-block-mode modes))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection check-safe-extends-varset
  :short "Theorems about the variable table being extended
          by the ACL2 safety checking functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The safety checking functions that return updated variables tables,
     namely @(tsee check-safe-statement) and @(tsee check-safe-statement-list),
     extend the variable table in general.
     That is, the resulting variable table is always a superset
     of the initial variable table;
     this is not strict superset, i.e. they may be equal.
     We prove that first for @(tsee add-var) and @(tsee add-vars),
     which are the functions that actually extend the variable table
     in the safety checking functions,
     and then we prove it on the safety checking functions by induction."))

  (defrule add-var-extends-varset
    (implies (identifier-setp varset)
             (b* ((varset1 (add-var var varset)))
               (implies (not (reserrp varset1))
                        (set::subset varset varset1))))
    :enable add-var)

  (defrule add-vars-extends-varset
    (implies (identifier-setp varset)
             (b* ((varset1 (add-vars vars varset)))
               (implies (not (reserrp varset1))
                        (set::subset varset varset1))))
    :enable (add-vars
             set::subset-transitive))

  (defrule check-safe-variable-single-extends-varset
    (implies (identifier-setp varset)
             (b* ((varset1 (check-safe-variable-single name init varset funtab)))
               (implies (not (reserrp varset1))
                        (set::subset varset varset1))))
    :enable check-safe-variable-single)

  (defrule check-safe-variable-multi-extends-varset
    (implies (identifier-setp varset)
             (b* ((varset1 (check-safe-variable-multi name init varset funtab)))
               (implies (not (reserrp varset1))
                        (set::subset varset varset1))))
    :enable check-safe-variable-multi)

  (defthm-check-safe-statements/blocks/cases/fundefs-flag

    (defthm check-safe-statement-extends-varset
      (implies
       (identifier-setp varset)
       (b* ((varsmodes (check-safe-statement stmt varset funtab)))
         (implies (not (reserrp varsmodes))
                  (set::subset varset
                               (vars+modes->vars varsmodes)))))
      :flag check-safe-statement)

    (defthm check-safe-statement-list-extends-varset
      (implies
       (identifier-setp varset)
       (b* ((varsmodes (check-safe-statement-list stmts varset funtab)))
         (implies (not (reserrp varsmodes))
                  (set::subset varset
                               (vars+modes->vars varsmodes)))))
      :flag check-safe-statement-list)

    (defthm check-safe-block-extends-varset
      t
      :rule-classes nil
      :flag check-safe-block)

    (defthm check-safe-block-option-extends-varset
      t
      :rule-classes nil
      :flag check-safe-block-option)

    (defthm check-safe-swcase-extends-varset
      t
      :rule-classes nil
      :flag check-safe-swcase)

    (defthm check-safe-swcase-list-extends-varset
      t
      :rule-classes nil
      :flag check-safe-swcase-list)

    (defthm check-safe-fundef-extends-varset
      t
      :rule-classes nil
      :flag check-safe-fundef)

    :hints
    (("Goal"
      :in-theory
      (enable
       check-safe-statement
       check-safe-statement-list
       set::subset-transitive
       identifier-setp-when-identifier-set-resultp-and-not-reserrp)))))
