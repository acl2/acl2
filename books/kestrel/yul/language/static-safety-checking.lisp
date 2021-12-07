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
(include-book "modes")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/nat-result" :dir :system)
(include-book "kestrel/std/util/defund-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-safety-checking
  :parents (static-semantics)
  :short "Static safety checking of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is (the main) part of the Yul static semantics.
     It consists of checks that ensure the safety of execution,
     i.e. that certain situations never happens during execution,
     such as reading or writing a non-existent variable.
     Our formal dynamic semantics of Yul defensively checks these conditions,
     returning error values when the conditions are not satisfied.
     The static safety checks formalized here
     ensure that those error values are never returned by the dynamic semantics,
     as we will formally prove soon."))
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

;;;;;;;;;;;;;;;;;;;;

(defruled not-resulterrp-when-funtypep
  (implies (funtypep x)
           (not (resulterrp x)))
  :enable (funtypep resulterrp))

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

;;;;;;;;;;;;;;;;;;;;

(defruled not-resulterrp-when-funtablep
  (implies (funtablep x)
           (not (resulterrp x)))
  :enable resulterrp)

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
  (b* ((pair (omap::in (identifier-fix name) (funtable-fix funtab))))
    (if (consp pair)
        (cdr pair)
      (err (list :function-not-found (identifier-fix name)))))
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
       ((ok funtab) (funtable-for-fundefs (cdr fundefs)))
       (fundef (car fundefs))
       (fun (fundef->name fundef))
       ((when (consp (omap::in fun funtab)))
        (err (list :duplicate-function fun))))
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
       ((ok funtab1) (funtable-for-fundefs fundefs))
       (overlap (set::intersect (omap::keys funtab1)
                                (omap::keys funtab)))
       ((unless (set::empty overlap))
        (err (list :duplicate-functions overlap))))
    (omap::update* funtab1 funtab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset vartable
  :short "Fixtype of variable tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are symbol tables for variables.
     For now a table is just a set of variable names (identifiers),
     because there is no type information associated to variables
     (cf. abstract syntax),
     but we may extend this to an omap from variables to types in the future.
     Currently this fixtype is equivalent to @(tsee identifier-set),
     but we make it a separate fixtype to facilitate
     the aforementioned extension in the future.")
   (xdoc::p
    "A variable table as defined here consists of the variables that are
     not only visible, but also accessible,
     according to [Yul: Specification of Yul: Scoping Rules]:
     a variable is visible in the rest of the block in which it is declared,
     including sub-blocks,
     but it is not accessible in
     function definitions in the block or sub-blocks.
     Variables that are visible but inaccessible
     are not represented in the variable tables defined here."))
  :elt-type identifier
  :elementp-of-nil nil
  :pred vartablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vartable-result
  :short "Fixtype of errors and variable tables."
  :ok vartable
  :pred vartable-resultp)

;;;;;;;;;;;;;;;;;;;;

(defruled not-resulterrp-when-vartablep
  (implies (vartablep x)
           (not (resulterrp x)))
  :enable (vartablep resulterrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-var ((var identifierp) (vartab vartablep))
  :returns (yes/no booleanp)
  :short "Check if a variable is in a variable table."
  (set::in (identifier-fix var) (vartable-fix vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var ((var identifierp) (vartab vartablep))
  :returns (vartab? vartable-resultp)
  :short "Add a variable to a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a variable with the same name is already in the table,
     an error is returned."))
  (b* ((var (identifier-fix var))
       (vartab (vartable-fix vartab)))
    (if (set::in var vartab)
        (err (list :duplicate-variable var))
      (set::insert var vartab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-vars ((vars identifier-listp)
                  (vartab vartablep))
  :returns (vartab? vartable-resultp)
  :short "Add (a list of) variables to a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are added, one after the other.
     Duplicates in the list will cause an error.")
   (xdoc::p
    "This lifts @(tsee add-var) to lists."))
  (b* (((when (endp vars)) (vartable-fix vartab))
       ((ok vartab) (add-var (car vars) vartab)))
    (add-vars (cdr vars) vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-path ((path pathp) (vartab vartablep))
  :returns (_ resulterr-optionp)
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
        (err (list :empty-path (path-fix path))))
       ((unless (endp (cdr idens)))
        (err (list :non-singleton-path (path-fix path))))
       (var (car idens))
       ((unless (check-var var vartab))
        (err (list :variable-not-found var))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-path-list ((paths path-listp) (vartab vartablep))
  :returns (_ resulterr-optionp)
  :short "Check if a list of paths is safe."
  (b* (((when (endp paths)) nil)
       ((ok &) (check-safe-path (car paths) vartab)))
    (check-safe-path-list (cdr paths) vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-literal ((lit literalp))
  :returns (_ resulterr-optionp)
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
  (b* (((ok &) (eval-literal lit)))
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
                                 (vartab vartablep)
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
     :path (b* (((ok &) (check-safe-path expr.get vartab)))
             1)
     :literal (b* (((ok &) (check-safe-literal expr.get)))
                1)
     :funcall (check-safe-funcall expr.get vartab funtab))
    :measure (expression-count expr))

  (define check-safe-expression-list ((exprs expression-listp)
                                      (vartab vartablep)
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
         ((ok n) (check-safe-expression (car exprs) vartab funtab))
         ((unless (= n 1))
          (err (list :multi-value-argument (expression-fix (car exprs)))))
         ((ok n) (check-safe-expression-list (cdr exprs) vartab funtab)))
      (1+ n))
    :measure (expression-list-count exprs))

  (define check-safe-funcall ((call funcallp)
                              (vartab vartablep)
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
         ((ok funty) (get-funtype call.name funtab))
         ((ok n) (check-safe-expression-list call.args vartab funtab))
         ((unless (= n (funtype->in funty)))
          (err (list :mismatched-formals-actuals
                     :required (funtype->in funty)
                     :supplied n))))
      (funtype->out funty))
    :measure (funcall-count call))

  :verify-guards nil ; done below
  ///
  (verify-guards check-safe-expression
    :hints
    (("Goal"
      :in-theory (enable acl2::natp-when-nat-resultp-and-not-resulterrp))))

  (fty::deffixequiv-mutual check-safe-expressions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-variable-single ((name identifierp)
                                    (init expression-optionp)
                                    (vartab vartablep)
                                    (funtab funtablep))
  :returns (vartab? vartable-resultp)
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
       ((ok vartab-new) (add-var name vartab))
       ((when (not init)) vartab-new)
       ((ok results) (check-safe-expression init vartab funtab))
       ((unless (= results 1))
        (err (list :declare-single-var-mismatch name results))))
    vartab-new)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-variable-multi ((names identifier-listp)
                                   (init funcall-optionp)
                                   (vartab vartablep)
                                   (funtab funtablep))
  :returns (vartab? vartable-resultp)
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
       ((ok vartab-new) (add-vars names vartab))
       ((unless (>= (len names) 2))
        (err (list :declare-zero-one-var names)))
       ((when (not init)) vartab-new)
       ((ok results) (check-safe-funcall init vartab funtab))
       ((unless (= results (len names)))
        (err (list :declare-multi-var-mismatch names results))))
    vartab-new)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-assign-single ((target pathp)
                                  (value expressionp)
                                  (vartab vartablep)
                                  (funtab funtablep))
  :returns (_ resulterr-optionp)
  :short "Check if a single assignment is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee check-safe-expression),
     for now we require the path to be a singleton;
     see discussion there about non-singleton paths.")
   (xdoc::p
    "We check the expression, and and ensure that it returns one result."))
  (b* (((ok &) (check-safe-path target vartab))
       ((ok results) (check-safe-expression value vartab funtab))
       ((unless (= results 1))
        (err (list :assign-single-var-mismatch (path-fix target) results))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-assign-multi ((targets path-listp)
                                 (value funcallp)
                                 (vartab vartablep)
                                 (funtab funtablep))
  :returns (_ resulterr-optionp)
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
  (b* (((ok &) (check-safe-path-list targets vartab))
       ((unless (>= (len targets) 2))
        (err (list :assign-zero-one-path (path-list-fix targets))))
       ((ok results) (check-safe-funcall value vartab funtab))
       ((unless (= results (len targets)))
        (err (list :assign-single-var-mismatch
               (path-list-fix targets) results))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod vartable-modes
  :short "Fixtype of pairs consisting of a variable table and a set of modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Values of this fixtype capture the information calculated
     by the successful check of statements.
     The variable table captures the updated variable table.
     The set of modes captures the possible ways in which
     the statement may terminate."))
  ((variables vartable)
   (modes mode-set))
  :tag :vartable-modes
  :pred vartable-modes-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vartable-modes-result
  :short "Fixtype of errors and
          pairs consisting of a variable table and a set of modes."
  :ok vartable-modes
  :pred vartable-modes-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-safe-statements/blocks/cases/fundefs
  :short "Check if statements, blocks, cases, and function definitions
          are safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are checked in the context of
     a variable table for visible and accessible variable @('vartab'),
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
                                (vartab vartablep)
                                (funtab funtablep))
    :returns (vartab-modes vartable-modes-resultp)
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
     (b* (((ok modes) (check-safe-block stmt.get vartab funtab)))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes modes))
     :variable-single
     (b* (((ok vartab) (check-safe-variable-single stmt.name
                                                   stmt.init
                                                   vartab
                                                   funtab)))
       (make-vartable-modes :variables vartab
                            :modes (set::insert (mode-regular) nil)))
     :variable-multi
     (b* (((ok vartab) (check-safe-variable-multi stmt.names
                                                  stmt.init
                                                  vartab
                                                  funtab)))
       (make-vartable-modes :variables vartab
                            :modes (set::insert (mode-regular) nil)))
     :assign-single
     (b* (((ok &) (check-safe-assign-single stmt.target
                                            stmt.value
                                            vartab
                                            funtab)))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes (set::insert (mode-regular) nil)))
     :assign-multi
     (b* (((ok &) (check-safe-assign-multi stmt.targets
                                           stmt.value
                                           vartab
                                           funtab)))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes (set::insert (mode-regular) nil)))
     :funcall
     (b* (((ok results) (check-safe-funcall stmt.get vartab funtab))
          ((unless (= results 0))
           (err (list :discarded-values stmt.get))))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes (set::insert (mode-regular) nil)))
     :if
     (b* (((ok results) (check-safe-expression stmt.test vartab funtab))
          ((unless (= results 1))
           (err (list :multi-valued-if-test stmt.test)))
          ((ok modes) (check-safe-block stmt.body
                                        vartab
                                        funtab)))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes (set::insert (mode-regular) modes)))
     :for
     (b* ((stmts (block->statements stmt.init))
          ((ok funtab) (add-funtypes (statements-to-fundefs stmts) funtab))
          ((ok vartab-modes) (check-safe-statement-list stmts
                                                        vartab
                                                        funtab))
          (vartab1 (vartable-modes->variables vartab-modes))
          (init-modes (vartable-modes->modes vartab-modes))
          ((when (set::in (mode-break) init-modes))
           (err (list :break-in-loop-init stmt.init)))
          ((when (set::in (mode-continue) init-modes))
           (err (list :continue-in-loop-init stmt.init)))
          ((ok results) (check-safe-expression stmt.test vartab1 funtab))
          ((unless (= results 1))
           (err (list :multi-valued-for-test stmt.test)))
          ((ok update-modes) (check-safe-block stmt.update
                                               vartab1
                                               funtab))
          ((when (set::in (mode-break) update-modes))
           (err (list :break-in-loop-update stmt.update)))
          ((when (set::in (mode-continue) update-modes))
           (err (list :continue-in-loop-update stmt.update)))
          ((ok body-modes) (check-safe-block stmt.body
                                             vartab1
                                             funtab))
          (modes (if (or (set::in (mode-leave) init-modes)
                         (set::in (mode-leave) update-modes)
                         (set::in (mode-leave) body-modes))
                     (set::insert (mode-leave) (set::insert (mode-regular) nil))
                   (set::insert (mode-regular) nil))))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes modes))
     :switch
     (b* (((ok results) (check-safe-expression stmt.target vartab funtab))
          ((unless (= results 1))
           (err (list :multi-valued-switch-target stmt.target)))
          ((unless (or (consp stmt.cases) stmt.default))
           (err (list :no-cases-in-switch (statement-fix stmt))))
          ((unless (no-duplicatesp-equal (swcase-list->value-list stmt.cases)))
           (err (list :duplicate-switch-cases (statement-fix stmt))))
          ((ok cases-modes) (check-safe-swcase-list stmt.cases
                                                    vartab
                                                    funtab))
          ((ok default-modes) (check-safe-block-option stmt.default
                                                       vartab
                                                       funtab)))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes (set::union cases-modes default-modes)))
     :leave
     (make-vartable-modes :variables (vartable-fix vartab)
                          :modes (set::insert (mode-leave) nil))
     :break
     (make-vartable-modes :variables (vartable-fix vartab)
                          :modes (set::insert (mode-break) nil))
     :continue
     (make-vartable-modes :variables (vartable-fix vartab)
                          :modes (set::insert (mode-continue) nil))
     :fundef
     (b* (((ok &) (check-safe-fundef stmt.get funtab)))
       (make-vartable-modes :variables (vartable-fix vartab)
                            :modes (set::insert (mode-regular) nil))))
    :measure (statement-count stmt)
    :normalize nil) ; without this, MAKE-FLAG (generated by DEFINES) fails

  (define check-safe-statement-list ((stmts statement-listp)
                                     (vartab vartablep)
                                     (funtab funtablep))
    :returns (vartab-modes vartable-modes-resultp)
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
          (make-vartable-modes :variables (vartable-fix vartab)
                               :modes (set::insert (mode-regular) nil)))
         ((ok vartab-modes) (check-safe-statement (car stmts)
                                                  vartab
                                                  funtab))
         (vartab (vartable-modes->variables vartab-modes))
         (first-modes (vartable-modes->modes vartab-modes))
         ((ok vartab-modes) (check-safe-statement-list (cdr stmts)
                                                       vartab
                                                       funtab))
         (vartab (vartable-modes->variables vartab-modes))
         (rest-modes (vartable-modes->modes vartab-modes))
         (modes (if (set::in (mode-regular) first-modes)
                    (set::union first-modes rest-modes)
                  first-modes)))
      (make-vartable-modes :variables vartab
                           :modes modes))
    :measure (statement-list-count stmts))

  (define check-safe-block ((block blockp)
                            (vartab vartablep)
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
         ((ok funtab) (add-funtypes (statements-to-fundefs stmts) funtab))
         ((ok vartab-modes) (check-safe-statement-list stmts
                                                       vartab
                                                       funtab)))
      (vartable-modes->modes vartab-modes))
    :measure (block-count block))

  (define check-safe-block-option ((block? block-optionp)
                                   (vartab vartablep)
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
                             vartab
                             funtab))
    :measure (block-option-count block?))

  (define check-safe-swcase ((case swcasep)
                             (vartab vartablep)
                             (funtab funtablep))
    :returns (modes mode-set-resultp)
    :short "Check if a case is safe."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check its literal and its block.
       We return the termination modes of the block."))
    (b* (((swcase case) case)
         ((ok &) (check-safe-literal case.value)))
      (check-safe-block case.body
                        vartab
                        funtab))
    :measure (swcase-count case))

  (define check-safe-swcase-list ((cases swcase-listp)
                                  (vartab vartablep)
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
         ((ok first-modes) (check-safe-swcase (car cases)
                                              vartab
                                              funtab))
         ((ok rest-modes) (check-safe-swcase-list (cdr cases)
                                                  vartab
                                                  funtab)))
      (set::union first-modes rest-modes))
    :measure (swcase-list-count cases))

  (define check-safe-fundef ((fundef fundefp)
                             (funtab funtablep))
    :returns (_ resulterr-optionp)
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
         ((ok vartab) (add-vars (append fundef.inputs fundef.outputs) nil))
         ((ok modes) (check-safe-block fundef.body
                                       vartab
                                       funtab))
         ((when (set::in (mode-break) modes))
          (err (list :break-from-function (fundef-fix fundef))))
         ((when (set::in (mode-continue) modes))
          (err (list :continue-from-function (fundef-fix fundef)))))
      nil)
    :measure (fundef-count fundef))

  :prepwork
  ((local
    (in-theory (enable mode-setp-when-mode-set-resultp-and-not-resulterrp))))

  :flag-local nil

  :verify-guards nil ; done below
  ///
  (verify-guards check-safe-statement
    :hints
    (("Goal"
      :in-theory
      (enable vartablep-when-vartable-resultp-and-not-resulterrp))))

  (fty::deffixequiv-mutual check-safe-statements/blocks/cases/fundefs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-fundef-list ((fundefs fundef-listp) (funtab funtablep))
  :returns (_ resulterr-optionp)
  :short "Check if a list of function definitions is safe."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not really add anything
     compared to @(tsee check-safe-statement-list),
     in the sense that checking the safey of a list of function definitions
     is the same as checking the safety of them as a list of statements.
     However, it is convenient to define a dedicated ACL2 function
     to check the safety of lists of function definitions directly,
     and that does not return any information if the safety checks succeed.
     (This ACL2 function is used in the "
    (xdoc::seetopic "static-soundness" "static soundness proof")
    ".)")
   (xdoc::p
    "We prove that if a list of statements passes the safety checks,
     the list of function definitions extraced from the statements
     passed the safety checks according to this ACL2 function.
     Given that the statement checking functions take variables tables as inputs
     while the function definition checking function do not,
     and given that the statement checking functions modify variable tables
     and thread them through the list of statements,
     we carry out the induction proof on a predicate
     that is universally quantified over variable tables."))
  (b* (((when (endp fundefs)) nil)
       ((ok &) (check-safe-fundef (car fundefs) funtab))
       ((ok &) (check-safe-fundef-list (cdr fundefs) funtab)))
    nil)
  :hooks (:fix)
  ///

  (defruled check-safe-fundef-list-of-statements-to-fundefs
    (implies (not (resulterrp
                   (check-safe-statement-list stmts vartab funtab)))
             (not (resulterrp
                   (check-safe-fundef-list (statements-to-fundefs stmts)
                                           funtab))))
    :use pred-holds
    :enable pred-necc

    :prep-lemmas

    ((defund-sk pred (stmts funtab)
       (forall vartab
               (implies
                (not (resulterrp
                      (check-safe-statement-list stmts vartab funtab)))
                (not (resulterrp
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
                     (not (resulterrp
                           (check-safe-statement-list stmts vartab funtab))))
                (not (resulterrp
                      (check-safe-fundef-list (statements-to-fundefs stmts)
                                              funtab))))
       :expand (check-safe-statement-list stmts vartab funtab)
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
