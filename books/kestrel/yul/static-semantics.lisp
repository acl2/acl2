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
(include-book "errors")

(include-book "kestrel/fty/defunit" :dir :system)
(include-book "kestrel/utilities/strings/char-kinds" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (yul)
  :short "Static semantics of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the static semantics of Yul
     via functions that check that the abstract syntax of Yul
     satisfy a number of constraints.")
   (xdoc::p
    "Since, as explained in @(see abstract-syntax), we omit types for now,
     type checking is prominently missing for now.
     We will probably want to introduce some notion of types soon."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defunit wellformed
  :short "Fixtype of the well-formedness indicator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is returned by the ACL2 static semantic checking functions
     when an abstract syntactic entity passes the static semantic checks
     and there is no additional information to return.
     When the static semantic checks fail,
     those functions return errors instead;
     see @(tsee wellformed-result)."))
  :value :wellformed
  :pred wellformedp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult wellformed "the @(tsee wellformed) indicator")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-identifier ((iden identifierp))
  :returns (wf? wellformed-resultp)
  :short "Check if an identifier is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of only
     letter (lowercase and uppercase),
     (decimal) digits,
     underscores, and
     dollars.
     It must be non-empty and not start with a digit.")
   (xdoc::p
    "We may move these requirements into an invariant of @(tsee identifier),
     but for now we state them as part of the static semantics."))
  (b* ((chars (str::explode (identifier->get iden))))
    (if (and (consp chars)
             (acl2::alpha/uscore/dollar-char-p (car chars))
             (acl2::alpha/digit/uscore/dollar-charlist-p (cdr chars)))
        :wellformed
      (error (list :bad-identifier (identifier-fix iden)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-identifier-list ((idens identifier-listp))
  :returns (wf? wellformed-resultp)
  :short "Check if all the identifiers in a list are well-formed."
  (b* (((when (endp idens)) :wellformed)
       (wf? (check-identifier (car idens)))
       ((when (errorp wf?)) wf?)
       (wf? (check-identifier-list (cdr idens)))
       ((when (errorp wf?)) wf?))
    :wellformed)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-path ((path pathp))
  :returns (wf? wellformed-resultp)
  :short "Check if a path is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of one or more well-formed identifiers.")
   (xdoc::p
    "We may move the non-emptiness requirement
     into an invariant of @(tsee path),
     but for now we state it as part of the static semantics."))
  (b* ((idens (path->get path))
       ((unless (consp idens)) (error (list :empty-path)))
       (wf? (check-identifier-list idens))
       ((when (errorp wf?)) wf?))
    :wellformed)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-literal ((lit literalp))
  :returns (wf? wellformed-resultp)
  :short "Check if a literal is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Restrictions on the Grammar],
     literals cannot be larger than their types,
     and the largest type is that of unsigned 256-bit integers.
     For now we do not model types (i.e. we assume one type),
     so we limit the size to 256 bits.
     This is straighforward for numeric literals.
     For (non-hex) string, it boils down to a limit of 32 on the length
     (since every character represents 8 bits).
     For hex strigns, it boils down to a limit of 32 on the number of hex pairs;
     hex strings must also be non-empty, according to the grammar.
     Boolean literals are always well-formed;
     they are not, and they do not represent, numbers anyways.")
   (xdoc::p
    "We do not impose other restrictions on (non-hex) strings here,
     such as that a string surrounded by double quotes
     cannot contain (unescaped) double quotes.
     Those are simply syntactic restrictions."))
  (b* ((err (error (list :bad-literal (literal-fix lit)))))
    (literal-case
     lit
     :boolean :wellformed
     :dec-number (if (< lit.get
                        (expt 2 256))
                     :wellformed
                   err)
     :hex-number (if (< (str::hex-digit-chars-value
                         (hex-digit-list->chars lit.get))
                        (expt 2 256))
                     :wellformed
                   err)
     :string (if (<= (len lit.content) 32)
                 :wellformed
               err)
     :hex-string (if (and (< 0 (len lit.content))
                          (<= (len lit.content) 32))
                     :wellformed
                   err)))
  :hooks (:fix))

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

(defresult funtype "function types")

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

(defresult funtable "function tables")

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
      (error (list :function-not-found (identifier-fix name)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-funtype ((name identifierp) (in natp) (out natp) (funtab funtablep))
  :returns (funtab? funtable-resultp)
  :short "Add a function and its type to a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return an error if a function with that name is already in the table."))
  (b* ((pair (omap::in (identifier-fix name) (funtable-fix funtab))))
    (if (consp pair)
        (error (list :duplicate-function (identifier-fix name)))
      (omap::update (identifier-fix name)
                    (make-funtype :in in :out out)
                    (funtable-fix funtab))))
  ///
  (fty::deffixequiv add-funtype :hints (("Goal" :in-theory (disable nfix)))))

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
     Variables that are visible but inaccessible are represented
     not in the variable tables defined here."))
  :elt-type identifier
  :elementp-of-nil nil
  :pred vartablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule vartablep-of-mergesort
  (implies (identifier-listp x)
           (vartablep (set::mergesort x)))
  :enable set::mergesort)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-expressions/funcalls
  :short "Check if expressions and function calls are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are checked in the context of
     a variable table and a function table."))

  (define check-expression ((expr expressionp)
                            (vartab vartablep)
                            (funtab funtablep))
    :returns (results? nat-resultp)
    :short "Check if an expression is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful, return the number of values that the expression yields.
       Otherwise, return an error.")
     (xdoc::p
      "It is not yet clear how paths with more than one identifier
       come about in generic Yul:
       variable declarations are for single identifiers
       (whether one single identifier,
       or two or more single identifiers),
       so it seems that singleton paths would always suffice to reference them
       in expressions and statements.
       For now we only regard singleton paths as well-formed,
       provided they are part of the accessible variables.
       A path always yields one result, so we return 1.")
     (xdoc::p
      "A literal's well-formedness is independent from the accessible variables.
       A literal always returns one result, so we return 1."))
    (expression-case
     expr
     :path
     (if (and (consp expr.get)
              (not (consp (cdr expr.get)))
              (set::in (car expr.get) (vartable-fix vartab)))
         1
       (error (list :bad-path expr.get)))
     :literal
     (b* ((wf? (check-literal expr.get))
          ((when (errorp wf?)) wf?))
       1)
     :funcall
     (check-funcall expr.get vartab funtab))
    :measure (expression-count expr))

  (define check-expression-list ((exprs expression-listp)
                                 (vartab vartablep)
                                 (funtab funtablep))
    :returns (number? nat-resultp)
    :short "Check if a list of expressions is well-formed."
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
         (n? (check-expression (car exprs) vartab funtab))
         ((when (errorp n?)) n?)
         ((unless (= n? 1))
          (error (list :multi-value-argument (expression-fix (car exprs)))))
         (n? (check-expression-list (cdr exprs) vartab funtab))
         ((when (errorp n?)) n?))
      (1+ n?))
    :measure (expression-list-count exprs))

  (define check-funcall ((call funcallp)
                         (vartab vartablep)
                         (funtab funtablep))
    :returns (results? nat-resultp)
    :short "Check if a function call is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We look up the function in the function table,
       which is passed as parameter.
       We ensure that the number of inputs matches,
       and we return the number of outputs.
       Each argument expression must return a single result."))
    (b* (((funcall call) call)
         (funty? (get-funtype call.name funtab))
         ((when (errorp funty?)) funty?)
         (n? (check-expression-list call.args vartab funtab))
         ((when (errorp n?)) n?)
         ((unless (= n? (funtype->in funty?)))
          (error (list :mismatched-formals-actuals
                       :required (funtype->in funty?)
                       :supplied n?))))
      (funtype->out funty?))
    :measure (funcall-count call))

  :verify-guards nil ; done below
  ///
  (verify-guards check-expression
    :hints
    (("Goal" :in-theory (enable acl2::natp-when-nat-resultp-and-not-errorp))))

  (fty::deffixequiv-mutual check-expressions/funcalls))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-functions-in-statement-list ((stmts statement-listp)
                                         (funtab funtablep))
  :returns (funtab? funtable-resultp)
  :short "Extend a function table with
          all the function definitions in a list of statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Scoping Rules],
     all the functions defined in a block are accessible in the whole block,
     even before they are defined in the block.
     Thus, just before checking a block,
     we extend the function table
     with all the function definitions in the block.
     The function table already contains the functions
     already accessible just before the block start,
     which are also accessible in the block,
     so extending the function table (as opposed to creating a new one)
     is appropriate here.")
   (xdoc::p
    "As soon as a duplication function is found, we stop with an error.")
   (xdoc::p
    "This ACL2 function is called on the list of statements
     contained in a block."))
  (b* (((when (endp stmts)) (funtable-fix funtab))
       (stmt (car stmts))
       ((unless (statement-case stmt :fundef))
        (add-functions-in-statement-list (cdr stmts) funtab))
       ((fundef fundef) (statement-fundef->get stmt))
       (funtab? (add-funtype fundef.name
                             (len fundef.inputs)
                             (len fundef.outputs)
                             funtab))
       ((when (errorp funtab?)) funtab?))
    (add-functions-in-statement-list (cdr stmts) funtab?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult vartable "variable tables")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-variable-single ((name identifierp)
                               (init expression-optionp)
                               (vartab vartablep)
                               (varvis identifier-setp)
                               (funtab funtablep))
  :returns (vartab? vartable-resultp)
  :short "Check if a single variable declaration is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee check-statement):
     see that function's documentation for background.")
   (xdoc::p
    "The name of the variable must be a well-formed identifier
     that is not visible (including accessible).
     The expression is checked if present,
     and it must return exactly one result."))
  (b* ((name (identifier-fix name))
       (init (expression-option-fix init))
       (wf? (check-identifier name))
       ((when (errorp wf?)) wf?)
       ((when (or (set::in name (vartable-fix vartab))
                  (set::in name (identifier-set-fix varvis))))
        (error (list :var-redeclare name)))
       ((when (not init)) (set::insert name (vartable-fix vartab)))
       (results? (check-expression init vartab funtab))
       ((when (errorp results?)) results?)
       ((unless (= results? 1))
        (error (list :declare-single-var-mismatch name results?))))
    (set::insert name (vartable-fix vartab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-variable-multi ((names identifier-listp)
                              (init funcall-optionp)
                              (vartab vartablep)
                              (varvis identifier-setp)
                              (funtab funtablep))
  :returns (vartab? vartable-resultp)
  :short "Check if a multiple variable declaration is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee check-statement):
     see that function's documentation for background.")
   (xdoc::p
    "The name of the variables must be well-formed identifiers
     that are not visible (including accessible).
     They must also be distinct and at least two.
     The expression is checked if present,
     and it must return the same number of results
     as the number of variables."))
  (b* ((names (identifier-list-fix names))
       (init (funcall-option-fix init))
       (wf? (check-identifier-list names))
       ((when (errorp wf?)) wf?)
       ((when (or (not (set::empty (set::intersect
                                    (set::mergesort names)
                                    (vartable-fix vartab))))
                  (not (set::empty (set::intersect
                                    (set::mergesort names)
                                    (identifier-set-fix varvis))))))
        (error (list :vars-redeclare names)))
       ((unless (no-duplicatesp-equal names))
        (error (list :duplicate-var-declare names)))
       ((unless (>= (len names) 2))
        (error (list :declare-zero-one-var names)))
       ((when (not init)) (set::union (set::mergesort names)
                                      (vartable-fix vartab)))
       (results? (check-funcall init vartab funtab))
       ((when (errorp results?)) results?)
       ((unless (= results? (len names)))
        (error (list :declare-multi-var-mismatch names results?))))
    (set::union (set::mergesort names) (vartable-fix vartab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-assign-single ((target pathp)
                             (value expressionp)
                             (vartab vartablep)
                             (funtab funtablep))
  :returns (wf? wellformed-resultp)
  :short "Check if a single assignment is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee check-expression),
     for now we require the path to be a singleton;
     see discussion there about non-singleton paths.")
   (xdoc::p
    "We check the expression, and and ensure that it returns one result.")
   (xdoc::p
    "This only depends on the (non-extended) variable table,
     which is unchanged and so we do not return an updated one."))
  (b* ((idents (path->get target))
       ((unless (and (consp idents)
                     (endp (cdr idents))
                     (set::in (car idents) (vartable-fix vartab))))
        (error (list :bad-path (path-fix target))))
       (results? (check-expression value vartab funtab))
       ((when (errorp results?)) results?)
       ((unless (= results? 1))
        (error (list :assign-single-var-mismatch (path-fix target) results?))))
    :wellformed)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-assign-multi ((targets path-listp)
                            (value funcallp)
                            (vartab vartablep)
                            (funtab funtablep))
  :returns (wf? wellformed-resultp)
  :short "Check if a multiple assignment is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Similarly to @(tsee check-expression),
     for now we require each path to be a singleton;
     see discussion there about non-singleton paths.")
   (xdoc::p
    "We check the expression, and and ensure that it returns
     a number of results equal to the number of variables.
     The variables must be two or more.")
   (xdoc::p
    "This only depends on the (non-extended) variable table,
     which is unchanged and so we do not return an updated one."))
  (b* (((unless (check-assign-multi-aux targets vartab))
        (error (list :bad-paths (path-list-fix targets))))
       ((unless (>= (len targets) 2))
        (error (list :assign-zero-one-path (path-list-fix targets))))
       (results? (check-funcall value vartab funtab))
       ((when (errorp results?)) results?)
       ((unless (= results? (len targets)))
        (error (list :assign-single-var-mismatch
                 (path-list-fix targets) results?))))
    :wellformed)
  :hooks (:fix)

  :prepwork
  ((define check-assign-multi-aux ((targets path-listp)
                                   (vartab vartablep))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp targets)
         (and (b* ((idents (path->get (car targets))))
                (and (consp idents)
                     (endp (cdr idents))
                     (set::in (car idents) (vartable-fix vartab))))
              (check-assign-multi-aux (cdr targets) vartab)))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-statements/blocks/cases/fundefs
  :short "Check if statements, blocks, cases, and function definitions
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are checked in the context of
     a variable table for visibile and accessible variable @('vartab'),
     a set of visible but inaccessible variables @('varvis'),
     and a function table @('funtab').
     The notions of `visible' and `accessible' are described
     in [Yul: Specification of Yul: Scoping Rules],
     and discussed in @(tsee vartable).
     Thus, all of the variables in @('vartab') and @('varvis')
     are actually visible (not only the ones in @('varvis')),
     but only the ones in @('vartab') are also accessible,
     while the ones in @('varvis') are visible but not accessible."))

  (define check-statement ((stmt statementp)
                           (vartab vartablep)
                           (varvis identifier-setp)
                           (funtab funtablep))
    :returns (vartab? vartable-resultp)
    :short "Check if a statement is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful,
       we return a possibly updated variable table.
       The table is updated only via variable declarations,
       while the other kinds of statements leave the table unchanged.
       The table may be changed in blocks nested in the statement,
       but those changes do not surface outside those blocks.
       Note also that the function table is not updated
       while checking function definition statements:
       as explained in @(tsee add-functions-in-block),
       the function definitions in a block are collected,
       and used to extend the function table,
       before processing the statements in a block.")
     (xdoc::p
      "We use separate ACL2 functions to check declarations and assignments,
       as their checking does not involve the mutual recursion.")
     (xdoc::p
      "For a function call used as a statement,
       we check the function call and ensure it returns no results.")
     (xdoc::p
      "For an @('if') statement, we check test, which must return one result,
       and we check the body block.
       Since the body is a block,
       the updated set of accessible variables is discarded.")
     (xdoc::p
      "For a @('for') statement, we first check the initialization block.
       We use the updated set of accessible variables
       to check the other components,
       because the scope of the initialization block
       extends to the whole statement, as explained
       in [Yul: Specification of Yul: Scoping Rules].
       The test must return one result."))
    (statement-case
     stmt
     :block
     (b* ((vartab? (check-block stmt.get vartab varvis funtab))
          ((when (errorp vartab?)) vartab?))
       (vartable-fix vartab))
     :variable-single
     (check-variable-single stmt.name stmt.init vartab varvis funtab)
     :variable-multi
     (check-variable-multi stmt.names stmt.init vartab varvis funtab)
     :assign-single
     (b* ((wf? (check-assign-single stmt.target stmt.value vartab funtab))
          ((when (errorp wf?)) wf?))
       (vartable-fix vartab))
     :assign-multi
     (b* ((wf? (check-assign-multi stmt.targets stmt.value vartab funtab))
          ((when (errorp wf?)) wf?))
       (vartable-fix vartab))
     :funcall
     (b* ((results? (check-funcall stmt.get vartab funtab))
          ((when (errorp results?)) results?)
          ((unless (= results? 0))
           (error (list :discarded-values stmt.get))))
       (vartable-fix vartab))
     :if
     (b* ((results? (check-expression stmt.test vartab funtab))
          ((when (errorp results?)) results?)
          ((unless (= results? 1))
           (error (list :multi-valued-if-test stmt.test)))
          (vartab? (check-block stmt.body vartab varvis funtab))
          ((when (errorp vartab?)) vartab?))
       (vartable-fix vartab))
     :for
     (b* ((vartab-init? (check-block stmt.init vartab varvis funtab))
          ((when (errorp vartab-init?)) vartab-init?)
          (results? (check-expression stmt.test vartab-init? funtab))
          ((when (errorp results?)) results?)
          ((unless (= results? 1))
           (error (list :multi-valued-for-test stmt.test)))
          (vartab-update? (check-block stmt.update
                                       vartab-init?
                                       varvis
                                       funtab))
          ((when (errorp vartab-update?)) vartab-update?)
          (vartab-body? (check-block stmt.body
                                     vartab-init?
                                     varvis
                                     funtab))
          ((when (errorp vartab-body?)) vartab-body?))
       (vartable-fix vartab))
     :switch (error :todo)
     :leave (error :todo)
     :break (error :todo)
     :continue (error :todo)
     :fundef (error :todo))
    :measure (statement-count stmt))

  (define check-block ((block blockp)
                       (vartab vartablep)
                       (varvis identifier-setp)
                       (funtab funtablep))
    :returns (vartab? vartable-resultp)
    :short "Check if a block is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we just check the statements in the block,
       but this will be extended soon."))
    (check-statement-list (block->statements block)
                          vartab
                          varvis
                          funtab)
    :measure (block-count block))

  (define check-statement-list ((stmts statement-listp)
                                (vartab vartablep)
                                (varvis identifier-setp)
                                (funtab funtablep))
    :returns (vartab? vartable-resultp)
    :short "Check if a list of statements is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the statements, one after the other,
       threading through the set of accessible variables."))
    (b* (((when (endp stmts)) (vartable-fix vartab))
         (vartab? (check-statement (car stmts) vartab varvis funtab))
         ((when (errorp vartab?)) vartab?))
      (check-statement-list (cdr stmts) vartab? varvis funtab))
    :measure (statement-list-count stmts))

  :verify-guards nil ; done below
  ///
  (verify-guards check-statement
    :hints
    (("Goal"
      :in-theory
      (enable vartablep-when-vartable-resultp-and-not-errorp))))

  (fty::deffixequiv-mutual check-statements/blocks/cases/fundefs))
