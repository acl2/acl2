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
     not in the variable tables defined here;
     see @(tsee add-var)."))
  :elt-type identifier
  :elementp-of-nil nil
  :pred vartablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult vartable "variable tables")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-var ((var identifierp) (vartab vartablep))
  :returns (yes/no booleanp)
  :short "Check if a variable is in a variable table."
  (set::in (identifier-fix var) (vartable-fix vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var ((var identifierp) (vartab vartablep) (varvis identifier-setp))
  :returns (vartab? vartable-resultp)
  :short "Add a variable to a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the variable and the variable table,
     this ACL2 function also takes as argument the set of variables
     that are visible but not accessible.
     The reason is that a new variable is allowed only if
     it does not shadow any visible variable, whether accessible or not.
     All of the variables in @('vartab') and @('varvis')
     are actually visible (not only the ones in @('varvis')),
     but only the ones in @('vartab') are also accessible,
     while the ones in @('varvis') are visible but not accessible."))
  (b* ((var (identifier-fix var))
       (vartab (vartable-fix vartab))
       (varvis (identifier-set-fix varvis)))
    (if (or (set::in var vartab)
            (set::in var varvis))
        (error (list :duplicate-variable var))
      (set::insert var vartab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-vars ((vars identifier-listp)
                  (vartab vartablep)
                  (varvis identifier-setp))
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
       (vartab? (add-var (car vars) vartab varvis))
       ((when (errorp vartab?)) vartab?))
    (add-vars (cdr vars) vartab? varvis))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-vars-inaccessible ((vartab vartablep) (varvis identifier-setp))
  :returns (new-varvis identifier-setp)
  :short "Add the variables from the variable table
          to the set of visible but inaccessible variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee add-var) for a description of
     what @('vartab') and @('varvis') represent.
     This is used just before checking a function definition.
     Since a function body cannot access
     variables declared outside the function,
     but those variables are still visible and cannot be shadowed,
     we add the variables in the variable table
     to the set of visible but inaccessible variables."))
  (set::union (vartable-fix vartab) (identifier-set-fix varvis))
  :prepwork
  ((defrulel lemma
     (implies (vartablep x)
              (identifier-setp x))
     :enable (identifier-setp vartablep)))
  :hooks (:fix))

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

(define check-path ((path pathp) (vartab vartablep))
  :returns (wf? wellformed-resultp)
  :short "Check if a path is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "As a structural condition,
     a path must consists of one or more well-formed identifiers.
     More importantly, it must refer to an existing variable.
     It is not yet clear how paths with more than one identifier
     come about in generic Yul:
     variable declarations are for single identifiers
     (whether one single identifier,
     or two or more single identifiers),
     so it seems that singleton paths would always suffice to reference them
     in expressions and statements.
     For now we only regard singleton paths as well-formed,
     provided they are part of the accessible variables.")
   (xdoc::p
    "We may move the non-emptiness requirement
     into an invariant of @(tsee path),
     but for now we state it as part of the static semantics."))
  (b* ((idens (path->get path))
       ((unless (consp idens))
        (error (list :empty-path (path-fix path))))
       (wf? (check-identifier-list idens))
       ((when (errorp wf?)) wf?)
       ((unless (endp (cdr idens)))
        (error (list :non-singleton-path (path-fix path))))
       (var (car idens))
       ((unless (check-var var vartab))
        (error (list :variable-not-found var))))
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
      "A path always yields one result.")
     (xdoc::p
      "A literal's well-formedness is independent from the accessible variables.
       A literal always returns one result."))
    (expression-case
     expr
     :path (b* ((wf? (check-path expr.get vartab))
                ((when (errorp wf?)) wf?))
             1)
     :literal (b* ((wf? (check-literal expr.get))
                   ((when (errorp wf?)) wf?))
                1)
     :funcall (check-funcall expr.get vartab funtab))
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
       (vartab? (add-var name vartab varvis))
       ((when (errorp vartab?)) vartab?)
       ((when (not init)) vartab?)
       (results? (check-expression init vartab funtab))
       ((when (errorp results?)) results?)
       ((unless (= results? 1))
        (error (list :declare-single-var-mismatch name results?))))
    vartab?)
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
       (vartab? (add-vars names vartab varvis))
       ((when (errorp vartab?)) vartab?)
       ((unless (>= (len names) 2))
        (error (list :declare-zero-one-var names)))
       ((when (not init)) vartab?)
       (results? (check-funcall init vartab funtab))
       ((when (errorp results?)) results?)
       ((unless (= results? (len names)))
        (error (list :declare-multi-var-mismatch names results?))))
    vartab?)
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
  (b* ((wf? (check-path target vartab))
       ((when (errorp wf?)) wf?)
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
  (b* ((wf? (check-assign-multi-aux targets vartab))
       ((when (errorp wf?)) wf?)
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
     :returns (wf? wellformed-resultp)
     :parents nil
     (b* (((when (endp targets)) :wellformed)
          (wf? (check-path (car targets) vartab))
          ((when (errorp wf?)) wf?))
       (check-assign-multi-aux (cdr targets) vartab))
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
     Also see @(tsee add-var) about @('vartab') and @('varvis').")
   (xdoc::p
    "In order to check that a @('leave') statement is only used in a function,
     according to [Yul: Specification of Yul: Restrictions on the Grammar],
     the context also includes a flag indicating
     whether we are in a function or not.
     This flag may be initially unset
     (e.g. in the top-level code block of a Yul object
     [Yul: Specification of Yul Object]),
     but then once it is set, it stays set as we go into the code.")
   (xdoc::p
    "We also need a flag indicating whether
     we are in a loop's initialization block.
     This is so we can ensure that no functions are defined in the block
     [Yul: Specification of Yul: Restrictions on the Grammar].
     The flag may be initially unset
     (e.g. in the top-level code block of a Yul object
     [Yul: Specification of Yul Object]),
     but it is set as soon as we go into a loop initialization block.
     From there, it always stays set as we go more inside the code;
     even if we encounter an inner loop,
     and eventually we go into its update or body block,
     we are still in the initialization block of the outer loop,
     and still no function definitions are allowed,
     and thus we need to keep that flag set.
     Note that, before going into a function definition's body block,
     we ensure that the flag is unset
     (i.e. we ensure that no functions are defined in the block),
     so we preserve its value also in this case.
     In summary, the flag is unconditionally set
     when entering a loop initialization block,
     and always preserved whenever we go into inner blocks.
     This flag is not passed to the ACL2 function
     that checks function definitions,
     because as explained above the flag must be unset
     in order for the function definition to be allowed,
     and so it being unset carries no information.")
   (xdoc::p
    "We also need a flag indicating whether
     we are in a loop's body block.
     Even though the preceding sentence is phrased analogously to
     the sentence about the loop initialization block above,
     this flag is actually treated differently.
     This flag serves to determine whether
     @('break') and @('continue') are allowed,
     which is the case if we are in a loop block or sub-blocks,
     but not in initialization or update blocks of inner loops
     [Yul: Specification of Yul: Restrictions on the Grammar].
     This means that, unlike the loop initialization block flag,
     this flag is unset when we enter a loop initialization or update block,
     it is set when we enter a loop body block,
     and is preserved when entering other kinds of blocks.
     The flag is not passed to the ACL2 function
     that checks function definitions,
     because as we enter a function body we are not in a loop,
     i.e. the flag is implicitly unset there."))

  (define check-statement ((stmt statementp)
                           (vartab vartablep)
                           (varvis identifier-setp)
                           (funtab funtablep)
                           (in-function booleanp)
                           (in-loop-init booleanp)
                           (in-loop-body booleanp))
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
       as explained in @(tsee add-functions-in-statement-list),
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
       the updated variable and function tables are discarded.")
     (xdoc::p
      "For a @('for') statement, we first check the initialization block.
       We use the updated variable table to check the other components,
       because the scope of the initialization block
       extends to the whole statement, as explained
       in [Yul: Specification of Yul: Scoping Rules].")
     (xdoc::p
      "For a @('switch') statement,
       we check the expression, ensuring it returns a single result.
       We ensure that ther is at least one (literal or default) case
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
       For now we check syntactic difference,
       but we may need to tighten that to semantic difference.
       Every (literal or default) block is then checked,
       along with the literals.")
     (xdoc::p
      "For a @('leave') statement,
       we ensure that we are in a function, as indicated by the flag.")
     (xdoc::p
      "For a function definition, we ensure that we are not
       in a loop initialization block, as indicated by the flag.
       Since a function body cannot access
       variables declared outside the function,
       we make the variables in the variable table inaccessible,
       and then we use a separate mutually recursive ACL2 function
       that checks function definition.
       That ACL2 function returns nothing in case of success,
       so here we return the outside variable table unchanged:
       a function definition does not modify the variable table."))
    (statement-case
     stmt
     :block
     (b* ((vartab? (check-block stmt.get
                                vartab
                                varvis
                                funtab
                                in-function
                                in-loop-init
                                in-loop-body))
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
          (vartab? (check-block stmt.body
                                vartab
                                varvis
                                funtab
                                in-function
                                in-loop-init
                                in-loop-body))
          ((when (errorp vartab?)) vartab?))
       (vartable-fix vartab))
     :for
     (b* ((vartab-init? (check-block stmt.init
                                     vartab
                                     varvis
                                     funtab
                                     in-function
                                     t
                                     nil))
          ((when (errorp vartab-init?)) vartab-init?)
          (results? (check-expression stmt.test vartab-init? funtab))
          ((when (errorp results?)) results?)
          ((unless (= results? 1))
           (error (list :multi-valued-for-test stmt.test)))
          (vartab-update? (check-block stmt.update
                                       vartab-init?
                                       varvis
                                       funtab
                                       in-function
                                       in-loop-init
                                       nil))
          ((when (errorp vartab-update?)) vartab-update?)
          (vartab-body? (check-block stmt.body
                                     vartab-init?
                                     varvis
                                     funtab
                                     in-function
                                     in-loop-init
                                     t))
          ((when (errorp vartab-body?)) vartab-body?))
       (vartable-fix vartab))
     :switch
     (b* ((results? (check-expression stmt.target vartab funtab))
          ((when (errorp results?)) results?)
          ((unless (= results? 1))
           (error (list :multi-valued-switch-target stmt.target)))
          ((unless (or (consp stmt.cases) stmt.default))
           (error (list :no-cases-in-switch (statement-fix stmt))))
          ((unless (no-duplicatesp-equal (swcase-list->value-list stmt.cases)))
           (error (list :duplicate-switch-cases (statement-fix stmt)))))
       (error :todo-continue))
     :leave
     (if in-function
         (vartable-fix vartab)
       (error (list :leave-outside-function)))
     :break
     (if in-loop-body
         (vartable-fix vartab)
       (error :break-not-in-loop-body))
     :continue
     (if in-loop-body
         (vartable-fix vartab)
       (error :continue-not-in-loop-body))
     :fundef
     (if in-loop-init
         (error :fundef-in-loop-init)
       (b* ((varvis (make-vars-inaccessible vartab varvis))
            (wf? (check-fundef stmt.get varvis funtab))
            ((when (errorp wf?)) wf?))
         (vartable-fix vartab))))
    :measure (statement-count stmt))

  (define check-statement-list ((stmts statement-listp)
                                (vartab vartablep)
                                (varvis identifier-setp)
                                (funtab funtablep)
                                (in-function booleanp)
                                (in-loop-init booleanp)
                                (in-loop-body booleanp))
    :returns (vartab? vartable-resultp)
    :short "Check if a list of statements is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the statements, one after the other,
       threading through the variable table."))
    (b* (((when (endp stmts)) (vartable-fix vartab))
         (vartab? (check-statement (car stmts)
                                   vartab
                                   varvis
                                   funtab
                                   in-function
                                   in-loop-init
                                   in-loop-body))
         ((when (errorp vartab?)) vartab?))
      (check-statement-list (cdr stmts)
                            vartab?
                            varvis
                            funtab
                            in-function
                            in-loop-init
                            in-loop-body))
    :measure (statement-list-count stmts))

  (define check-block ((block blockp)
                       (vartab vartablep)
                       (varvis identifier-setp)
                       (funtab funtablep)
                       (in-function booleanp)
                       (in-loop-init booleanp)
                       (in-loop-body booleanp))
    :returns (vartab? vartable-resultp)
    :short "Check if a block is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "If successful, return a possibly updated variable table.
       This is normally discarded by the caller,
       because the updates are almost always only visible in the block itself,
       except for the initialization block of a @('for') statement,
       which is treated specially as explained in
       [Yul: Specification of Yul: Scoping Rules].")
     (xdoc::p
      "As explained in @(tsee add-functions-in-statement-list),
       all the functions defined in a block are visible in the whole block,
       so we first collect them from the statements that form the block,
       updating the function table with them,
       and then we check the statements that form the block."))
    (b* ((stmts (block->statements block))
         (funtab? (add-functions-in-statement-list stmts funtab))
         ((when (errorp funtab?)) funtab?)
         (vartab? (check-statement-list stmts
                                        vartab
                                        varvis
                                        funtab?
                                        in-function
                                        in-loop-init
                                        in-loop-body))
         ((when (errorp vartab?)) vartab?))
      vartab?)
    :measure (block-count block))

  (define check-swcase ((case swcasep)
                        (vartab vartablep)
                        (varvis identifier-setp)
                        (funtab funtablep)
                        (in-function booleanp)
                        (in-loop-init booleanp)
                        (in-loop-body booleanp))
    :returns (wf? wellformed-resultp)
    :short "Check if a case is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check its literal and its block.
       We do not need to return anything in case of success."))
    (b* (((swcase case) case)
         (wf? (check-literal case.value))
         ((when (errorp wf?)) wf?)
         (vartab? (check-block case.body
                               vartab
                               varvis
                               funtab
                               in-function
                               in-loop-init
                               in-loop-body))
         ((when (errorp vartab?)) vartab?))
      :wellformed)
    :measure (swcase-count case))

  (define check-swcase-list ((cases swcase-listp)
                             (vartab vartablep)
                             (varvis identifier-setp)
                             (funtab funtablep)
                             (in-function booleanp)
                             (in-loop-init booleanp)
                             (in-loop-body booleanp))
    :returns (wf? wellformed-resultp)
    :short "Check if a list of cases is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "We just check each case in turn."))
    (b* (((when (endp cases)) :wellformed)
         (wf? (check-swcase (car cases)
                            vartab
                            varvis
                            funtab
                            in-function
                            in-loop-init
                            in-loop-body))
         ((when (errorp wf?)) wf?))
      (check-swcase-list (cdr cases)
                         vartab
                         varvis
                         funtab
                         in-function
                         in-loop-init
                         in-loop-body))
    :measure (swcase-list-count cases))

  (define check-fundef ((fundef fundefp)
                        (varvis identifier-setp)
                        (funtab funtablep))
    :returns (wf? wellformed-resultp)
    :short "Check if a function definition is well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "This ACL2 function takes as input less contextual information
       than its mutually recursive companions.
       The reason is that such contextual information is always set
       when a funtion definition is checked.
       In particular, as explained in @(tsee make-vars-inaccessible),
       there is no variable table to pass.
       The flags saying whether we are
       in a function
       or in a loop initialization block
       or in a loop body block
       are also not passed because it is always the case that
       we are in a function and we are not in any loop block initially.")
     (xdoc::p
      "This ACL2 function does not need to return anything.
       Any variable table internal to the function's body
       does not surface outside the function's body.
       Also recall that the function definition itself
       is added to the function table prior to checking it;
       see @(tsee add-functions-in-statement-list).")
     (xdoc::p
      "To check the function definition, we construct an initial variable table
       from the inputs and outputs of the function.
       Note that the construction will detect and reject any duplicates.
       Then we check the function's body."))
    (b* (((fundef fundef) fundef)
         (vartab? (add-vars (append fundef.inputs fundef.outputs)
                            nil
                            varvis))
         ((when (errorp vartab?)) vartab?)
         (vartab? (check-block fundef.body
                               vartab?
                               varvis
                               funtab
                               t
                               nil
                               nil))
         ((when (errorp vartab?)) vartab?))
      :wellformed)
    :measure (fundef-count fundef))

  :verify-guards nil ; done below
  ///
  (verify-guards check-statement
    :hints
    (("Goal"
      :in-theory
      (enable vartablep-when-vartable-resultp-and-not-errorp))))

  (fty::deffixequiv-mutual check-statements/blocks/cases/fundefs))
