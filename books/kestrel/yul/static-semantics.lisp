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

(defines check-expression
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
     provided they are part of the current set of accessible variables,
     passed as parameter.
     These are just a set for now because
     there is no type information associated to variables (cf. abstract syntax),
     but we may extend that to an omap from variables to types in the future.
     A path always yields one result, so we return 1.")
   (xdoc::p
    "A literal's well-formedness is independent from the accessible variables.
     A literal always returns one result, so we return 1.")
   (xdoc::p
    "For a function call, we look up the function in the function table,
     which is passed as parameter.
     We ensure that the number of inputs matches,
     and we return the number of outputs.
     Each argument expression must return a single result.
     Note that while the function @(tsee check-expression)
     returns the number of values that the expression yields,
     the function @(tsee check-expression-list)
     returns the number of expressions,
     checking that they are all single-valued."))

  (define check-expression ((expr expressionp)
                            (var-acc identifier-setp)
                            (funtab funtablep))
    :returns (results? nat-resultp)
    (expression-case
     expr
     :path
     (if (and (consp expr.get)
              (not (consp (cdr expr.get)))
              (set::in (car expr.get) (identifier-set-fix var-acc)))
         1
       (error (list :bad-path expr.get)))
     :literal
     (b* ((wf? (check-literal expr.get))
          ((when (errorp wf?)) wf?))
       1)
     :funcall
     (check-funcall expr.get var-acc funtab))
    :measure (expression-count expr))

  (define check-expression-list ((exprs expression-listp)
                                 (var-acc identifier-setp)
                                 (funtab funtablep))
    :returns (number? nat-resultp)
    (b* (((when (endp exprs)) 0)
         (n? (check-expression (car exprs) var-acc funtab))
         ((when (errorp n?)) n?)
         ((unless (= n? 1))
          (error (list :multi-value-argument (expression-fix (car exprs)))))
         (n? (check-expression-list (cdr exprs) var-acc funtab))
         ((when (errorp n?)) n?))
      (1+ n?))
    :measure (expression-list-count exprs))

  (define check-funcall ((call funcallp)
                         (var-acc identifier-setp)
                         (funtab funtablep))
    :returns (results? nat-resultp)
    (b* (((funcall call) call)
         (funty? (get-funtype call.name funtab))
         ((when (errorp funty?)) funty?)
         (n? (check-expression-list call.args var-acc funtab))
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

  (fty::deffixequiv-mutual check-expression))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-functions-in-block ((block blockp) (funtab funtablep))
  :returns (funtab? funtable-resultp)
  :short "Extend a function table with
          all the function definitions in a block."
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
    "As soon as a duplication function is found, we stop with an error."))
  (b* (((when (endp block)) (funtable-fix funtab))
       (stmt (car block))
       ((unless (statement-case stmt :fundef))
        (add-functions-in-block (cdr block) funtab))
       ((fundef fundef) (statement-fundef->get stmt))
       (funtab? (add-funtype fundef.name
                             (len fundef.inputs)
                             (len fundef.outputs)
                             funtab))
       ((when (errorp funtab?)) funtab?))
    (add-functions-in-block (cdr block) funtab?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add checking of statements etc.
