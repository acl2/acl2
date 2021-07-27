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

(define check-identifier ((iden identifierp))
  :returns (yes/no booleanp)
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
    (and (consp chars)
         (acl2::alpha/uscore/dollar-char-p (car chars))
         (acl2::alpha/digit/uscore/dollar-charlist-p (cdr chars))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist check-identifier-list (x)
  :guard (identifier-listp x)
  :short "Check if all the identifiers in a list are well-formed."
  (check-identifier x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-path ((path pathp))
  :returns (yes/no booleanp)
  :short "Check if a path is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must consists of one or more well-formed identifiers.")
   (xdoc::p
    "We may move the non-emptiness requirement
     into an invariant of @(tsee path),
     but for now we state it as part of the static semantics."))
  (b* ((idens (path->get path)))
    (and (consp idens)
         (check-identifier-list idens)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-literal ((lit literalp))
  :returns (yes/no booleanp)
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
  (literal-case
   lit
   :boolean t
   :dec-number (< lit.get
                  (expt 2 256))
   :hex-number (< (str::hex-digit-chars-value (hex-digit-list->chars lit.get))
                  (expt 2 256))
   :string (<= (len lit.content) 32)
   :hex-string (and (< 0 (len lit.content))
                    (<= (len lit.content) 32)))
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

(fty::defoption funtype-option
  funtype
  :short "Fixtype of optional function types."
  :pred funtype-optionp)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-funtype ((name identifierp) (funtab funtablep))
  :returns (funty? funtype-optionp
                   :hints (("Goal" :in-theory (enable funtype-optionp))))
  :short "Look up a function in a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lookup is by name.
     If a function is found, we return its type.
     Otherwise we return @('nil')."))
  (cdr (omap::in (identifier-fix name) (funtable-fix funtab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-expression
  :short "Check if an expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return the number of values that the expression yields.
     Otherwise, return @('nil').")
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

  (define check-expression ((e expressionp)
                            (var-acc identifier-setp)
                            (funtab funtablep))
    :returns (results acl2::maybe-natp)
    (expression-case
     e
     :path
     (and (consp e.get)
          (not (consp (cdr e.get)))
          (set::in (car e.get) (identifier-set-fix var-acc))
          1)
     :literal
     (and (check-literal e.get)
          1)
     :funcall
     (check-funcall e.get var-acc funtab))
    :measure (expression-count e))

  (define check-expression-list ((es expression-listp)
                                 (var-acc identifier-setp)
                                 (funtab funtablep))
    :returns (number acl2::maybe-natp)
    (b* (((when (endp es)) 0)
         (n? (check-expression (car es) var-acc funtab))
         ((unless (equal n? 1)) nil)
         (n? (check-expression-list (cdr es) var-acc funtab))
         ((unless (natp n?)) nil))
      (1+ n?))
    :measure (expression-list-count es))

  (define check-funcall ((call funcallp)
                         (var-acc identifier-setp)
                         (funtab funtablep))
    :returns (results acl2::maybe-natp)
    (b* (((funcall call) call)
         (funty? (get-funtype call.name funtab))
         ((unless (funtypep funty?)) nil)
         (n? (check-expression-list call.args var-acc funtab))
         ((unless (equal n? (funtype->in funty?))) nil))
      (funtype->out funty?))
    :measure (funcall-count call))

  ///

  (fty::deffixequiv-mutual check-expression))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add checking of statements etc.
