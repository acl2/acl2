; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "../library-extensions/osets")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/hex-digit-char" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (language)
  :short "Abstract syntax of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an abstract syntax of Yul based on its "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ".")
   (xdoc::p
    "The abstract syntax defined here is fairly close to the concrete syntax.
     The reason for this closeness is to reduce incidental differences
     between the code before and after a transformation,
     to facilitate inspection and debugging.
     (Although our formalization of Yul stands on its own,
     a major motivation for it is to formalize and verify Yul transformations.)
     In some cases our abstract syntax may be broader than the concrete syntax,
     to keep the definition of the abstract syntax slightly simpler;
     the important thing is that all the concrete syntax
     is representable in abstract syntax."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod identifier
  :short "Fixtype of identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "An identifier is a sequence of characters satisfying certain conditions.
     For now we use an ACL2 string, wrapped in a one-field product type.
     ACL2 strings suffice to represent all identifiers, and more.
     In the future we may add restrictions on the string
     to be a true identifier as defined in the concrete syntax."))
  ((get string))
  :tag :identifier
  :pred identifierp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-result
  :short "Fixtype of errors and identifiers."
  :ok identifier
  :pred identifier-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption identifier-option
  identifier
  :short "Fixtype of optional identifiers."
  :pred identifier-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist identifier-list
  :short "Fixtype of lists of identifiers."
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-list-result
  :short "Fixtype of errors and lists of identifiers."
  :ok identifier-list
  :pred identifier-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset identifier-set
  :short "Fixtype of sets of identifiers."
  :elt-type identifier
  :elementp-of-nil nil
  :pred identifier-setp

  ///

  (defrule identifier-setp-of-mergesort
    (implies (true-listp x)
             (equal (identifier-setp (set::mergesort x))
                    (identifier-listp x)))
    :enable set::mergesort)

  (defrule identifier-setp-of-list-insert
    (implies (and (identifier-listp list)
                  (identifier-setp set))
             (identifier-setp (set::list-insert list set)))
    :enable set::list-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-set-result
  :short "Fixtype of errors and sets of identifiers."
  :ok identifier-set
  :pred identifier-set-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap identifier-identifier-map
  :short "Fixtype of maps from identifiers to identifiers."
  :key-type identifier
  :val-type identifier
  :pred identifier-identifier-mapp

  ///

  (defrule identifier-setp-of-keys-when-identifier-identifier-mapp
    (implies (identifier-identifier-mapp m)
             (identifier-setp (omap::keys m)))
    :enable omap::keys)

  (defrule identifier-setp-of-values-when-identifier-identifier-mapp
    (implies (identifier-identifier-mapp m)
             (identifier-setp (omap::values m)))
    :enable omap::values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-identifier-map-result
  :short "Fixtype of errors and maps from identifiers to identifiers."
  :ok identifier-identifier-map
  :pred identifier-identifier-map-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist identifier-identifier-alist
  :short "Fixtype of alists from identifiers to identifiers."
  :key-type identifier
  :val-type identifier
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred identifier-identifier-alistp

  ///

  (defruled identifier-listp-of-strip-cars-when-identifier-identifier-alistp
    (implies (identifier-identifier-alistp alist)
             (identifier-listp (strip-cars alist))))

  (defruled identifier-listp-of-strip-cdrs-when-identifier-identifier-alistp
    (implies (identifier-identifier-alistp alist)
             (identifier-listp (strip-cdrs alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod path
  :short "Fixtype of paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "A path is a non-empty sequence of identifiers, separated by dots.
     Here we define a path as a list of identifiers,
     wrapped in a one-field product type.
     In the future we may add an invariant that the list is not empty.")
   (xdoc::p
    "Representing paths as a wrapped list of identifiers,
     as opposed to just a list of identifiers,
     lets us make a finer distinction between
     lists of identifiers representing paths (when wrapped),
     and just lists of identifiers that may be used for other purposes.
     In other words, the wrapping conveys that it is a path,
     and that the identifiers in the list are separated by dots
     (if written in concrete syntax)."))
  ((get identifier-list))
  :tag :path
  :pred pathp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult path-result
  :short "Fixtype of errors and paths."
  :ok path
  :pred path-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist path-list
  :short "Fixtype of lists of paths."
  :elt-type path
  :true-listp t
  :elementp-of-nil nil
  :pred path-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-digit
  :short "Fixtype of hex digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "We wrap a hexadecimal digit character into a one-field product.
     We could perhaps use @(tsee hex-digit-char) directly here,
     but the name @('hex-digit') is slightly shorter,
     and unambiguous in the Yul context."))
  ((get hex-digit-char))
  :tag :hex-digit
  :pred hex-digitp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist hex-digit-list
  :short "Fixtype of lists of hex digits."
  :elt-type hex-digit
  :true-listp t
  :elementp-of-nil nil
  :pred hex-digit-listp)

;;;;;;;;;;;;;;;;;;;;

(std::defprojection hex-digit-list->chars ((x hex-digit-listp))
  :returns (chars str::hex-digit-char-list*p)
  :short "Extract the characters from a list of hex digits."
  (hex-digit->get x)
  ///
  (fty::deffixequiv hex-digit-list->chars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-pair
  :short "Fixtype of pairs of hex digits."
  ((1st hex-digit)
   (2nd hex-digit))
  :tag :hex-pair
  :pred hex-pairp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-quad
  :short "Fixtype of quadruples of hex digits."
  ((1st hex-digit)
   (2nd hex-digit)
   (3rd hex-digit)
   (4th hex-digit))
  :tag :hex-quad
  :pred hex-quadp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum escape
  :short "Fixtype of escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the escapes used in string literals.
     They are all preceded by backslash,
     which we do not need to represent explicitly in abstract syntax.
     There are simple escapes consisting of
     a single character just after the backslash,
     as well as escapes consisting of @('x') (not explicitly represented)
     followed by a pair of hex digits,
     and Unicode escapes consisting of @('u') (not explicitly represented)
     followed by a quadruple of hex digits.
     Thus in this abstract syntax of escapes we capture
     all the information from the concrete syntax."))
  (:single-quote ())
  (:double-quote ())
  (:backslash ())
  (:letter-n ())
  (:letter-r ())
  (:letter-t ())
  (:line-feed ())
  (:carriage-return ())
  (:x ((get hex-pair)))
  (:u ((get hex-quad)))
  :pred escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult escape-result
  :short "Fixtype of errors and escapes."
  :ok escape
  :pred escape-resultp
  :prepwork ((local (in-theory (enable escape-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum string-element
  :short "Fixtype of string elements."
  :long
  (xdoc::topstring
   (xdoc::p
    "A string literal consists of a sequence of
     printable ASCII characters and escapes:
     these are the string elements we define here.
     We use ACL2 characters for the former,
     which can represent all the printable ASCII characters and more;
     We might restrict the range of characters at some point."))
  (:char ((get character)))
  (:escape ((get escape)))
  :pred string-elementp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult string-element-result
  :short "Fixtype of errors and string elements."
  :ok string-element
  :pred string-element-resultp
  :prepwork ((local (in-theory (enable string-element-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist string-element-list
  :short "Fixtype of string elements."
  :elt-type string-element
  :true-listp t
  :elementp-of-nil nil
  :pred string-element-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult string-element-list-result
  :short "Fixtype of errors and lists of string elements."
  :ok string-element-list
  :pred string-element-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod plain-string
  :short "Fixtype of plain strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as literals; they are the regular, non-hex strings.
     We call them `plain' to clearly distinguish them from hex strings.")
   (xdoc::p
    "We represent a plain string as a list of elements,
     plus a flag saying whether
     the surrounding quotes are double or not (i.e. single).
     This captures the full concrete syntax information."))
  ((content string-element-list)
   (double-quote-p bool))
  :tag :plain-string
  :pred plain-stringp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-string-rest-element
  :short "Fixtype of elements of hex strings after the first one."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar defines the content of a hex string
     as consisting of zero or more pairs of hex digits,
     where the pairs may be optionally separated by single underscores.
     In order to retain that concrete syntax information in the abstract syntax,
     this fixtype captures the notion of
     something of the form @('_hh') or @('hh'),
     where each @('h') is a (potentially different) hex digit.
     A value of this fixtype represents an element of a hex string,
     but not the first element, which may not be preceded by underscore."))
  ((uscorep bool)
   (pair hex-pair))
  :tag :hex-string-rest-element
  :pred hex-string-rest-elementp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist hex-string-rest-element-list
  :short "Fixtype of lists of elements of hex strings after the first one."
  :elt-type hex-string-rest-element
  :true-listp t
  :elementp-of-nil nil
  :pred hex-string-rest-element-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-string-content
  :short "Fixtype of contents of hex strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a hex string is not empty,
     it contains one or more pairs of hex digits,
     optionally separated by single underscores.
     This fixtype captures this non-empty content:
     it consists of the starting pair of hex digit,
     and the list of zero or more remaining pairs of hex digits,
     each of which is optionally preceded by underscore."))
  ((first hex-pair)
   (rest hex-string-rest-element-list))
  :tag :hex-string-content
  :pred hex-string-contentp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption hex-string-content-option
  hex-string-content
  :short "Fixtype of optional contents of hex strings."
  :pred hex-string-content-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod hex-string
  :short "Fixtype of hex strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "We represent a hex string as consisting of
     an optional content (absent if the string is empty)
     and a boolean flag saying whether
     the surrounding quotes are double or not (i.e. single)."))
  ((content hex-string-content-option)
   (double-quote-p bool))
  :tag :hex-string
  :pred hex-stringp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum literal
  :short "Fixtype of literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Boolean literals are straightforward.")
   (xdoc::p
    "We represent a decimal literal as a natural number.
     Since the Yul grammar requires no leading zeros in decimal numbers,
     a natural number captures the full information.")
   (xdoc::p
    "We represent a hexadecimal literal as a list of hex digits,
     which therefore captures full information:
     leading zeros and capitalization of the letters.")
   (xdoc::p
    "We represent plain and hex strings
     as described in @(tsee plain-string) and @(tsee hex-string)."))
  (:boolean ((get bool)))
  (:dec-number ((get nat)))
  (:hex-number ((get hex-digit-list)))
  (:plain-string ((get plain-string)))
  (:hex-string ((get hex-string)))
  :pred literalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption literal-option
  literal
  :short "Fixtype of optional literals."
  :pred literal-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult literal-result
  :short "Fixtype of errors and literals."
  :ok literal
  :pred literal-resultp
  :prepwork ((local (in-theory (enable literal-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist literal-list
  :short "Fixtype of lists of literals."
  :elt-type literal
  :true-listp t
  :elementp-of-nil nil
  :pred literal-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes expressions/funcalls
  :short "Fixtypes of expressions and function calls."

  (fty::deftagsum expression
    :short "Fixtype of expressions."
    (:path ((get path)))
    (:literal ((get literal)))
    (:funcall ((get funcall)))
    :pred expressionp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist expression-list
    :short "Fixtype of lists of expressions."
    :elt-type expression
    :true-listp t
    :elementp-of-nil nil
    :pred expression-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod funcall
    :short "Fixtype of function calls."
    ((name identifier)
     (args expression-list))
    :tag :funcall
    :pred funcallp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption expression-option
  expression
  :short "Fixtype of optional expressions."
  :pred expression-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expression-result
  :short "Fixtype of errors and expressions."
  :ok expression
  :pred expression-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption funcall-option
  funcall
  :short "Fixtype of optional function calls."
  :pred funcall-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funcall-result
  :short "Fixtype of errors and function calls."
  :ok funcall
  :pred funcall-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes statements/blocks/cases/fundefs
  :short "Fixtypes of statements, blocks, cases, and function definitions."

  (fty::deftagsum statement
    :short "Fixtype of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "We use different constructors for
       declaration of single vs. multiple variables.
       We also use different constructors for
       assignments to single or mulitple paths.
       This way, we can restrict the use of function calls
       for multiple variables/targets,
       as opposed to general expressions for single variables/targets.
       The requirements that
       the lists of multiple variables or paths contain at least two elements
       are given in the static semantics.
       Also the requirement that switch statements have at least one case
       (literal or default)
       is given in the static semantics."))
    (:block ((get block)))
    (:variable-single ((name identifier)
                       (init expression-option)))
    (:variable-multi ((names identifier-list)
                      (init funcall-option)))
    (:assign-single ((target path)
                     (value expression)))
    (:assign-multi ((targets path-list)
                    (value funcall)))
    (:funcall ((get funcall)))
    (:if ((test expression)
          (body block)))
    (:for ((init block)
           (test expression)
           (update block)
           (body block)))
    (:switch ((target expression)
              (cases swcase-list)
              (default block-option)))
    (:leave ())
    (:break ())
    (:continue ())
    (:fundef ((get fundef)))
    :pred statementp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist statement-list
    :short "Fixtype of lists of statements."
    :elt-type statement
    :true-listp t
    :elementp-of-nil nil
    :pred statement-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod block
    :short "Fixtype of blocks."
    ((statements statement-list))
    :tag :block
    :pred blockp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::defoption block-option
    block
    :short "Fixtype of optional blocks."
    :pred block-optionp
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::defprod swcase
    :short "Fixtype of cases (of switch statements)."
    ((value literal)
     (body block))
    :tag :swcase
    :pred swcasep
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::deflist swcase-list
    :short "Fixtype of lists of cases (of switch statements)."
    :elt-type swcase
    :true-listp t
    :elementp-of-nil nil
    :pred swcase-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod fundef
    :short "Fixtype of function definitions."
    ((name identifier)
     (inputs identifier-list)
     (outputs identifier-list)
     (body block))
    :tag :fundef
    :pred fundefp
    :measure (two-nats-measure (acl2-count x) 2))

  ///

  (defruled block-option-some->val-when-nonnil
    (implies x
             (equal (block-option-some->val x)
                    (block-fix x)))
    :enable block-option-some->val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption statement-option
  statement
  :short "Fixtype of optional statements."
  :pred statement-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult block-result
  :short "Fixtype of errors and blocks."
  :ok block
  :pred block-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult statement-result
  :short "Fixtype of errors and statements."
  :ok statement
  :pred statement-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult fundef-result
  :short "Fixtype of errors and function definitions."
  :ok fundef
  :pred fundef-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult swcase-result
  :short "Fixtype of errors and swcase clauses (for switch statements)."
  :ok swcase
  :pred swcase-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection swcase-list->value-list ((x swcase-listp))
  :returns (lits literal-listp)
  :short "Lift @(tsee swcase->value) to lists."
  (swcase->value x)
  ///
  (fty::deffixequiv swcase-list->value-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist fundef-list
  :short "Fixtype of lists of function definitions."
  :elt-type fundef
  :true-listp t
  :elementp-of-nil nil
  :pred fundef-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection fundef-list->name-list ((x fundef-listp))
  :returns (names identifier-listp)
  :short "Lift @(tsee fundef->name) to lists."
  (fundef->name x)
  ///
  (fty::deffixequiv fundef-list->name-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define statements-to-fundefs ((stmts statement-listp))
  :returns (fundefs fundef-listp)
  :short "Filter function definitions out of a list of statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function definitions are in the same order
     as they appear in the list of statements.
     We discard all the statements that are not function definitions,
     and we eliminate the @(':statement-fundef') wrappers."))
  (cond ((endp stmts) nil)
        ((statement-case (car stmts) :fundef)
         (cons (statement-fundef->get (car stmts))
               (statements-to-fundefs (cdr stmts))))
        (t (statements-to-fundefs (cdr stmts))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum data-value
  :short "Fixtype of data values in Yul objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "A data value is either a hex string or a plain string.")
   (xdoc::p
    "See @(tsee data-item)."))
  (:hex ((get hex-string)))
  (:plain ((get plain-string)))
  :pred data-value-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod data-item
  :short "Fixtype of data items in Yul objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "A data item consits of a name (a plain string) and a value."))
  ((name plain-string)
   (value data-value))
  :tag :data
  :pred data-item-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes objects
  :short "Fixtypes of Yul objects and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concrete syntax of Yul objects is described in
     [Yul: Specification of Yul Object].
     That description refers to the old grammar (see @(see concrete-syntax));
     the new grammar does not include Yul objects.")
   (xdoc::p
    "Here we formalize an abstract syntax version of Yul objects.
     We ``map'' from the old grammar to the new grammar as needed."))

  (fty::defprod object
    :short "Fixtype of Yul objects."
    :long
    (xdoc::topstring
     (xdoc::p
      "An object consists of
       a name (a plain string literal),
       a code block,
       and a sequence of zero or more objects and data items.
       In that sequence of objects and data items,
       the objects are sub-objects of this object,
       which motivates our choice of field name."))
    ((name plain-string)
     (code block)
     (sub/data object/data-list))
    :tag :object
    :pred objectp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deftagsum object/data
    :short "Fixtype of Yul objects and data items."
    (:object ((get object)))
    (:data ((get data-item)))
    :pred object/data-p
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist object/data-list
    :short "Fixtype of lists of Yul objects and data items."
    :elt-type object/data
    :true-listp t
    :elementp-of-nil nil
    :pred object/data-listp
    :measure (two-nats-measure (acl2-count x) 0)))
