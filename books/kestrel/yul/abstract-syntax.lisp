; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/hex-digit-char" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (yul)
  :short "Abstract syntax of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an abstract syntax of Yul based on its "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    "; more precisely, on the new grammar.")
   (xdoc::p
    "The abstract syntax defined here is fairly close to the concrete syntax,
     more precisely to the grammar,
     which already omits lexical entities like whitespace.
     The reason for this closeness is that we want to keep
     as much information as possible in the abstract syntax.
     In some cases our abstract syntax may be broader than the concrete syntax,
     to keep the definition of the abstract syntax slightly simpler;
     the important thing is that all the concrete syntax
     is representable in abstract syntax.")
   (xdoc::p
    "It is not yet clear whether the proper handling of Yul dialects
     will require extending this abstract syntax with types
     (which are not present in the new grammar).
     For now we omit types, but we may revisit this at some point."))
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

(fty::deflist identifier-list
  :short "Fixtype of lists of identifiers."
  :elt-type identifier
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset identifier-set
  :short "Fixtype of osets of identifiers."
  :elt-type identifier
  :elementp-of-nil nil
  :pred identifier-setp)

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
  :returns (chars str::hex-digit-char-listp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist hex-pair-list
  :short "Fixtype of lists of hex pairs."
  :elt-type hex-pair
  :true-listp t
  :elementp-of-nil nil
  :pred hex-pair-listp)

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
  (:letter-n ())
  (:letter-r ())
  (:letter-t ())
  (:line-feed ())
  (:carriage-return ())
  (:x ((get hex-pair)))
  (:u ((get hex-quad)))
  :pred escapep)

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
     We migh restrict the range of characters at some point."))
  (:char ((get character)))
  (:escape ((get escape)))
  :pred string-elementp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist string-element-list
  :short "Fixtype of string elements."
  :elt-type string-element
  :true-listp t
  :elementp-of-nil nil
  :pred string-element-listp)

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
    "We represent a (non-hex) string as a list of elements,
     plus a flag saying whether the surrounding quotes are double
     or not (i.e. single).
     This captures the full concrete syntax information.
     To more clearly distinguish this kind of string literal from hex strings,
     we call these strings `ASCII strings'.")
   (xdoc::p
    "We represent a hex string as a list of hex pairs,
     plus a flag saying whether the surrounding quotes are double
     or not (i.e. single).
     We do not capture the optional underscores for now."))
  (:boolean ((get bool)))
  (:dec-number ((get nat)))
  (:hex-number ((get hex-digit-list)))
  (:ascii-string ((content string-element-list)
                  (double-quote-p bool)))
  (:hex-string ((content hex-pair-list)
                (double-quote-p bool)))
  :pred literalp)

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
    :pred funcallp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption expression-option
  expression
  :short "Fixtype of optional expressions."
  :pred expression-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption funcall-option
  funcall
  :short "Fixtype of optional function calls."
  :pred funcall-optionp)

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
                      (init funcall-optionp)))
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
    :pred blockp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::defoption block-option
    block
    :short "Fixtye of optional blocks."
    :pred block-optionp
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::defprod swcase
    :short "Fixtype of cases (of switch statements)."
    ((value literal)
     (body block))
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
    :measure (two-nats-measure (acl2-count x) 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection swcase-list->value-list ((x swcase-listp))
  :returns (lits literal-listp)
  :short "Lift @(tsee swcase->value) to lists."
  (swcase->value x)
  ///
  (fty::deffixequiv swcase-list->value-list))
