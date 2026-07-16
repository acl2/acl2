; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/dec-digit-char-list" :dir :system)
(include-book "kestrel/fty/hex-digit-char-list" :dir :system)
(include-book "kestrel/fty/oct-digit-char-list" :dir :system)
(include-book "std/strings/eqv" :dir :system)

(include-book "portcullis")

(local (include-book "std/basic/ifix" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/basic/rfix" :dir :system))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST thms

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-trees
  :parents (abstract-syntax)
  :short "Abstract syntax trees of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for abstract syntax trees (ASTs) for typed Remora,
     based on
     [thesis] (Figure 4.1),
     [arxiv] (Figure 1),
     [esop] (Figure 6),
     and [impl].
     These ASTs are consistent with the "
    (xdoc::seetopic "grammar" "ABNF grammar of Remora")
    ", which is derived from [impl].
     We use the term `ispace' to refer to what [thesis] calls `index';
     [impl] also uses `ispace'.
     The rationale for `ispace' is that it denotes an index space,
     i.e. a space where indices range;
     one index over a dimension, zero or more indices over a shape.")
   (xdoc::p
    "These ASTs preserve much of the concrete syntax information,
     so they include both core and non-core constructs.
     We have defined a characterization of core ASTs
     and a desugaring transformation from all ASTs to core ASTs.
     The ASTs in [impl] are more abstracted than ours;
     they contain less sugar.")
   (xdoc::p
    "Our ASTs contain some information absent from the concrete syntax,
     such as certain type annotations.
     These are calculated by type checking/inference.")
   (xdoc::p
    "As a general remark that applies to multiple fixtypes defined here,
     we use ACL2 strings for variable names.
     But we should probably introduce and use
     a slightly more abstract notion of identifiers.")
   (xdoc::p
    "Note that the strings representing identifiers
     that derive from potentially-non-ASCII Remora surface syntax
     are stored in our ASTs as ACL2 strings whose bytes are
     the UTF-8 encoding of the original Unicode code-point sequence.
     Since ACL2 char codes are 0-255,
     a non-ASCII code point such as U+03B1 cannot occupy a single character;
     the UTF-8 convention encodes it as two bytes (@('0xCE 0xB1'))
     within the string.
     ASCII identifiers are unaffected
     (each ASCII code point is a single UTF-8 byte).
     The encoding is performed by syntax abstraction by @('abs-nats-to-string'),
     and is symmetric to the UTF-8 decoding
     performed by the parsing entry points (see @(see parser-interface)).
     Consumers that need code points back
     can decode the string with @(tsee acl2::utf8=>ustring).
     String equality on names is byte-wise,
     which agrees with code-point-sequence equality,
     given the assumption that the strings are well-formed UTF-8."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes dims
  :short "Fixtypes of dimensions and lists of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "[thesis] defines ispaces (`indices' there)
     as consisting of dimensions and shapes ``mixed together'',
     and uses sorting rules to ensure ispace well-formedness.
     Instead we provide separate syntactic definitions of dimensions and shapes,
     and avoid sorting rules;
     this is also consistent with [impl].
     The key point is that [thesis] has
     one form of ispace variables, which may denote dimensions or shapes,
     while our ASTs have two separate forms, one per sort,
     consistently with the concrete syntax (see ABNF grammar),
     which uses prefix symbols to explicate the sort of the variable."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum dim
    :parents (abstract-syntax-trees dims)
    :short "Fixtype of dimensions."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('dim') in the ABNF grammar.")
     (xdoc::p
      "There are
       named variables,
       constants (natural numbers),
       additions of zero or more dimensions,
       multiplications of zero or more dimensions,
       and subtractions of zero or more dimensions."))
    (:var ((name string)))
    (:const ((val nat)))
    (:add ((dims dim-list)))
    (:mul ((dims dim-list)))
    (:sub ((dims dim-list)))
    :pred dimp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist dim-list
    :parents (abstract-syntax-trees dims)
    :short "Fixtype of lists of dimensions."
    :elt-type dim
    :true-listp t
    :elementp-of-nil nil
    :pred dim-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist dim-list-list
  :short "Fixtype of lists of lists of dimensions."
  :elt-type dim-list
  :true-listp t
  :elementp-of-nil t
  :pred dim-list-listp

  ///

  (defruled true-list-listp-when-dim-list-listp
    (implies (dim-list-listp x)
             (true-list-listp x))
    :induct t
    :enable dim-list-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes shapes/ispaces
  :short "Fixtypes of shapes and ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee dims) for the reason why
     we define dimensions and shapes separately,
     as in [impl] but unlike [thesis].")
   (xdoc::p
    "Shapes and ispaces are mutually recursive
     because splices, which are shapes, contain ispaces.
     This is consistent with a recent change to [impl]."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum shape
    :parents (abstract-syntax-trees shapes/ispaces)
    :short "Fixtype of shapes."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('shape') in the ABNF grammar.")
     (xdoc::p
      "There are
       named variables,
       shapes built from zero or more dimensions,
       concatenations of shapes,
       and splicing of ispaces.")
     (xdoc::p
      "The @(':dims') summand is the core constructor
       for a shape consisting of zero or more dimensions;
       in [esop] it is written as @($(\\mathtt{S}\\ \\iota\\ldots)$),
       in [arxiv] it is written as @($(\\mathtt{Shp}\\ \\iota\\ldots)$),
       in [thesis] it is written as @($(\\mathtt{shape}\\ \\iota\\ldots)$),
       and in [impl], as defined in the ABNF grammar,
       it is written as @($(\\mathtt{dims}\\ ...)$),
       so we use @(':dims') here.")
     (xdoc::p
      "The @(':splice') summand represents the square bracket notation.
       As in [impl] and the ABNF grammar, it contains ispaces,
       which is why shapes and ispaces are mutually recursive.
       This makes it apparent that
       concatenation and splicing are equivalent constructs."))
    (:var ((name string)))
    (:dims ((dims dim-list)))
    (:append ((shapes shape-list)))
    (:splice ((ispaces ispace-list)))
    :pred shapep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist shape-list
    :parents (abstract-syntax-trees shapes/ispaces)
    :short "Fixtype of lists of shapes."
    :elt-type shape
    :true-listp t
    :elementp-of-nil nil
    :pred shape-listp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum ispace
    :parents (abstract-syntax-trees shapes/ispaces)
    :short "Fixtype of ispaces."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('ispace') in the ABNF grammar."))
    (:dim ((dim dim)))
    (:shape ((shape shape)))
    :pred ispacep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist ispace-list
    :parents (abstract-syntax-trees shapes/ispaces)
    :short "Fixtype of lists of ispaces."
    :elt-type ispace
    :true-listp t
    :elementp-of-nil nil
    :pred ispace-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist shape-list-list
  :short "Fixtype of lists of lists of shapes."
  :elt-type shape-list
  :true-listp t
  :elementp-of-nil t
  :pred shape-list-listp

  ///

  (defruled true-list-listp-when-shape-list-listp
    (implies (shape-list-listp x)
             (true-list-listp x))
    :induct t
    :enable shape-list-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption ispace-option
  ispace
  :short "Fixtype of optional ispaces."
  :pred ispace-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ispace-list-option
  :short "Fixtype of optional lists of ispaces."
  (:some ((val ispace-list)))
  (:none ())
  :pred ispace-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ispace-var
  :short "Fixtype of ispace variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('ispace-var') in the ABNF grammar.")
   (xdoc::p
    "As in @(tsee dim) and @(tsee shape),
     these variables carry their own sort (dimension or shape),
     i.e. they are syntactically distinct.
     This is different from [thesis],
     where dimension and shape variables are syntactically the same,
     and thus explicit sorting rules are needed."))
  (:dim ((name string)))
  (:shape ((name string)))
  :pred ispace-varp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ispace-var-list
  :short "Fixtype of lists of ispace variables."
  :elt-type ispace-var
  :true-listp t
  :elementp-of-nil nil
  :pred ispace-var-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset ispace-var-set
  :short "Fixtype of sets of ispace variables."
  :elt-type ispace-var
  :pred ispace-var-setp

  ///

  (defrule ispace-var-setp-of-mergesort
    (implies (ispace-var-listp x)
             (ispace-var-setp (set::mergesort x)))
    :induct t
    :enable set::mergesort))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ispace-var-list-option
  :short "Fixtype of optional lists of ispace variables."
  (:some ((val ispace-var-list)))
  (:none ())
  :pred ispace-var-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-type
  :short "Fixtype of base types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('base-type') in the ABNF grammar.")
   (xdoc::p
    "There are types for booleans, integers, and floats."))
  (:bool ())
  (:int ())
  (:float ())
  :pred base-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-var
  :short "Fixtype of type variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('type-var') in the ABNF grammar.")
   (xdoc::p
    "Similarly to how @(tsee ispace-var) carries sorts,
     these variables carry their own kind (atom or array),
     i.e. they are syntactically distinct.
     This is different from [thesis],
     where atom type variables and array type variables
     are syntactically the same,
     and thus explicit kinding rules are needed."))
  (:atom ((name string)))
  (:array ((name string)))
  :pred type-varp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type-var-list
  :short "Fixtype of lists of type variables."
  :elt-type type-var
  :true-listp t
  :elementp-of-nil nil
  :pred type-var-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset type-var-set
  :short "Fixtype of sets of type variables."
  :elt-type type-var
  :pred type-var-setp

  ///

  (defrule type-var-setp-of-mergesort
    (implies (type-var-listp x)
             (type-var-setp (set::mergesort x)))
    :induct t
    :enable set::mergesort))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-var-list-option
  :short "Fixtype of optional lists of type variables."
  (:some ((val type-var-list)))
  (:none ())
  :pred type-var-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes types
  :short "Fixtypes of types and lists of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given that types are partitioned into two kinds
     similarly to how ispaces are partitioned into two sorts,
     and given that expressions and atoms are defined separately below,
     it may seem natural to also partition the definition of types
     into atom-kinded types and array-kinded types.
     However, Remora allows atom-kinded types
     wherever array-kinded types are expected:
     the atom-kinded type is auto-lifted to a zero-rank array type.
     There are only two spots in which a type must be atom-kinded,
     namely the element type of an array or bracket type,
     and that restriction can be enforced in the static semantics.
     Also note that ispaces and expressions/atoms
     have a different recursive structure than types,
     making those more naturally amenable to a partitioned definition."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum type
    :parents (abstract-syntax-trees types)
    :short "Fixtype of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('type') in the ABNF grammar.")
     (xdoc::p
      "There are
       variables (of two kinds),
       base types,
       array types consisting of a type for the elements
       and an ispace indicating how the elements are arranged,
       bracket types which are similar to array types
       but they have zero or more ispaces to be spliced,
       function types (with zero or more input types and an output type),
       universal types (quantified over kinded variables),
       product types (quantified over ispace parameters),
       and sum types (quantified over ispace parameters).")
     (xdoc::p
      "The @(':pi') summand is
       the main, core form of product type,
       which binds exactly one parameter,
       while the @(':pin') summand is sugar for
       a nesting of unary product types.
       The CST-to-AST mapping turns
       the product types with one parameter into @(':pi'),
       and those with two or more parameters into @(':pin'),
       similarly to ispace applications (see @(tsee expr)).
       The @(':forall') and @(':sigma') summands
       will be similarly given unary forms.")
     (xdoc::p
      "The concrete syntax requires the parameter lists of
       @(':forall'), @(':pin'), and @(':sigma') to be non-empty;
       this is not captured in this fixtype."))
    (:var ((var type-var)))
    (:base ((type base-type)))
    (:array ((elem type)
             (ispace ispace)))
    (:bracket ((elem type)
               (ispaces ispace-list)))
    (:fun ((in type-list)
           (out type)))
    (:forall ((params type-var-list)
              (body type)))
    (:pi ((param ispace-var)
          (body type)))
    (:pin ((params ispace-var-list)
           (body type)))
    (:sigma ((params ispace-var-list)
             (body type)))
    :pred typep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist type-list
    :parents (abstract-syntax-trees types)
    :short "Fixtype of lists of types."
    :elt-type type
    :true-listp t
    :elementp-of-nil nil
    :pred type-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-option
  type
  :short "Fixtype of optional types."
  :pred type-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum type-list-option
  :short "Fixtype of optional lists of types."
  (:some ((val type-list)))
  (:none ())
  :pred type-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var+type?
  :short "Fixtype of variables with optional types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('pat') in the ABNF grammar,
     with the relaxation that we allow a type to be missing.
     In fact, Remora concrete syntax may evolve in that direction,
     with type inference inferring the missing types.")
   (xdoc::p
    "These are pairs consisting of a variable name and an associated type.
     The type is an array one because variables are expressions, not atoms.
     These variables are separate from ispace and type variables."))
  ((var string)
   (type? type-option))
  :pred var+type?-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var+type?-list
  :short "Fixtype of lists of variables with optional types."
  :elt-type var+type?
  :true-listp t
  :elementp-of-nil nil
  :pred var+type?-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum sign
  :short "Fixtype of signs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used in numeric literals."))
  (:plus ())
  (:minus ())
  :pred signp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption sign-option
  sign
  :short "Fixtype of optional signs."
  :pred sign-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-lit
  :short "Fixtype of integer literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('num-val') with @('decimal') in the ABNF grammar.")
   (xdoc::p
    "An absent sign is semantically equivalent to a positive sign,
     but we preserve the concrete syntax information.
     Leading zero digits make no semantic difference,
     but we preserve the concrete syntax information.
     There must be at least one digit."))
  ((sign? sign-option)
   (digits dec-digit-char-list
           :reqfix (if (consp digits) digits '(#\0))))
  :require (consp digits)
  :pred int-litp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist int-lit-list
  :short "Fixtype of lists of integer literals."
  :elt-type int-lit
  :true-listp t
  :elementp-of-nil nil
  :pred int-lit-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expo
  :short "Fixtype of exponents."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used in float literals.")
   (xdoc::p
    "The boolean flag says whether we have @('E') (@('t')) or @('e') @('nil');
     this is not semantically relevant,
     but we preserve the concrete syntax information.
     An absent sign is semantically equivalent to a positive sign,
     but we preserve the concrete syntax information.
     We require at least one digit, per the ABNF grammar."))
  ((upcase bool)
   (sign? sign-option)
   (digits dec-digit-char-list
           :reqfix (if (consp digits) digits '(#\0))))
  :require (consp digits)
  :pred expop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption expo-option
  expo
  :short "Fixtype of optional exponents."
  :pred expo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod float-lit
  :short "Fixtype of float literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('num-val') with @('float-lit') in the ABNF grammar.")
   (xdoc::p
    "An absent sign is semantically equivalent to a positive sign,
     but we preserve the concrete syntax information.
     There must be always at least a digit in the whole part
     (i.e. the digits before the dot);
     the number cannot start with dot.
     The list of digits in the fractional part (i.e. after the dot)
     may be empty, which means that there is no dot:
     the number cannot end with dot without a digit after that.
     At least one of the dot and exponent must be present, possibly both."))
  ((sign? sign-option)
   (whole-digits dec-digit-char-list
                 :reqfix (if (consp whole-digits) whole-digits '(#\0)))
   (frac-digits dec-digit-char-list
                :reqfix (if (or (consp frac-digits) expo?) frac-digits '(#\0)))
   (expo? expo-option))
  :require (and (consp whole-digits)
                (or (consp frac-digits)
                    (expo-option-case expo? :some)))
  :pred float-litp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum char-escape
  :short "Fixtype of character escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('char-escape') in the ABNF grammar."))
  (:a ())
  (:b ())
  (:f ())
  (:n ())
  (:r ())
  (:t ())
  (:v ())
  (:bslash ())
  (:dquote ())
  (:squote ())
  :pred char-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ascii-escape
  :short "Fixtype of ASCII escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('ascii-escape') in the ABNF grammar.")
   (xdoc::p
    "We model the sequence from NUL to SP via their codes,
     and DEL separately."))
  (:nul-to-sp ((code nat
                     :reqfix (if (<= code #x20) code 0)))
   :require (<= code #x20))
  (:del ())
  :pred ascii-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod caret-escape
  :short "Fixtype of caret escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('caret-escape') in the ABNF grammar.")
   (xdoc::p
    "We model these via their codes."))
  ((code nat
         :reqfix (if (<= code #x1f) code 0)))
  :require (<= code #x1f)
  :pred caret-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum num-escape
  :short "Fixtype of numeric escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('num-escape') in the ABNF grammar."))
  (:dec ((digits dec-digit-char-list
                 :reqfix (if (consp digits) digits '(#\0))))
   :require (consp digits))
  (:oct ((digits oct-digit-char-list
                 :reqfix (if (consp digits) digits '(#\0))))
   :require (consp digits))
  (:hex ((digits hex-digit-char-list
                 :reqfix (if (consp digits) digits '(#\0))))
   :require (consp digits))
  :pred num-escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum escape
  :short "Fixtype of escapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('escape-char') in the ABNF grammar."))
  (:char ((escape char-escape)))
  (:ascii ((escape ascii-escape)))
  (:caret ((escape caret-escape)))
  (:num ((escape num-escape)))
  :pred escapep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum char-lit
  :short "Fixtype of character-literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('char-lit') in the ABNF grammar."))
  (:char ((code nat
                :reqfix (if (or (and (<= #x0 code) (<= code #x21))
                                (and (<= #x23 code) (<= code #x5b))
                                (and (<= #x5d code) (<= code #xd7ff))
                                (and (<= #xe000 code) (<= code #x10ffff)))
                            code
                          0)))
   :require (or (and (<= #x0 code) (<= code #x21))
                (and (<= #x23 code) (<= code #x5b))
                (and (<= #x5d code) (<= code #xd7ff))
                (and (<= #xe000 code) (<= code #x10ffff))))
  (:escape ((escape escape)))
  :pred char-litp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char-lit-list
  :short "Fixtype of lists of character literals."
  :elt-type char-lit
  :true-listp t
  :elementp-of-nil nil
  :pred char-lit-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-lit
  :short "Fixtype of base literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('base-val') in the ABNF grammar.")
   (xdoc::p
    "Literals are direct representations of values.
     These are the literals that directly represent base values,
     i.e. atom values, as opposed to array values.
     These atom values are the values of the base types.")
   (xdoc::p
    "[thesis] does not pin down the base values,
     leaving them abstract,
     but [impl] currently has booleans, integers, and floats,
     as does the ABNF grammar.
     For integers, [impl] use Haskell's @('Int'),
     which consists of fixed-precision integers with at least 30 bits.
     For floats, [impl] uses Haskell's @('Float'),
     which consists of single-precision floating-point numbers,
     ``desired'' (according to the Haskell documentation)
     to comply with the IEEE standard.
     We defer those details to the semantics:
     here we use data structures for literals
     that are isomorphic to their concrete syntax,
     namely @(tsee int-lit) and @(tsee float-lit).
     For booleans, we just use ACL2 booleans."))
  (:bool ((lit bool)))
  (:int ((lit int-lit)))
  (:float ((lit float-lit)))
  :pred base-litp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist base-lit-list
  :short "Fixtype of lists of base literals."
  :elt-type base-lit
  :true-listp t
  :elementp-of-nil nil
  :pred base-lit-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes exprs/atoms/binds
  :short "Fixtypes of expressions, atoms, bindings, and lists thereof."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expr
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('exp') in the ABNF grammar.")
     (xdoc::p
      "There are
       named variables,
       atoms (auto-lifted to expressions),
       non-empty arrays with at least one atom,
       empty arrays with the type of the elements,
       non-empty frames with at least one expression,
       empty frames with the type of the cells,
       string literals,
       applications of expressions to expressions
       (called `term applications' in the Remora publications),
       applications of expressions to types,
       applications of expressions to ispaces (unary or n-ary),
       combined applications of expressions to types/ispaces/expressions,
       unboxing expressions,
       bracketed expressions,
       and @('let') expressions.
       An unboxing expression
       binds one or more variables to ispaces,
       binds a variable to the boxed expression,
       and returns the body expression;
       it is optionally annotated by its type
       (the type of the whole unboxing expression).")
     (xdoc::p
      "The @(':iapp') summand is the main, core form of ispace application,
       while the @(':iappn') summand is sugar for
       a left-nested chain of the unary applications to one argument at a time.
       The CST-to-AST mapping turns
       applications to one argument into @(':iapp'),
       and applications to two or more arguments into @(':iappn').
       We also plan to define and use well-formedness predicates
       saying that @(':iappn') always has two or more arguments
       (this could be also realized via a fixtype @(':require') in principle,
       but that currently is not working well within @(tsee fty::deftypes)).
       Other n-ary constructs will be similarly given unary forms,
       and treated in the same way.")
     (xdoc::p
      "The non-emptiness of the atom list in @(':array'),
       of the expression list in @(':frame'),
       of the argument lists of @(':app'), @(':tapp'), and @(':iappn')
       (but not of @(':capp'), whose value arguments may be absent),
       of the bind list in @(':let'),
       and of the ispace-var list in @(':unbox')
       is not captured in this fixtype.
       The FTY @(':require') feature does not seem to work here,
       perhaps because of the interaction with the mutually recursive fixtypes.
       We can enforce this non-emptiness in the static semantics.
       [thesis] enforces non-emptiness with the patterns
       @($\\mathfrak{a}\\ \\mathfrak{a}\\ldots$) and @($e\\ e\\ldots$),
       while [arxiv] paper does not.")
     (xdoc::p
      "The optional type of the body of an unbox expression
       (i.e. the result type of the unboxing)
       is calculated and stored by the type checker.
       It is absent after parsing."))
    (:var ((name string)))
    (:atom ((atom atom)))
    (:array ((dims nat-list)
             (atoms atom-list)))
    (:array-empty ((dims nat-list)
                   (type type)))
    (:frame ((dims nat-list)
             (exprs expr-list)))
    (:frame-empty ((dims nat-list)
                   (type type)))
    (:string ((chars char-lit-list)))
    (:app ((fun expr)
           (args expr-list)))
    (:tapp ((fun expr)
            (args type-list)))
    (:iapp ((fun expr)
            (arg ispace)))
    (:iappn ((fun expr)
             (args ispace-list)))
    (:capp ((fun expr)
            (targs type-list-option)
            (iargs ispace-list-option)
            (args expr-list)))
    (:unbox ((ispaces ispace-var-list)
             (var string)
             (target expr)
             (body expr)
             (type? type-option)))
    (:bracket ((exprs expr-list)))
    (:let ((binds bind-list)
           (body expr)))
    :pred exprp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-list
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of lists of expressions."
    :elt-type expr
    :true-listp t
    :elementp-of-nil nil
    :pred expr-listp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum atom
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of atoms."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('atom') in the ABNF grammar.")
     (xdoc::p
      "There are
       base literals,
       lambda abstractions of expressions over variables with types
       with an optional type of the body (not of the abstraction),
       lambda abstractions of expressions over type variables,
       lambda abstractions of expressions over ispace variables,
       and boxed arrays with given ispaces and type.
       Since the type in a boxing construct must be a sum type,
       we could enforce this syntactically,
       but we follow [arxiv], [thesis], and [impl],
       which all use a generic type.")
     (xdoc::p
      "The @(':ilambda') summand is
       the main, core form of ispace lambda abstraction,
       which binds exactly one parameter,
       while the @(':ilambdan') summand is sugar for
       a nesting of unary ispace lambda abstractions.
       The CST-to-AST mapping turns
       the ispace lambda abstractions with one parameter into @(':ilambda'),
       and those with two or more parameters into @(':ilambdan'),
       similarly to ispace applications (see @(tsee expr)).
       The other lambda summands will be similarly given unary forms.")
     (xdoc::p
      "The concrete syntax requires the parameter lists of
       the @(':lambda'), @(':tlambda'), and @(':ilambdan') summands
       and the ispace list of @(':box') to be non-empty;
       this is not captured in this fixtype.")
     (xdoc::p
      "The optional type of the body of a lambda abstraction
       is calculated and stored by the type checker.
       It is absent after parsing."))
    (:base ((lit base-lit)))
    (:lambda ((params var+type?-list)
              (body expr)
              (type? type-option)))
    (:tlambda ((params type-var-list)
               (body expr)))
    (:ilambda ((param ispace-var)
               (body expr)))
    (:ilambdan ((params ispace-var-list)
                (body expr)))
    (:box ((ispaces ispace-list)
           (array expr)
           (type type)))
    :pred atomp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist atom-list
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of lists of atoms."
    :elt-type atom
    :true-listp t
    :elementp-of-nil nil
    :pred atom-listp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum bind
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of bindings."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('bind') in the ABNF grammar.")
     (xdoc::p
      "These are used in @('let') expressions.
       There are
       ispace bindings,
       type bindings,
       value bindings,
       function bindings,
       type function bindings,
       ispace function bindings, and
       combined function bindings."))
    (:ispace ((var ispace-var)
              (ispace ispace)))
    (:type ((var type-var)
            (type type)))
    (:val ((var string)
           (type? type-option)
           (expr expr)))
    (:fun ((var string)
           (params var+type?-list)
           (type? type-option)
           (expr expr)))
    (:tfun ((var string)
            (params type-var-list)
            (type? type-option)
            (expr expr)))
    (:ifun ((var string)
            (params ispace-var-list)
            (type? type-option)
            (expr expr)))
    (:cfun ((var string)
            (tparams? type-var-list-option)
            (iparams? ispace-var-list-option)
            (params var+type?-list)
            (type type)
            (expr expr)))
    :pred bindp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist bind-list
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of lists of bindings."
    :elt-type bind
    :true-listp t
    :elementp-of-nil nil
    :pred bind-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist expr-list-list
  :short "Fixtype of lists of lists of expressions."
  :elt-type expr-list
  :true-listp t
  :elementp-of-nil t
  :pred expr-list-listp

  ///

  (defruled true-list-listp-when-expr-list-listp
    (implies (expr-list-listp x)
             (true-list-listp x))
    :induct t
    :enable expr-list-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atom-list-list
  :short "Fixtype of lists of lists of atoms."
  :elt-type atom-list
  :true-listp t
  :elementp-of-nil t
  :pred atom-list-listp

  ///

  (defruled true-list-listp-when-atom-list-listp
    (implies (atom-list-listp x)
             (true-list-listp x))
    :induct t
    :enable atom-list-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod import
  :short "Fixtype of imports."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('import') in the ABNF grammar.")
   (xdoc::p
    "An import names another Remora source file
     whose declarations are in scope in the importing file.
     The path is a string literal,
     represented as a list of character literals
     like the @(':string') summand of @(tsee expr)."))
  ((path char-lit-list))
  :pred importp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist import-list
  :short "Fixtype of lists of imports."
  :elt-type import
  :true-listp t
  :elementp-of-nil nil
  :pred import-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum decl
  :short "Fixtype of declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('decl') in the ABNF grammar.")
   (xdoc::p
    "A declaration is either
     a definition, wrapping any of the binding forms
     used in @('let') expressions,
     or an entry point, whose signature has the same shape
     as that of a function binding
     (the @(':fun') summand of @(tsee bind)):
     a name, value parameters, an optional return type,
     and a body expression."))
  (:def ((bind bind)))
  (:entry ((var string)
           (params var+type?-list)
           (type? type-option)
           (expr expr)))
  :pred declp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist decl-list
  :short "Fixtype of lists of declarations."
  :elt-type decl
  :true-listp t
  :elementp-of-nil nil
  :pred decl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod file
  :short "Fixtype of source files and import-expanded programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('file') in the ABNF grammar.")
   (xdoc::p
    "A source file is a sequence of imports
     followed by a sequence of declarations.")
   (xdoc::p
    "This fixtype also represents import-expanded programs:
     resolving the imports of a file
     replaces them with the declarations of the imported files,
     yielding a value of this fixtype with an empty list of imports.
     In the Haskell implementation,
     these are two different types:
     parsing yields a list of imports paired with a program
     (a pair with no named type),
     and import resolution yields a program
     (@('Prog'), a list of declarations)."))
  ((imports import-list)
   (decls decl-list))
  :pred filep)
