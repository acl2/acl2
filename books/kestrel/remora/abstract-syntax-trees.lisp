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
     [impl] currently uses the term `extent', but it will use `ispace' soon.
     The rationale for `ispace' is that it denotes an index space,
     i.e. a space where indices range;
     one index over a dimension, zero or more indices over a shape.")
   (xdoc::p
    "These ASTs preserve much of the concrete syntax information,
     so they include both core and non-core constructs.
     We plan to define a characterization of core ASTs
     and a desugaring transformation from all ASTs to core ASTs.
     The ASTs in [impl] are slightly more abstracted than ours.")
   (xdoc::p
    "The coverage of our ASTs is almost complete.
     Still missing are string literals,
     and multiplications and subtraction of dimensions;
     we plan to add all of these shortly.
     We may also need to replace ACL2 rationals (in base values)
     with a more explicit notion of floating literals.")
   (xdoc::p
    "As a general remark that applies to multiple fixtypes defined here,
     we use ACL2 strings for variable names.
     But we should probably introduce and use
     a slightly more abstract notion of identifiers."))
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
     while our ASTs have two separate formsm, one per sort,
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
       and additions.
       We also plan to add multiplications and subtractions, as in [impl]."))
    (:var ((name string)))
    (:const ((value nat)))
    (:add ((dims dim-list)))
    :pred dimp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist dim-list
    :parents (abstract-syntax-trees dims)
    :short "Fixtype of lists of dimensions."
    :elt-type dim
    :true-listp t
    :elementp-of-nil nil
    :pred dim-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes shapes
  :short "Fixtypes of shapes and lists of shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee dims) for the reason why
     we define dimensions and shapes separately,
     as in [impl] but unlike [thesis]."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum shape
    :parents (abstract-syntax-trees shapes)
    :short "Fixtype of shapes."
    :long
    (xdoc::topstring
     (xdoc::p
      "This corresponds to @('shape') in the ABNF grammar.")
     (xdoc::p
      "There are
       named variables,
       dimensions (lifted to be shapes),
       shapes built from zero or more dimensions,
       concatenations of shapes,
       and splicing of dimensions and shapes.")
     (xdoc::p
      "The @(':dim') summand captures the case in which
       a shape is expected
       (currently the only place is in an array type),
       but a dimension is provided:
       the dimension is auto-lifted to a singleton shape;
       it is a convenience construct, not a core construct.
       In contrast, the @(':dims') summand is the core constructor
       for a shape consisting of zero or more dimensions;
       in [esop] it is written as @($(\\mathtt{S}\\ \\iota\\ldots)$),
       in [arxiv] it is written as @($(\\mathtt{Shp}\\ \\iota\\ldots)$),
       in [thesis] it is written as @($(\\mathtt{shape}\\ \\iota\\ldots)$),
       and in [impl], as defined in the ABNF grammar,
       it is written as @($(\\mathtt{dims}\\ ...)$),
       so we use @(':dims') here.")
     (xdoc::p
      "The @(':splice') summand represents the square bracket notation.
       Although [impl] and the ABNF grammar use ispaces inside the brackets,
       since dimensions may be auto-lifted dimensions,
       we can just use shapes, and avoid a mutual recursion with ispaces here.
       This makes it apparent that
       concatenation and splicing are equivalent constructs."))
    (:var ((name string)))
    (:dim ((dim dim)))
    (:dims ((dims dim-list)))
    (:append ((shapes shape-list)))
    (:splice ((shapes shape-list)))
    :pred shapep)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist shape-list
    :parents (abstract-syntax-trees shapes)
    :short "Fixtype of lists of shapes."
    :elt-type shape
    :true-listp t
    :elementp-of-nil nil
    :pred shape-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ispace
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
  :short "Fixtype of lists of ispaces."
  :elt-type ispace
  :true-listp t
  :elementp-of-nil nil
  :pred ispace-listp)

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
     and thus explcit sorting rules are needed."))
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
      "This corresponds to @('type-exp') in the ABNF grammar.")
     (xdoc::p
      "There are
       variables (of two kinds),
       base types,
       array types consisting of a type for the elements
       and a shape in which the elements are arranged,
       bracket types which are like array types
       but the zero or more shapes are concatenated
       (the splicing comes from the fact that
       dimensions are auto-lifted to shapes as in bracket shapes),
       function types (with zero or more input types and an output type),
       universal types (quantified over kinded variables),
       product types (quantified over ispace parameters),
       and sum types (quantified over ispace parameters)."))
    (:var ((var type-var)))
    (:base ((type base-type)))
    (:array ((elem type)
             (shape shape)))
    (:bracket ((elem type)
               (shapes shape-list)))
    (:fun ((in type-list)
           (out type)))
    (:forall ((params type-var-list)
              (body type)))
    (:pi ((params ispace-var-list)
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

(fty::defprod var+type
  :short "Fixtype of variables with types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('pat') in the ABNF grammar.")
   (xdoc::p
    "These are pairs consisting of a variable name and an associated type.
     The type is an array one because variables are expressions, not atoms.
     These variables are separate from ispace and type variables."))
  ((var string)
   (type type))
  :pred var+type-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var+type-list
  :short "Fixtype of lists of variables with types."
  :elt-type var+type
  :true-listp t
  :elementp-of-nil nil
  :pred var+type-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-value
  :short "Fixtype of base values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('base-val') in the ABNF grammar.")
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
     For now, we use ACL2 arbitrary-precision integers and rationals;
     but we will refine them."))
  (:bool ((value bool)))
  (:int ((value int)))
  (:float ((value acl2::rational)))
  :pred base-valuep)

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
       atoms (auto-lifted to scalars, i.e. arrays of rank 0),
       non-empty arrays with at least one atom,
       empty arrays with the type of the elements,
       non-empty frames with at least one expression,
       empty frames with the type of the cells,
       applications of expressions to expressions
       (called `term applications' in the Remora publications),
       applications of expressions to types,
       applications of expressions to ispaces,
       combined applications of expressions to types/ispaces/expressions,
       unboxing expressions,
       bracketed expressions,
       and @('let') expressions.
       An unboxing expression
       binds zero or more variables to ispaces,
       binds a variable to the boxed expression,
       and returns the body expression.")
     (xdoc::p
      "The non-emptiness of the atom list in @(':array')
       and of the expression list in @(':frame')
       is not captured in this fixtype.
       The FTY @(':require') feature does not seem to work here,
       perhaps because of the interaction with the mutually recursive fixtypes.
       We can enforce this non-emptiness in the static semantics.
       [thesis] enforces non-emptiness with the patterns
       @($\\mathfrak{a}\\ \\mathfrak{a}\\ldots$) and @($e\\ e\\ldots$),
       while [arxiv] paper does not."))
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
    (:app ((fun expr)
           (args expr-list)))
    (:tapp ((fun expr)
            (args type-list)))
    (:iapp ((fun expr)
            (args ispace-list)))
    (:capp ((fun expr)
            (targs type-list-option)
            (iargs ispace-list-option)
            (args expr-list)))
    (:unbox ((ispaces ispace-var-list)
             (var string)
             (target expr)
             (body expr)))
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
       base values,
       lambda abstractions of expressions over variables with types,
       lambda abstractions of expressions over type variables,
       lambda abstractions of expressions over ispace variables,
       and boxed arrays with given ispaces and type.
       Since the type in a boxing construct must be a sum type,
       we could enforce this syntactically,
       but we follow [arxiv], [thesis], and [impl],
       which all use a generic type."))
    (:base ((value base-value)))
    (:lambda ((params var+type-list)
              (body expr)))
    (:tlambda ((params type-var-list)
               (body expr)))
    (:ilambda ((params ispace-var-list)
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
       type function bindings
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
           (params var+type-list)
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
            (params var+type-list)
            (type type)
            (expr expr)))
    :pred bindp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist bind-list
    :parents (abstract-syntax-trees exprs/atoms/binds)
    :short "Fixtype of lists of atoms."
    :elt-type bind
    :true-listp t
    :elementp-of-nil nil
    :pred bind-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod prog
  :short "Fixtypr of programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to @('program') in the ABNF grammar.")
   (xdoc::p
    "Currently a program is just a (top-level) expression."))
  ((expr expr))
  :pred progp)
