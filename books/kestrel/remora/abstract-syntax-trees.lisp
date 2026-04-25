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
     [arxiv] (Figure 1),
     [thesis] (Figure 4.1),
     [esop] (Figure 6),
     and [impl].
     These ASTs are consistent with the "
    (xdoc::seetopic "grammar" "ABNF grammar of Remora")
    ".")
   (xdoc::p
    "The syntax definitions in [arxiv] and [thesis] are quite aligned,
     while [esop] has some differences;
     since [esop] is older, we just consider [arxiv] and [thesis] here.
     [impl] makes some extensions to [arxiv] and [thesis].
     The ABNF grammar is derived from [impl].")
   (xdoc::p
    "We have started defining the syntax as in [arxiv] and [thesis],
     but we are in the process of extending it according to [impl].
     We have started defining just the core syntax, as in [arxiv] and [thesis],
     but we are in the process of adding non-core constructs as in [impl];
     we plan to characterize the core subset
     and to define a desugaring transformation
     from the full syntax to the core syntax.")
   (xdoc::p
    "As a general remark that applies to multiple fixtypes defined here,
     we use ACL2 strings for variable names
     (for expressions, types, and indices).
     We may change this if needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-value
  :short "Fixtype of base values."
  :long
  (xdoc::topstring
   (xdoc::p
    "[arxiv] and [thesis] do not pin down the base values,
     leaving them abstract,
     but [impl] currently has booleans, integers, and floats.
     For integers, [impl] use Haskell's @('Int'),
     which consists of fixed-precision integers with at least 30 bits.
     For floats, [impl] uses Haskell's @('Float'),
     which consists of single-precision floating-point numbers,
     ``desired'' (according to the Haskell documentation)
     to comply with the IEEE standard.
     For now, we use ACL2 arbitrary-precision integers and rationals;
     we will refine them later."))
  (:bool ((value bool)))
  (:int ((value int)))
  (:float ((value acl2::rational)))
  :pred base-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-type
  :short "Fixtype of base types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These mirror the base values in @(tsee base-value)."))
  (:bool ())
  (:int ())
  (:float ())
  :pred base-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum kind
  :short "Fixtype of kinds."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are associated to types.
     They denote arrays and atoms."))
  (:array ())
  (:atom ())
  :pred kindp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist kind-list
  :short "Fixtype of lists of kinds."
  :elt-type kind
  :true-listp t
  :elementp-of-nil nil
  :pred kind-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod kinded-var
  :short "Fixtype of kinded variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A kinded variable consists of a variable name and an associated kind."))
  ((var string)
   (kind kind))
  :pred kinded-varp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist kinded-var-list
  :short "Fixtype of lists of kinded variables."
  :elt-type kinded-var
  :true-listp t
  :elementp-of-nil nil
  :pred kinded-var-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes dims
  :short "Fixtypes of dimensions and lists of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Although [arxiv] and [thesis]
     define indices as consisting of dimensions and shapes mixed together,
     and use sorting rules to ensure index well-formedness,
     we provide separate syntactic definitions of dimensions and shapes,
     and avoid sorting rules;
     this is also consistent with [impl].
     The key point is that [arxiv] and [thesis] have
     one form of index variables, which may denote dimensions or shapes,
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
     as in [impl] but unlike [arxiv] and [thesis]."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum shape
    :parents (abstract-syntax-trees shapes)
    :short "Fixtype of shapes."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       named variables,
       dimensions (lifted to be shapes),
       shapes built from zero or more dimensions,
       concatenations of shapes,
       and splicing of dimensions and shapes.")
     (xdoc::p
      "The @(':dim') and @(':splice') summands are non-core.")
     (xdoc::p
      "The @(':dim') summand captures the case in which
       a shape is expected
       (currently the only place is in an array type),
       but a dimension is provided:
       the dimension is auto-lifted to a singleton shape;
       it is a convenience construct, not a core construct.
       In contrast, the @(':dims') summand is the core constructor
       for a shape consisting of zero or more dimensions;
       in [arxiv] it is written as @($(\\mathtt{Shp}\\ \\iota\\ldots)$),
       in [thesis] it is written as @($(\\mathtt{shape}\\ \\iota\\ldots)$),
       and in [impl], as defined in the ABNF grammar,
       it is written as @($(\\mathtt{dims}\\ ...)$),
       so we use @(':dims') here.")
     (xdoc::p
      "The @(':splice') summand represents the square bracket notation.
       Although [impl] and the ABNF grammar use indices inside the brackets,
       since dimensions may be auto-lifted dimensions,
       we can just use shapes, and avoid a mutual recursion with indices here.
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

(fty::deftagsum index
  :short "Fixtype of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "An index is either a dimension or a shape:
     this enforces index sorts syntactically,
     without the need for sorting rules;
     the key point is that dimensions and shapes have distinct variables.
     [impl], and the ABNF grammar after it,
     uses the term `extent', but we stick to `index' here."))
  (:dim ((dim dim)))
  (:shape ((shape shape)))
  :pred indexp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist index-list
  :short "Fixtype of lists of indices."
  :elt-type index
  :true-listp t
  :elementp-of-nil nil
  :pred index-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum index-param
  :short "Fixtype of index parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are index variables used as parameters,
     e.g. in a product or sum type;
     they correspond to @('index-var') in the ABNF grammar.
     As in dimension and shape variables in @(tsee dim) and @(tsee shape),
     index parameters carry their own sort (dimension or shape),
     i.e. they are syntactically distinct.
     This is different from [arxiv] and [thesis],
     where dimension and shape variables are syntactically the same,
     and thus they need explcit sorting rules."))
  (:dim ((name string)))
  (:shape ((name string)))
  :pred index-paramp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist index-param-list
  :short "Fixtype of lists of index parameters."
  :elt-type index-param
  :true-listp t
  :elementp-of-nil nil
  :pred index-param-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes types
  :short "Fixtypes of types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum type
    :parents (abstract-syntax-trees types)
    :short "Fixtype of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       named variables,
       base types,
       array types (consisting of an atom type and a shape),
       function types (with zero or more input types and an output type),
       universal types (quantified over kinded variables),
       product types (quantified over index parameters),
       and sum types (quantified over index parameters)."))
    (:var ((name string)))
    (:base ((type base-type)))
    (:array ((type type)
             (shape shape)))
    (:fun ((in type-list)
           (out type)))
    (:forall ((vars kinded-var-list)
              (type type)))
    (:pi ((params index-param-list)
          (type type)))
    (:sigma ((params index-param-list)
             (type type)))
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

(fty::defprod typed-var
  :short "Fixtype of typed variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A typed variable consists of a variable name and an associated type."))
  ((var string)
   (type type))
  :pred typed-varp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist typed-var-list
  :short "Fixtype of lists of typed variables."
  :elt-type typed-var
  :true-listp t
  :elementp-of-nil nil
  :pred typed-var-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes exprs/atoms
  :short "Fixtypes of expressions, atoms, and lists thereof."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expr
    :parents (abstract-syntax-trees exprs/atoms)
    :short "Fixtype of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       named variables,
       non-empty arrays with at least one atom,
       empty arrays with the atom type,
       non-empty frames with at least one expression,
       empty frames with the cell type,
       applications of expressions to expressions
       (called `term applications' in the Remora publications),
       applications of expressions to types,
       applications of expressions to indices,
       and unboxing of expressions;
       the latter binds zero or more variables to indices,
       a variable to the boxed value,
       and then returns the body expression.")
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
    (:array ((dims nat-list)
             (atoms atom-list)))
    (:array-empty ((dims nat-list)
                   (type type)))
    (:frame ((dims nat-list)
             (exprs expr-list)))
    (:frame-empty ((dims nat-list)
                   (type type)))
    (:term-app ((fun expr)
                (args expr-list)))
    (:type-app ((fun expr)
                (args type-list)))
    (:index-app ((fun expr)
                 (args index-list)))
    (:unbox ((indices index-param-list)
             (var string)
             (target expr)
             (body expr)))
    :pred exprp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-list
    :parents (abstract-syntax-trees exprs/atoms)
    :short "Fixtype of lists of expressions."
    :elt-type expr
    :true-listp t
    :elementp-of-nil nil
    :pred expr-listp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum atom
    :parents (abstract-syntax-trees exprs/atoms)
    :short "Fixtype of atoms."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       base values,
       lambda abstractions of expressions over typed variables,
       lambda abstractions of expressions over kinded variables,
       lambda abstractions of expressions over sorted variables,
       and boxed arrays with given indices and type.")
     (xdoc::p
      "[arxiv] uses @($v$) as the body of type and index abstraction,
       while [thesis] uses @($e$), same as term abstraction.
       We use the latter, as that seems the intent."))
    (:base ((value base-value)))
    (:term-abs ((vars typed-var-list)
                (body expr)))
    (:type-abs ((vars kinded-var-list)
                (body expr)))
    (:index-abs ((params index-param-list)
                 (body expr)))
    (:box ((indices index-list)
           (array expr)
           (type type)))
    :pred atomp)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist atom-list
    :parents (abstract-syntax-trees exprs/atoms)
    :short "Fixtype of lists of atoms."
    :elt-type atom
    :true-listp t
    :elementp-of-nil nil
    :pred atom-listp))
