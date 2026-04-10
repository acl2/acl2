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

(local (include-book "kestrel/utilities/nfix" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x) x))
  :enable ifix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (remora)
  :short "Abstract syntax of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for abstract syntax trees (ASTs) for typed Remora,
     based on the publications on Remora mentioned in @(see remora).
     See Figure 1 in the arXiv paper,
     Figure 4.1 in the dissertation,
     and Figure 6 in the ESOP paper.
     The arXiv paper and the dissertation are quite aligned,
     while the ESOP paper has some differences;
     we adhere to the former because they are newer than the latter.")
   (xdoc::p
    "As a general remark that applies to multiple fixtypes defined here,
     we use ACL2 strings for variable names
     (for expressions, types, and indices).
     We may change this if needed.")
   (xdoc::p
    "We may generalize these ASTs to encompass untyped and type-erased Remora,
     or we might define alternative ASTs for those, with suitable mappings.")
   (xdoc::p
    "In line with the Remora publications, which define a core language,
     we do not yet define any higher-level constructs such as ``programs'',
     intended as collections of named definitions.
     But we plan to add such constructs at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-value
  :short "Fixtype of base values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The publications on Remora
     do not pin down the base values, leaving them abstract.
     Here we define some initial representative base values,
     which we may extend in the future.
     We may also parameterize our abstract syntax
     over the exact choice of these base values.")
   (xdoc::p
    "We may move this fixtype definition to a more general place,
     since besides being part of the abstract syntax,
     it may be part of the dynamic semantics."))
  (:bool ((value bool)))
  (:char ((value character)))
  (:int ((value int)))
  :pred base-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum base-type
  :short "Fixtype of base types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These mirror the base values in @(tsee base-value)."))
  (:bool ())
  (:char ())
  (:int ())
  :pred base-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum prim-op
  :short "Fixtype of primitive operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "The publications on Remora
     do not pin down the primitive operators, leaving them abstract;
     but they do provide a partial list.
     Here we define some initial representative primitive operators,
     consisting of the ones listed in the publications,
     which we may extend in the future.
     We may also parameterize our abstract syntax
     over the exact choice of these primitive operators."))
  (:add ())
  (:sub ())
  (:mul ())
  (:div ())
  (:append ())
  (:reduce ())
  (:iota ())
  :pred prim-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum sort
  :short "Fixtype of sorts."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are associated to indices.
     They denote shapes and dimensions."))
  (:shape ())
  (:dim ())
  :pred sortp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod sorted-var
  :short "Fixtype of sorted variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A sorted variable consists of a variable name and an associated sort."))
  ((var string)
   (sort sort))
  :pred sorted-varp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist sorted-var-list
  :short "Fixtype of lists of sorted variables."
  :elt-type sorted-var
  :true-listp t
  :elementp-of-nil nil
  :pred sorted-var-listp)

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

(fty::deftypes indices
  :short "Fixtypes of indices and lists of indices."

  (fty::deftagsum index
    :parents (abstract-syntax indices)
    :short "Fixtype of indices."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       named variables,
       constants (natural numbers),
       shapes (consisting of zero or more dimensions),
       additions of indices,
       and concatenations of indices."))
    (:var ((name string)))
    (:const ((val nat)))
    (:shape ((indices index-list)))
    (:add ((indices index-list)))
    (:append ((indices index-list)))
    :pred indexp)

  (fty::deflist index-list
    :parents (abstract-syntax indices)
    :short "Fixtype of lists of indices."
    :elt-type index
    :true-listp t
    :elementp-of-nil nil
    :pred index-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes types
  :short "Fixtypes of types and lists of types."

  (fty::deftagsum type
    :parents (abstract-syntax types)
    :short "Fixtype of types."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       named variables,
       base types,
       array types (consisting of an atom type and an index),
       function types (with zero or more input types and an output type),
       universal types (quantified over kinded variables),
       product types (quantified over sorted variables),
       and sum types (quantified over sorted variables)."))
    (:var ((name string)))
    (:base ((type base-type)))
    (:array ((type type)
             (index index)))
    (:fun ((in type-list)
           (out type)))
    (:forall ((vars kinded-var-list)
              (type type)))
    (:pi ((vars sorted-var-list)
          (type type)))
    (:sigma ((vars sorted-var-list)
             (type type)))
    :pred typep)

  (fty::deflist type-list
    :parents (abstract-syntax types)
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

  (fty::deftagsum expr
    :parents (abstract-syntax exprs/atoms)
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
       The dissertation enforces non-emptiness with the patterns
       @($\\mathfrak{a}\\ \\mathfrak{a}\ldots$) and @($e\\ e\ldots$),
       while the arXiv paper does not."))
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
    (:unbox ((index-vars string-list)
             (term-var string)
             (target expr)
             (body expr)))
    :pred exprp)

  (fty::deflist expr-list
    :parents (abstract-syntax exprs/atoms)
    :short "Fixtype of lists of expressions."
    :elt-type expr
    :true-listp t
    :elementp-of-nil nil
    :pred expr-listp)

  (fty::deftagsum atom
    :parents (abstract-syntax exprs/atoms)
    :short "Fixtype of atoms."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       base values,
       primitive operators,
       lambda abstractions of expressions over typed variables,
       lambda abstractions of expressions over kinded variables,
       lambda abstractions of expressions over sorted variables,
       and boxed arrays with given indices and type.")
     (xdoc::p
      "The arXiv paper uses @($v$) as the body of type and index abstraction,
       while the dissertation uses @($e$), same as term abstraction.
       We use the latter, as that seems the intent."))
    (:base ((value base-value)))
    (:op ((op prim-op)))
    (:term-abs ((vars typed-var-list)
                (body expr)))
    (:type-abs ((vars kinded-var-list)
                (body expr)))
    (:index-abs ((vars sorted-var-list)
                 (body expr)))
    (:box ((indices index-list)
           (array expr)
           (type type)))
    :pred atomp)

  (fty::deflist atom-list
    :parents (abstract-syntax exprs/atoms)
    :short "Fixtype of lists of atoms."
    :elt-type atom
    :true-listp t
    :elementp-of-nil nil
    :pred atom-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum function
  :short "Fixtype of functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are primitive operators or expressions."))
  (:primop ((op prim-op)))
  (:expr ((expr expr)))
  :pred functionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum term
  :short "Fixtype of terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are atoms and term abstractions."))
  (:atom ((atom atom)))
  (:abs ((vars typed-var-list)
         (body expr)))
  :pred termp)
