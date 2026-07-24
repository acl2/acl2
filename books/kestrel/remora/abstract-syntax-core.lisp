; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(include-book "lists")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-core
  :parents (abstract-syntax)
  :short "Core abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We characterize the subset of the ASTs
     that form the core of the language.
     This is mostly based on [thesis],
     but some choices are discussed in the documentation below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce corep
  :short "Predicates on ASTs that characterize the core subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "We exclude:")
   (xdoc::ul
    (xdoc::li
     "Shapes with non-singleton lists of dimensions,
      because they are expressible as concatenations of
      shapes with singleton lists of dimensions.")
    (xdoc::li
     "Shape splices,
      because they are expressible as concatenations.")
    (xdoc::li
     "Bracket types,
      because they are expressible as array types.")
    (xdoc::li
     "N-ary function types,
      because they are expressible as nests of one or more unary function types
      (one when the AST corresponds to a type @('(-> (T) R)'),
      i.e. with a parenthesized single input type).")
    (xdoc::li
     "N-ary universal, product, and sum types,
      because they are expressible as nests of
      two or more unary universal, product, and sum types.")
    (xdoc::li
     "Atom expressions,
      because they are expressible as 0-rank array expressions.")
    (xdoc::li
     "String literals,
      because they are expressible as array expressions.")
    (xdoc::li
     "Combined applications,
      because they are expressible as simpler applications.")
    (xdoc::li
     "Bracket expressions,
      because they are expressible as array expressions.")
    (xdoc::li
     "Function bindings,
      because they are expressible as value bindings
      (to lambda abstractions)."))
   (xdoc::p
    "Perhaps surprisingly, we do not exclude @('let') expressions,
     although one might expect that they should be reducible to
     applications of lambda abstractions:
     abstractly, @($(\\mathbf{let}\\ x = a\\ \\mathbf{in}\\ b)$)
     is equivalent to @($((\\lambda x.\\ b)\\ a)$).
     However, if we attempt to perform that transformation
     on Remora's @('let val') expressions,
     we run into the issue that the type is optional,
     but a lambda abstraction in Remora always needs a parameter type.
     For example, given")
   (xdoc::codeblock
    "(let ((val x a)) b)")
   (xdoc::p
    "where the optional type is omitted, we would need to turn that into")
   (xdoc::codeblock
    "((fn ((x ?)) b) a)")
   (xdoc::p
    "but, as signified by the @('?'), which is a required type,
     we do not know which type to use.
     This can be known via type checking,
     but the desugaring transformation is just a syntactic one,
     at least for now.")
   (xdoc::p
    "The issue could be avoided by doing beta reduction as part of desugaring.
     That is, speaking abstractly again,
     instead of turning @($(\\mathbf{let}\\ x = a\\ \\mathbf{in}\\ b)$)
     into @($((\\lambda x.\\ b)\\ a)$),
     we could turn that directly into @($b[x/a]$),
     by which we mean substituting
     each free occurrence of @($x$) in @($b$) with @($a$).
     However, substitution may need to rename bound variables to avoid capture,
     as done by our "
    (xdoc::seetopic "variable-substitution-alpha-operations"
                    "auto-alpha-renaming substitution operations")
    "; but both beta reduction and alpha renaming add conceptual complexity,
     partly due to the fact that there are many ways
     to alpha-rename bound variables to avoid capture;
     it is much simpler to generate an application of a lambda abstraction.")
   (xdoc::p
    "We have recently extended our abstract syntax to allow
     parameters of lambda abstractions without types.
     This would let us desugar @('let')s at the AST level,
     but the results may not have a concrete syntax counterpart.
     Thus. for now we keep @('let')s in the core.
     The Remora concrete syntax is likely to evolve
     towards requiring fewer type annotations,
     thus matching our current abstract syntax.")
   (xdoc::p
    "We desugar the four function bindings to value bindings.
     So the core has ispace, type, and value bindings.")
   (xdoc::p
    "We could also desugar ispace and type bindings
     to applications of ispace and type lambda abstractions,
     since their parameters are just ispace and type variables,
     which do not require anything extra (like types for term variables).
     We should also desugar @('let')s with multiple bindings
     to multiple @('let')s with single bindings."))
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          var+type?
          var+type?-list
          exprs/atoms/binds
          expr-list-list
          atom-list-list)
  :result booleanp
  :default t
  :combine and
  :override
  ((shape :dims (and (consp shape.dims)
                     (endp (cdr shape.dims))))
   (shape :splice nil)
   (type :bracket nil)
   (type :funn nil)
   (type :foralln nil)
   (type :pin nil)
   (type :sigman nil)
   (expr :atom nil)
   (expr :string nil)
   (expr :capp nil)
   (expr :bracket nil)
   (bind :fun nil)
   (bind :tfun nil)
   (bind :ifun nil)
   (bind :cfun nil))
  :name ast-corep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ast-corep-additional-theorems
  :short "Additional theorems about the core AST predicates."

  (defruled shape-corep-when-var
    (implies (shape-case shape :var)
             (shape-corep shape))
    :enable shape-corep)

  (defruled shape-corep-when-dims-and-singleton
    (implies (and (shape-case shape :dims)
                  (consp (shape-dims->dims shape))
                  (endp (cdr (shape-dims->dims shape))))
             (shape-corep shape))
    :enable shape-corep)

  (defruled ispace-corep-when-dim
    (implies (ispace-case ispace :dim)
             (ispace-corep ispace))
    :enable ispace-corep)

  (defruled type-corep-when-var
    (implies (type-case type :var)
             (type-corep type))
    :enable type-corep)

  (defruled type-corep-when-base
    (implies (type-case type :base)
             (type-corep type))
    :enable type-corep)

  (defruled expr-corep-when-var
    (implies (expr-case expr :var)
             (expr-corep expr))
    :enable expr-corep)

  (defruled atom-corep-when-base
    (implies (atom-case atom :base)
             (atom-corep atom))
    :enable atom-corep)

  (defruled not-bind-corep-when-fun
    (implies (equal (bind-kind bind) :fun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled not-bind-corep-when-tfun
    (implies (equal (bind-kind bind) :tfun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled not-bind-corep-when-ifun
    (implies (equal (bind-kind bind) :ifun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled not-bind-corep-when-cfun
    (implies (equal (bind-kind bind) :cfun)
             (not (bind-corep bind)))
    :enable bind-corep)

  (defruled expr-list-corep-of-append-all
    (equal (expr-list-corep (append-all exprss))
           (expr-list-list-corep exprss))
    :induct t
    :enable (append-all
             expr-list-corep-of-append
             expr-list-list-corep-of-cons
             expr-list-list-corep-when-atom))

  (defruled atom-list-corep-of-append-all
    (equal (atom-list-corep (append-all atomss))
           (atom-list-list-corep atomss))
    :induct t
    :enable (append-all
             atom-list-corep-of-append
             atom-list-list-corep-of-cons
             atom-list-list-corep-when-atom))

  (add-to-ruleset ast-corep-rules
                  '(shape-corep-when-var
                    shape-corep-when-dims-and-singleton
                    ispace-corep-when-dim
                    type-corep-when-var
                    type-corep-when-base
                    expr-corep-when-var
                    atom-corep-when-base
                    not-bind-corep-when-fun
                    not-bind-corep-when-tfun
                    not-bind-corep-when-ifun
                    not-bind-corep-when-cfun
                    expr-list-corep-of-append-all
                    atom-list-corep-of-append-all)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-theorems-about-structurals
  :short "Some theorems about
          the core AST predicates over some structural operations."

  (local (in-theory (enable* ast-corep-rules)))

  (defruled shape-list-corep-of-shape-dims-list-of-list-to-singletons
    (shape-list-corep (shape-dims-list (list-to-singletons dims)))
    :induct t
    :enable (list-to-singletons
             shape-corep-when-dims-and-singleton))

  (defrule atom-list-corep-of-atom-base-list
    (atom-list-corep (atom-base-list lits))
    :induct t
    :enable atom-base-list)

  (defrule atom-list-list-corep-of-expr-array-list->atoms
    (implies (and (expr-list-corep exprs)
                  (expr-list-case-array exprs))
             (atom-list-list-corep (expr-array-list->atoms exprs)))
    :induct t
    :enable expr-array-list->atoms)

  (defrule expr-list-list-corep-of-expr-frame-list->exprs
    (implies (and (expr-list-corep exprs)
                  (expr-list-case-frame exprs))
             (expr-list-list-corep (expr-frame-list->exprs exprs)))
    :induct t
    :enable expr-frame-list->exprs)

  (defrule shape-list-corep-of-ispace-shape-list->shape
    (implies (and (ispace-list-corep ispaces)
                  (ispace-list-case-shape ispaces))
             (shape-list-corep (ispace-shape-list->shape ispaces)))
    :induct t
    :enable ispace-shape-list->shape)

  (defruled type-corep-of-var+type?->type-or-err
    (implies (and (var+type?-corep x)
                  (not (reserrp (var+type?->type-or-err x))))
             (type-corep (var+type?->type-or-err x)))
    :enable var+type?->type-or-err)

  (defruled type-list-corep-of-var+type?-list->type-list
    (implies (and (var+type?-list-corep x)
                  (not (reserrp (var+type?-list->type-list-or-err x))))
             (type-list-corep (var+type?-list->type-list-or-err x)))
    :induct t
    :enable (var+type?-list->type-list-or-err
             type-corep-of-var+type?->type-or-err))

  (defrule type-corep-of-nest-fun-types
    (equal (type-corep (nest-fun-types in out))
           (and (type-list-corep in)
                (type-corep out)))
    :induct t
    :enable nest-fun-types)

  (defrule type-corep-of-nest-forall-types
    (equal (type-corep (nest-forall-types params body))
           (type-corep body))
    :induct t
    :enable nest-forall-types)

  (defrule type-corep-of-nest-pi-types
    (equal (type-corep (nest-pi-types params body))
           (type-corep body))
    :induct t
    :enable nest-pi-types)

  (defrule type-corep-of-nest-sigma-types
    (equal (type-corep (nest-sigma-types params body))
           (type-corep body))
    :induct t
    :enable nest-sigma-types))
