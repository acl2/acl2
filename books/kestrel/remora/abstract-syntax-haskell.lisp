; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Sarah Johnson

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-haskell
  :parents (abstract-syntax)
  :short "Haskell implementation abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We characterize the subset of the ASTs
     that corresponds exactly to the ASTs of [impl].
     We specifically target [impl]'s unchecked ASTs,
     @('ProgBase TypeExp TypeParamExp NoInfo Text')
     (aliased as @('UncheckedProg'))
     along with its constituent AST types.
     That is the instantiation our AST fixtypes mirror:
     types are source-level
     (they include array type variables,
     their quantifiers are n-ary, and
     they do not separate atom types from array types),
     type parameters are source-level as well
     (they include array type parameters),
     type annotations are empty, and
     variables are names without tags.")
   (xdoc::p
    "The characterization is determined by
     the declarations of [impl]'s AST types alone,
     not by which of their values any [impl] pass happens to build.
     An AST of ours is in the subset when its constructors and fields
     can be matched with those of [impl]'s constructors,
     where a field of ours holding a list
     matches a field of [impl] holding a single value
     just when the list is a singleton,
     and matches a field of [impl] holding a @('NonEmpty')
     just when the list is not empty.
     Note that this does not require the correspondence to be injective:
     two ASTs of ours may match the same AST of [impl].
     For instance, both @('(-> T R)') and @('(-> (T) R)')
     match @('TEArrow'),
     because our ASTs preserve the parenthesization of
     the input type of a unary function type, whereas [impl]'s do not."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce hip
    :short "Predicates on ASTs that characterize the subset
            corresponding to [impl]."
    :long
    (xdoc::topstring
     (xdoc::p
      "We exclude:")
     (xdoc::ul
      (xdoc::li
       "Shapes with non-singleton lists of dimensions,
        because [impl]'s @('ShapeDim') holds exactly one dimension.")
      (xdoc::li
       "Shape splices,
        because [impl] has no corresponding constructor.")
      (xdoc::li
       "Array types with non-shape ispaces,
        because [impl]'s @('TEArray') holds a @('Shape'), not an @('ISpace').")
      (xdoc::li
       "Bracket types,
        because [impl] has no corresponding constructor.")
      (xdoc::li
       "N-ary function types with non-singleton lists of input types,
        because [impl]'s @('TEArrow') holds exactly one input type.")
      (xdoc::li
       "Sum types with empty lists of parameters
        (will be removed once length invariant is in place).")
; Todo: remove above once invariant is in place
      (xdoc::li
       "Variables with optional types that have no type,
        because [impl]'s @('PatId') holds a required type.")
      (xdoc::li
       "Atom expressions,
        because [impl] has no corresponding constructor.")
      (xdoc::li
       "Array expressions with empty lists of atoms
        (will be removed once length invariant is in place).")
; Todo: remove above once invariant is in place
      (xdoc::li
       "Frame expressions with empty lists of expressions
        (will be removed once length invariant is in place).")
; Todo: remove above once invariant is in place
      (xdoc::li
       "String expressions,
        because [impl] has no corresponding constructor.")
      (xdoc::li
       "N-ary application expressions,
        because [impl]'s @('App') holds exactly one argument.")
      (xdoc::li
       "N-ary type application expressions,
        because [impl]'s @('TApp') holds exactly one argument.")
      (xdoc::li
       "N-ary ispace application expressions,
        because [impl]'s @('IApp') holds exactly one argument.")
      (xdoc::li
       "Combined application expressions,
        because [impl] has no corresponding constructor.")
      (xdoc::li
       "N-ary unboxing expressions,
        because [impl]'s @('Unbox') holds exactly one ispace.")
      (xdoc::li
       "Bracket expressions,
        because [impl] has no corresponding constructor.")
      (xdoc::li
       "Let expressions with empty lists of binds
        (will be removed once length invariant is in place).")
      (xdoc::li
       "N-ary lambda abstractions,
        because [impl]'s @('Lambda') holds exactly one parameter.")
      (xdoc::li
       "N-ary type lambda abstractions,
        because [impl]'s @('TLambda') holds exactly one parameter.")
      (xdoc::li
       "N-ary ispace lambda abstractions,
        because [impl]'s @('ILambda') holds exactly one parameter.")
      (xdoc::li
       "N-ary boxing atoms,
        because [impl]'s @('Box') holds exactly one ispace.")
      (xdoc::li
       "Function bindings with empty lists of parameters,
        because [impl]'s @('BindFun') holds a @('NonEmpty') list of parameters.")
      (xdoc::li
       "Type function bindings with empty lists of parameters,
        because [impl]'s @('BindTFun') holds a @('NonEmpty') list of parameters.")
      (xdoc::li
       "Ispace function bindings with empty lists of parameters,
        because [impl]'s @('BindIFun') holds a @('NonEmpty') list of parameters.")
      (xdoc::li
       "Combined function bindings,
        because [impl] has no corresponding constructor.")
; Todo: remove above once invariant is in place
      (xdoc::li
       "Files with non-empty lists of imports,
        because [impl]'s @('ProgBase') has no imports field")
      ))
    :types (shapes/ispaces
            types
            type-option
            var+type?
            var+type?-list
            exprs/atoms/binds
            decl
            decl-list
            file)
    :result booleanp
    :default t
    :combine and
    :override
    ((shape :dims (and (consp shape.dims)
                       (endp (cdr shape.dims))))
     (shape :splice nil)
     (type :array (and (type-hip type.elem)
                       (ispace-hip type.ispace)
                       (ispace-case type.ispace :shape)))
     (type :bracket nil)
     (type :funn (and (type-list-hip type.in)
                      (type-hip type.out)
                      (consp type.in)
                      (endp (cdr type.in))))
     (type :sigman (and (type-hip type.body)
                        (consp type.params))) ; Todo: remove once invariant is in place
     (var+type? (b* (((var+type? var+type?)))
                  (and (type-option-hip var+type?.type?)
                       (type-option-case var+type?.type? :some))))
     (expr :atom nil)
     (expr :array (and (atom-list-hip expr.atoms)
                       (consp expr.atoms))) ; Todo: remove once invariant is in place
     (expr :frame (and (expr-list-hip expr.exprs)
                       (consp expr.exprs))) ; Todo: remove once invariant is in place
     (expr :string nil)
     (expr :appn nil)
     (expr :tappn nil)
     (expr :iappn nil)
     (expr :capp nil)
     (expr :unboxn nil)
     (expr :bracket nil)
     (expr :let (and (bind-list-hip expr.binds)
                     (expr-hip expr.body)
                     (consp expr.binds))) ; Todo: remove once invariant is in place
     (atom :lambdan nil)
     (atom :tlambdan nil)
     (atom :ilambdan nil)
     (atom :boxn nil)
     (bind :fun (and (var+type?-list-hip bind.params)
                     (type-option-hip bind.type?)
                     (expr-hip bind.expr)
                     (consp bind.params)))
     (bind :tfun (and (type-option-hip bind.type?)
                      (expr-hip bind.expr)
                      (consp bind.params)))
     (bind :ifun (and (type-option-hip bind.type?)
                      (expr-hip bind.expr)
                      (consp bind.params)))
     (bind :cfun nil)
     (file (b* (((file file)))
             (and (decl-list-hip file.decls)
                  (endp file.imports)))))
    :name ast-hip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ast-hip-additional-theorems
    :short "Additional theorems about
            the Haskell implementation AST predicates."

    (defruled shape-hip-when-var
        (implies (shape-case shape :var)
                 (shape-hip shape))
      :enable shape-hip)

    (defruled shape-hip-when-dims
        (implies (shape-case shape :dims)
                 (equal (shape-hip shape)
                        (and (consp (shape-dims->dims shape))
                             (endp (cdr (shape-dims->dims shape))))))
      :enable shape-hip)

    (defruled not-shape-hip-when-splice
        (implies (equal (shape-kind shape) :splice)
                 (not (shape-hip shape)))
      :enable shape-hip)

    (defruled ispace-hip-when-dim
        (implies (ispace-case ispace :dim)
                 (ispace-hip ispace))
      :enable ispace-hip)

    (defruled type-hip-when-var
        (implies (type-case type :var)
                 (type-hip type))
      :enable type-hip)

    (defruled type-hip-when-base
        (implies (type-case type :base)
                 (type-hip type))
      :enable type-hip)

    (defruled not-type-hip-when-array-with-dim
        (implies (and (equal (type-kind type) :array)
                      (equal (ispace-kind (type-array->ispace type)) :dim))
                 (not (type-hip type)))
      :enable type-hip)

    (defruled not-type-hip-when-bracket
        (implies (equal (type-kind type) :bracket)
                 (not (type-hip type)))
      :enable type-hip)

    (defruled type-hip-when-funn
        (implies (type-case type :funn)
                 (equal (type-hip type)
                        (and (type-list-hip (type-funn->in type))
                             (type-hip (type-funn->out type))
                             (consp (type-funn->in type))
                             (endp (cdr (type-funn->in type))))))
      :enable type-hip)

    (defruled not-var+type?-hip-when-no-type
        (implies (type-option-case (var+type?->type? vt) :none)
                 (not (var+type?-hip vt)))
      :enable var+type?-hip)

    (defruled expr-hip-when-var
        (implies (expr-case expr :var)
                 (expr-hip expr))
      :enable expr-hip)

    (defruled not-expr-hip-when-atom
        (implies (equal (expr-kind expr) :atom)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-string
        (implies (equal (expr-kind expr) :string)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-appn
        (implies (equal (expr-kind expr) :appn)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-tappn
        (implies (equal (expr-kind expr) :tappn)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-iappn
        (implies (equal (expr-kind expr) :iappn)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-capp
        (implies (equal (expr-kind expr) :capp)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-unboxn
        (implies (equal (expr-kind expr) :unboxn)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled not-expr-hip-when-bracket
        (implies (equal (expr-kind expr) :bracket)
                 (not (expr-hip expr)))
      :enable expr-hip)

    (defruled atom-hip-when-base
        (implies (atom-case atom :base)
                 (atom-hip atom))
      :enable atom-hip)

    (defruled not-atom-hip-when-lambdan
        (implies (equal (atom-kind atom) :lambdan)
                 (not (atom-hip atom)))
      :enable atom-hip)

    (defruled not-atom-hip-when-tlambdan
        (implies (equal (atom-kind atom) :tlambdan)
                 (not (atom-hip atom)))
      :enable atom-hip)

    (defruled not-atom-hip-when-ilambdan
        (implies (equal (atom-kind atom) :ilambdan)
                 (not (atom-hip atom)))
      :enable atom-hip)

    (defruled not-atom-hip-when-boxn
        (implies (equal (atom-kind atom) :boxn)
                 (not (atom-hip atom)))
      :enable atom-hip)

    (defruled not-bind-hip-when-fun-without-params
        (implies (and (equal (bind-kind bind) :fun)
                      (endp (bind-fun->params bind)))
                 (not (bind-hip bind)))
      :enable bind-hip)

    (defruled not-bind-hip-when-tfun-without-params
        (implies (and (equal (bind-kind bind) :tfun)
                      (endp (bind-tfun->params bind)))
                 (not (bind-hip bind)))
      :enable bind-hip)

    (defruled not-bind-hip-when-ifun-without-params
        (implies (and (equal (bind-kind bind) :ifun)
                      (endp (bind-ifun->params bind)))
                 (not (bind-hip bind)))
      :enable bind-hip)

    (defruled not-bind-hip-when-cfun
        (implies (equal (bind-kind bind) :cfun)
                 (not (bind-hip bind)))
      :enable bind-hip)

    (defruled not-file-hip-when-imports
        (implies (consp (file->imports file))
                 (not (file-hip file)))
      :enable file-hip)

    (add-to-ruleset ast-hip-rules
                    '(shape-hip-when-var
                      shape-hip-when-dims
                      not-shape-hip-when-splice
                      ispace-hip-when-dim
                      type-hip-when-var
                      type-hip-when-base
                      not-type-hip-when-array-with-dim
                      not-type-hip-when-bracket
                      type-hip-when-funn
                      not-var+type?-hip-when-no-type
                      expr-hip-when-var
                      not-expr-hip-when-atom
                      not-expr-hip-when-string
                      not-expr-hip-when-appn
                      not-expr-hip-when-tappn
                      not-expr-hip-when-iappn
                      not-expr-hip-when-capp
                      not-expr-hip-when-unboxn
                      not-expr-hip-when-bracket
                      atom-hip-when-base
                      not-atom-hip-when-lambdan
                      not-atom-hip-when-tlambdan
                      not-atom-hip-when-ilambdan
                      not-atom-hip-when-boxn
                      not-bind-hip-when-fun-without-params
                      not-bind-hip-when-tfun-without-params
                      not-bind-hip-when-ifun-without-params
                      not-bind-hip-when-cfun
                      not-file-hip-when-imports)))
