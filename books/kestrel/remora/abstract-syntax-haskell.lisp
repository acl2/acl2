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
     We currently target [impl]'s unchecked ASTs,
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

(fty::deffold-reduce huncheckedp
    :short "Predicates on ASTs that characterize the subset
            corresponding to [impl]'s unchecked ASTs."
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
       "Variables with optional types that have no type,
        because [impl]'s @('PatId') holds a required type.")
      (xdoc::li
       "Atom expressions,
        because [impl] has no corresponding constructor.")
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
     (type :array (and (type-huncheckedp type.elem)
                       (ispace-huncheckedp type.ispace)
                       (ispace-case type.ispace :shape)))
     (type :bracket nil)
     (type :funn (and (type-list-huncheckedp type.in)
                      (type-huncheckedp type.out)
                      (consp type.in)
                      (endp (cdr type.in))))
     (var+type? (b* (((var+type? var+type?)))
                  (and (type-option-huncheckedp var+type?.type?)
                       (type-option-case var+type?.type? :some))))
     (expr :atom nil)
     (expr :string nil)
     (expr :appn nil)
     (expr :tappn nil)
     (expr :iappn nil)
     (expr :capp nil)
     (expr :unboxn nil)
     (expr :bracket nil)
     (atom :lambdan nil)
     (atom :tlambdan nil)
     (atom :ilambdan nil)
     (atom :boxn nil)
     (bind :fun (and (var+type?-list-huncheckedp bind.params)
                     (type-option-huncheckedp bind.type?)
                     (expr-huncheckedp bind.expr)
                     (consp bind.params)))
     (bind :tfun (and (type-option-huncheckedp bind.type?)
                      (expr-huncheckedp bind.expr)
                      (consp bind.params)))
     (bind :ifun (and (type-option-huncheckedp bind.type?)
                      (expr-huncheckedp bind.expr)
                      (consp bind.params)))
     (bind :cfun nil)
     (file (b* (((file file)))
             (and (decl-list-huncheckedp file.decls)
                  (endp file.imports)))))
    :name ast-huncheckedp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ast-huncheckedp-additional-theorems
    :short "Additional theorems about
            the Haskell implementation unchecked AST predicates."

    (defruled shape-huncheckedp-when-var
        (implies (shape-case shape :var)
                 (shape-huncheckedp shape))
      :enable shape-huncheckedp)

    (defruled shape-huncheckedp-when-dims
        (implies (shape-case shape :dims)
                 (equal (shape-huncheckedp shape)
                        (and (consp (shape-dims->dims shape))
                             (endp (cdr (shape-dims->dims shape))))))
      :enable shape-huncheckedp)

    (defruled not-shape-huncheckedp-when-splice
        (implies (equal (shape-kind shape) :splice)
                 (not (shape-huncheckedp shape)))
      :enable shape-huncheckedp)

    (defruled ispace-huncheckedp-when-dim
        (implies (ispace-case ispace :dim)
                 (ispace-huncheckedp ispace))
      :enable ispace-huncheckedp)

    (defruled type-huncheckedp-when-var
        (implies (type-case type :var)
                 (type-huncheckedp type))
      :enable type-huncheckedp)

    (defruled type-huncheckedp-when-base
        (implies (type-case type :base)
                 (type-huncheckedp type))
      :enable type-huncheckedp)

    (defruled type-huncheckedp-when-array
        (implies (type-case type :array)
                 (equal (type-huncheckedp type)
                        (and (type-huncheckedp (type-array->elem type))
                             (ispace-huncheckedp (type-array->ispace type))
                             (ispace-case (type-array->ispace type) :shape))))
      :enable type-huncheckedp)

    (defruled not-type-huncheckedp-when-array-with-dim
        (implies (and (equal (type-kind type) :array)
                      (equal (ispace-kind (type-array->ispace type)) :dim))
                 (not (type-huncheckedp type)))
      :enable type-huncheckedp)

    (defruled not-type-huncheckedp-when-bracket
        (implies (equal (type-kind type) :bracket)
                 (not (type-huncheckedp type)))
      :enable type-huncheckedp)

    (defruled type-huncheckedp-when-funn
        (implies (type-case type :funn)
                 (equal (type-huncheckedp type)
                        (and (type-list-huncheckedp (type-funn->in type))
                             (type-huncheckedp (type-funn->out type))
                             (consp (type-funn->in type))
                             (endp (cdr (type-funn->in type))))))
      :enable type-huncheckedp)

    (defruled type-huncheckedp-when-sigman
        (implies (type-case type :sigman)
                 (equal (type-huncheckedp type)
                        (and (type-huncheckedp (type-sigman->body type))
                             (consp (type-sigman->params type)))))
      :enable type-huncheckedp)

    (defruled type-option-huncheckedp-when-some
        (implies (type-option-case type? :some)
                 (equal (type-option-huncheckedp type?)
                        (type-huncheckedp (type-option-some->val type?))))
      :enable type-option-huncheckedp)

    (defruled var+type?-huncheckedp-when-type
        (implies (type-option-case (var+type?->type? vt) :some)
                 (equal (var+type?-huncheckedp vt)
                        (type-option-huncheckedp (var+type?->type? vt))))
      :enable var+type?-huncheckedp)

    (defruled not-var+type?-huncheckedp-when-no-type
        (implies (type-option-case (var+type?->type? vt) :none)
                 (not (var+type?-huncheckedp vt)))
      :enable var+type?-huncheckedp)

    (defruled expr-huncheckedp-when-var
        (implies (expr-case expr :var)
                 (expr-huncheckedp expr))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-atom
        (implies (equal (expr-kind expr) :atom)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled expr-huncheckedp-when-array
        (implies (expr-case expr :array)
                 (equal (expr-huncheckedp expr)
                        (and (atom-list-huncheckedp (expr-array->atoms expr))
                             (consp (expr-array->atoms expr)))))
      :enable expr-huncheckedp)

    (defruled expr-huncheckedp-when-frame
        (implies (expr-case expr :frame)
                 (equal (expr-huncheckedp expr)
                        (and (expr-list-huncheckedp (expr-frame->exprs expr))
                             (consp (expr-frame->exprs expr)))))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-string
        (implies (equal (expr-kind expr) :string)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-appn
        (implies (equal (expr-kind expr) :appn)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-tappn
        (implies (equal (expr-kind expr) :tappn)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-iappn
        (implies (equal (expr-kind expr) :iappn)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-capp
        (implies (equal (expr-kind expr) :capp)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-unboxn
        (implies (equal (expr-kind expr) :unboxn)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled not-expr-huncheckedp-when-bracket
        (implies (equal (expr-kind expr) :bracket)
                 (not (expr-huncheckedp expr)))
      :enable expr-huncheckedp)

    (defruled expr-huncheckedp-when-let
        (implies (expr-case expr :let)
                 (equal (expr-huncheckedp expr)
                        (and (bind-list-huncheckedp (expr-let->binds expr))
                             (expr-huncheckedp (expr-let->body expr)))))
      :enable expr-huncheckedp)

    (defruled atom-huncheckedp-when-base
        (implies (atom-case atom :base)
                 (atom-huncheckedp atom))
      :enable atom-huncheckedp)

    (defruled not-atom-huncheckedp-when-lambdan
        (implies (equal (atom-kind atom) :lambdan)
                 (not (atom-huncheckedp atom)))
      :enable atom-huncheckedp)

    (defruled not-atom-huncheckedp-when-tlambdan
        (implies (equal (atom-kind atom) :tlambdan)
                 (not (atom-huncheckedp atom)))
      :enable atom-huncheckedp)

    (defruled not-atom-huncheckedp-when-ilambdan
        (implies (equal (atom-kind atom) :ilambdan)
                 (not (atom-huncheckedp atom)))
      :enable atom-huncheckedp)

    (defruled not-atom-huncheckedp-when-boxn
        (implies (equal (atom-kind atom) :boxn)
                 (not (atom-huncheckedp atom)))
      :enable atom-huncheckedp)

    (defruled bind-huncheckedp-when-fun
        (implies (bind-case bind :fun)
                 (equal (bind-huncheckedp bind)
                        (and (var+type?-list-huncheckedp (bind-fun->params bind))
                             (type-option-huncheckedp (bind-fun->type? bind))
                             (expr-huncheckedp (bind-fun->expr bind))
                             (consp (bind-fun->params bind)))))
      :enable bind-huncheckedp)

    (defruled not-bind-huncheckedp-when-fun-without-params
        (implies (and (equal (bind-kind bind) :fun)
                      (endp (bind-fun->params bind)))
                 (not (bind-huncheckedp bind)))
      :enable bind-huncheckedp)

    (defruled bind-huncheckedp-when-tfun
        (implies (bind-case bind :tfun)
                 (equal (bind-huncheckedp bind)
                        (and (type-option-huncheckedp (bind-tfun->type? bind))
                             (expr-huncheckedp (bind-tfun->expr bind))
                             (consp (bind-tfun->params bind)))))
      :enable bind-huncheckedp)

    (defruled not-bind-huncheckedp-when-tfun-without-params
        (implies (and (equal (bind-kind bind) :tfun)
                      (endp (bind-tfun->params bind)))
                 (not (bind-huncheckedp bind)))
      :enable bind-huncheckedp)

    (defruled bind-huncheckedp-when-ifun
        (implies (bind-case bind :ifun)
                 (equal (bind-huncheckedp bind)
                        (and (type-option-huncheckedp (bind-ifun->type? bind))
                             (expr-huncheckedp (bind-ifun->expr bind))
                             (consp (bind-ifun->params bind)))))
      :enable bind-huncheckedp)

    (defruled not-bind-huncheckedp-when-ifun-without-params
        (implies (and (equal (bind-kind bind) :ifun)
                      (endp (bind-ifun->params bind)))
                 (not (bind-huncheckedp bind)))
      :enable bind-huncheckedp)

    (defruled not-bind-huncheckedp-when-cfun
        (implies (equal (bind-kind bind) :cfun)
                 (not (bind-huncheckedp bind)))
      :enable bind-huncheckedp)

    (defruled file-huncheckedp-when-no-imports
        (implies (endp (file->imports file))
                 (equal (file-huncheckedp file)
                        (decl-list-huncheckedp (file->decls file))))
      :enable file-huncheckedp)

    (defruled not-file-huncheckedp-when-imports
        (implies (consp (file->imports file))
                 (not (file-huncheckedp file)))
      :enable file-huncheckedp)

    (add-to-ruleset ast-huncheckedp-rules
                    '(shape-huncheckedp-when-var
                      shape-huncheckedp-when-dims
                      not-shape-huncheckedp-when-splice
                      ispace-huncheckedp-when-dim
                      type-huncheckedp-when-var
                      type-huncheckedp-when-base
                      type-huncheckedp-when-array
                      not-type-huncheckedp-when-array-with-dim
                      not-type-huncheckedp-when-bracket
                      type-huncheckedp-when-funn
                      type-huncheckedp-when-sigman
                      type-option-huncheckedp-when-some
                      var+type?-huncheckedp-when-type
                      not-var+type?-huncheckedp-when-no-type
                      expr-huncheckedp-when-var
                      not-expr-huncheckedp-when-atom
                      expr-huncheckedp-when-array
                      expr-huncheckedp-when-frame
                      not-expr-huncheckedp-when-string
                      not-expr-huncheckedp-when-appn
                      not-expr-huncheckedp-when-tappn
                      not-expr-huncheckedp-when-iappn
                      not-expr-huncheckedp-when-capp
                      not-expr-huncheckedp-when-unboxn
                      not-expr-huncheckedp-when-bracket
                      expr-huncheckedp-when-let
                      atom-huncheckedp-when-base
                      not-atom-huncheckedp-when-lambdan
                      not-atom-huncheckedp-when-tlambdan
                      not-atom-huncheckedp-when-ilambdan
                      not-atom-huncheckedp-when-boxn
                      bind-huncheckedp-when-fun
                      not-bind-huncheckedp-when-fun-without-params
                      bind-huncheckedp-when-tfun
                      not-bind-huncheckedp-when-tfun-without-params
                      bind-huncheckedp-when-ifun
                      not-bind-huncheckedp-when-ifun-without-params
                      not-bind-huncheckedp-when-cfun
                      file-huncheckedp-when-no-imports
                      not-file-huncheckedp-when-imports)))
