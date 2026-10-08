; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-derived-fixtypes")
(include-book "abstract-syntax-structurals")
(include-book "abstract-syntax-constructors")
(include-book "variable-substitution-operations")
(include-book "variable-substitution-alpha-operations")

(local (include-book "std/lists/no-duplicatesp" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable typep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-environments
  :parents (static-semantics)
  :short "Static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of
     the contextual information needed to
     enforce the static semantics of some AST.
     It is the static counterpart of a "
    (xdoc::seetopic "dynamic-semantics" "dynamic environment")
    ".")
   (xdoc::p
    "There are three kinds of static environments:
     for ispace variables, type variables, and expression variables.
     They correspond to, respectively,
     the sort environment @($\\Theta$),
     the kind environment @($\\Delta$), and
     the type environment @($\\Gamma$)
     in [thesis] [arxiv] [esop].
     The nomenclature in [thesis] [arxiv] [esop]
     refers to what is assigned to the variables:
     sorts to ispace variables,
     kinds to type variables,
     and types to expression variables.
     In our formalization,
     we use a nomenclature that refers to the variables instead:
     an ispace environment contains information about ispace variables;
     a type environment contains information about type variables; and
     an expression environment contains information about expression variables.
     There are two reasons for this terminological difference:")
   (xdoc::ul
    (xdoc::li
     "Our static environments do not quite assign
      sorts to ispace variables and kinds to type variables:
      sorts and kinds are part of our ASTs for ispace and type variables,
      and instead our static environments may assign
      ispaces and types to ispace and type variables,
      to capture definitions from @('let') bindings
      (see the details in the fixtype definitions for environments).")
    (xdoc::li
     "We want a clear correspondence between static and dynamic environments,
      but the latter assign
      ispace values to ispace variables,
      type values to type variables, and
      expression values to expression variables.
      None of these involve the assignment of sorts, kinds, or types."))
   (xdoc::p
    "The only terminological overlap and possible confusion
     between our formalization and [thesis] [arxiv] [esop]
     is then `type environments',
     which assign information to type variables in our formalization,
     while they assign types to (expression) variables
     in [thesis] [arxiv] [esop].
     This is not ideal, but we see no way around it,
     given the motivations above for our nomenclature.
     As a weak form of disambiguation,
     we can say that ours are actually
     `type static environments' and `type dynamic environments',
     while the ones in [thesis] [arxiv] [esop]
     are just `type environments' without qualification.
     However, when clear from context,
     we may just say `type environment'
     to mean either `type static environment' or `type dynamic environment',
     and we use the same abbreviations for
     ispace environments and expression environments as well.")
   (xdoc::p
    "In Remora, variables are in five separate name spaces:
     one for dimension variables,
     one for shape variables,
     one for atom types,
     one for array types,
     and one for expression variables.
     E.g. @('$x'), @('@x'), @('&x'), @('*x'), and @('x')
     are all distinct variables, despite the common @('x') part;
     indeed, they are distinguished by the prefixes.
     The variables in static environments are similarly separated."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ispace-senv
  :short "Fixtype of ispace static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "An ispace static environment is
     a map from the ispace variables in scope to optional ispaces.
     This corresponds to @($\\Theta$);
     since our ispace variables include their own sort,
     the keys suffice to capture the sorts,
     as opposed to a map from variables to sorts.
     The optional ispace associated to a variable:
     is absent when the variable is bound by an abstraction,
     i.e. it does not stand for any specific ispace;
     it is present when the variable is bound by a @('let')
     to a specific ispace, which is then its definition."))
  ((ispaces ispace-var-ispace-option-map))
  :pred ispace-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-senv
  :short "Fixtype of type static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type static environment is
     a map from the type variables in scope to optional types.
     This corresponds to @($\\Delta$);
     since our type variables include their own kind,
     the keys suffice to capture the kinds,
     as opposed to a map from variables to kinds.
     The optional type associated to a variable:
     is absent when the variable is bound by an abstraction,
     i.e. it does not stand for any specific type;
     it is present when the variable is bound by a @('let')
     to a specific type, which is then its definition."))
  ((types type-var-type-option-map))
  :pred type-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-senv
  :short "Fixtype of expression static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "An expression static environment is
     a map from the expression variables in scope to their types.
     This corresponds to @($\\Gamma$)."))
  ((exprs string-type-map))
  :pred expr-senvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-senv-result
  :short "Fixtype of expression static environments and errors."
  :ok expr-senv
  :pred expr-senv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-types ()
  :returns (expr-vars string-type-mapp)
  :short "Association of primitive operations to their types."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Remora, the primitive operations (i.e. built-in functions)
     are syntactically variables of (zero-rank array type of) a function type.
     These variables are implicitly in scope,
     and thus part of the initial static environment.
     Each operation's name (the map key) is its surface name in [impl].
     This is an initial selection of primitive operations;
     more will be added as the formalization grows.")
   (xdoc::p
    "The operations from @('+') to @('bool->f') have monomorphic types:
     function types between base types.
     The @('head'), @('tail'), @('length'),
     @('append'), @('reverse'), @('index'), @('index2d'),
     @('reshape'), @('flatten'), @('transpose2d'),
     @('reduce'), and @('fold') operations
     have polymorphic types:
     a universal type of a product type of a function type, as in [impl].
     The first input types of @('reduce') and @('fold')
     are themselves function types,
     making them higher-order operations.
     The @('sum') operation is polymorphic only in the shape,
     not in the element type, which is always integer:
     its type is a product type of a function type,
     without an enclosing universal type, as in [impl].
     The @('iota/static') operation is also polymorphic only in the shape:
     its type is a product type of an array type,
     without any function type, as in [impl],
     since the single ispace application directly yields the array.
     The @('iota') operation is polymorphic only in a dimension:
     its type is a product type of a function type
     whose output is an existential type, as in [impl],
     since the shape of the result depends on the argument's value,
     and is thus not known statically.
     The @('reify-dim') and @('reify-shape') operations are polymorphic
     only in a dimension and only in a shape, respectively:
     their types are product types of, respectively,
     the integer base type
     and an existential type of an integer array type,
     without any function type, as in [impl],
     since the single ispace application directly yields the result.
     The @('trace') operation returns its second argument,
     ignoring its first one,
     which the interpreter in [impl] prints as a side effect
     that we do not model;
     its type has two type parameters and two shape parameters,
     for the two arguments.
     The @('undefined') operation always fails, as in [impl]:
     like @('iota/static'), its type has no function type,
     so the last ispace application yields the (erroneous) result.
     All these types are atom-kinded, without zero-rank array type wrapping:
     as explained in @(see types),
     atom-kinded types are allowed wherever array-kinded types are expected,
     implicitly standing for zero-rank array types of those atom types."))
  (b* ((int-binop-type
        (t-> :int :int :int))
       (int-unop-type
        (t-> :int :int))
       (int-relop-type
        (t-> :int :int :bool))
       (int-to-float-type
        (t-> :int :float))
       (int-to-bool-type
        (t-> :int :bool))
       (float-binop-type
        (t-> :float :float :float))
       (float-unop-type
        (t-> :float :float))
       (float-relop-type
        (t-> :float :float :bool))
       (float-to-int-type
        (t-> :float :int))
       (bool-unop-type
        (t-> :bool :bool))
       (bool-binop-type
        (t-> :bool :bool :bool))
       (bool-to-int-type
        (t-> :bool :int))
       (bool-to-float-type
        (t-> :bool :float))
       (head-type
        (tfa "&t"
             (tpi ("$d" "@s")
                  (t-> (t[] "&t" (shp[] (dim+ 1 "$d") "@s"))
                       (t[] "&t" "@s")))))
       (tail-type
        (tfa "&t"
             (tpi ("$d" "@s")
                  (t-> (t[] "&t" (shp[] (dim+ 1 "$d") "@s"))
                       (t[] "&t" (shp[] "$d" "@s"))))))
       (length-type
        (tfa "&t"
             (tpi ("$d" "@s")
                  (t-> (t[] "&t" (shp[] "$d" "@s"))
                       :int))))
       (append-type
        (tfa "&t"
             (tpi ("$m" "$n" "@s")
                  (t-> (t[] "&t" (shp[] "$m" "@s"))
                       (t[] "&t" (shp[] "$n" "@s"))
                       (t[] "&t" (shp[] (dim+ "$m" "$n") "@s"))))))
       (reverse-type
        (tfa "&t"
             (tpi ("$d" "@s")
                  (t-> (t[] "&t" (shp[] "$d" "@s"))
                       (t[] "&t" (shp[] "$d" "@s"))))))
       (index-type
        (tfa "&t"
             (tpi "$m"
                  (t-> (t[] "&t" "$m")
                       :int
                       "&t"))))
       (index2d-type
        (tfa "&t"
             (tpi ("$m" "$n")
                  (t-> (t[] "&t" (shp[] "$m" "$n"))
                       (t[] :int (shp 2))
                       "&t"))))
       (sum-type
        (tpi "@s"
             (t-> (t[] :int "@s")
                  :int)))
       (reshape-type
        (tfa "&t"
             (tpi ("@s1" "@s2")
                  (t-> (t[] "&t" "@s1")
                       (t[] "&t" "@s2")))))
       (flatten-type
        (tfa "&t"
             (tpi ("$m" "$n" "@s")
                  (t-> (t[] "&t" (shp[] "$m" "$n" "@s"))
                       (t[] "&t" (shp[] (dim* "$m" "$n") "@s"))))))
       (transpose2d-type
        (tfa "&t"
             (tpi ("$m" "$n")
                  (t-> (t[] "&t" (shp[] "$m" "$n"))
                       (t[] "&t" (shp[] "$n" "$m"))))))
       (iota/static-type
        (tpi "@s"
             (t[] :int "@s")))
       (reduce-type
        (tfa "&t"
             (tpi ("$d" "@s")
                  (t-> (t-> (t[] "&t" "@s")
                            (t[] "&t" "@s")
                            (t[] "&t" "@s"))
                       (t[] "&t" (shp[] (dim+ 1 "$d") "@s"))
                       (t[] "&t" "@s")))))
       (fold-type
        (tfa ("&t" "&t2")
             (tpi ("$d" "@s" "@s2")
                  (t-> (t-> (t[] "&t2" "@s2")
                            (t[] "&t" "@s")
                            (t[] "&t2" "@s2"))
                       (t[] "&t2" "@s2")
                       (t[] "&t" (shp[] (dim+ 1 "$d") "@s"))
                       (t[] "&t2" "@s2")))))
       (reify-dim-type
        (tpi "$d" :int))
       (reify-shape-type
        (tpi "@s"
             (tsi "$r"
                  (t[] :int (shp "$r")))))
       (iota-type
        (tpi "$d"
             (t-> (t[] :int (shp "$d"))
                  (tsi "@s"
                       (t[] :int "@s")))))
       (trace-type
        (tfa ("&t" "&r")
             (tpi ("@s" "@q")
                  (t-> (t[] "&t" "@s")
                       (t[] "&r" "@q")
                       (t[] "&r" "@q")))))
       (undefined-type
        (tfa "&t"
             (tpi "@s"
                  (t[] "&t" "@s")))))
    (omap::from-alist
     (list$ (cons "+" int-binop-type)
            (cons "-" int-binop-type)
            (cons "*" int-binop-type)
            (cons "/" int-binop-type)
            (cons "^" int-binop-type)
            (cons "mod" int-binop-type)
            (cons "max" int-binop-type)
            (cons "min" int-binop-type)
            (cons "bit-and" int-binop-type)
            (cons "bit-or" int-binop-type)
            (cons "bit-xor" int-binop-type)
            (cons "shl" int-binop-type)
            (cons "shr" int-binop-type)
            (cons "bit-not" int-unop-type)
            (cons "popc" int-unop-type)
            (cons "==" int-relop-type)
            (cons "!=" int-relop-type)
            (cons "<" int-relop-type)
            (cons ">" int-relop-type)
            (cons "<=" int-relop-type)
            (cons ">=" int-relop-type)
            (cons "i->f" int-to-float-type)
            (cons "i->bool" int-to-bool-type)
            (cons "f.+" float-binop-type)
            (cons "f.-" float-binop-type)
            (cons "f.*" float-binop-type)
            (cons "f./" float-binop-type)
            (cons "f.^" float-binop-type)
            (cons "f.max" float-binop-type)
            (cons "f.min" float-binop-type)
            (cons "sqrt" float-unop-type)
            (cons "f.sqrt" float-unop-type)
            (cons "f.==" float-relop-type)
            (cons "f.!=" float-relop-type)
            (cons "f.<" float-relop-type)
            (cons "f.>" float-relop-type)
            (cons "f.<=" float-relop-type)
            (cons "f.>=" float-relop-type)
            (cons "truncate" float-to-int-type)
            (cons "round" float-to-int-type)
            (cons "ceiling" float-to-int-type)
            (cons "floor" float-to-int-type)
            (cons "not" bool-unop-type)
            (cons "and" bool-binop-type)
            (cons "or" bool-binop-type)
            (cons "bool.==" bool-binop-type)
            (cons "bool.!=" bool-binop-type)
            (cons "bool->i" bool-to-int-type)
            (cons "bool->f" bool-to-float-type)
            (cons "head" head-type)
            (cons "tail" tail-type)
            (cons "length" length-type)
            (cons "append" append-type)
            (cons "reverse" reverse-type)
            (cons "index" index-type)
            (cons "index2d" index2d-type)
            (cons "sum" sum-type)
            (cons "reshape" reshape-type)
            (cons "flatten" flatten-type)
            (cons "transpose2d" transpose2d-type)
            (cons "iota/static" iota/static-type)
            (cons "reduce" reduce-type)
            (cons "fold" fold-type)
            (cons "reify-dim" reify-dim-type)
            (cons "reify-shape" reify-shape-type)
            (cons "iota" iota-type)
            (cons "trace" trace-type)
            (cons "undefined" undefined-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-ispace-senv ()
  :returns (ienv ispace-senvp)
  :short "Initial ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, ispace static environment.
     It is empty."))
  (ispace-senv nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-type-senv ()
  :returns (tenv type-senvp)
  :short "Initial type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, type static environment.
     It is empty."))
  (type-senv nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-expr-senv ()
  :returns (eenv expr-senvp)
  :short "Initial expression static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, expression static environment.
     It contains the primitive operations."))
  (expr-senv (primop-types)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-add-var ((var ispace-varp) (ienv ispace-senvp))
  :returns (new-ienv ispace-senvp)
  :short "Add an ispace variable to the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with an absent associated ispace,
     because it does not stand for any specific ispace;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-ispace-senv ienv
                      :ispaces (omap::update (ispace-var-fix var)
                                             nil
                                             (ispace-senv->ispaces ienv))))

;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-add-vars ((vars ispace-var-listp) (ienv ispace-senvp))
  :returns (new-ienv ispace-senvp)
  :short "Add zero or more ispace variables to the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee ispace-senv-add-var),
     which this function repeats for each variable."))
  (b* (((when (endp vars)) (ispace-senv-fix ienv))
       (ienv (ispace-senv-add-var (car vars) ienv)))
    (ispace-senv-add-vars (cdr vars) ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-senv-add-var ((var type-varp) (tenv type-senvp))
  :returns (new-tenv type-senvp)
  :short "Add a type variable to the type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with an absent associated type,
     because it does not stand for any specific type;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-type-senv tenv
                    :types (omap::update (type-var-fix var)
                                         nil
                                         (type-senv->types tenv))))

;;;;;;;;;;;;;;;;;;;;

(define type-senv-add-vars ((vars type-var-listp) (tenv type-senvp))
  :returns (new-tenv type-senvp)
  :short "Add zero or more type variables to the type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee type-senv-add-var),
     which this function repeats for each variable."))
  (b* (((when (endp vars)) (type-senv-fix tenv))
       (tenv (type-senv-add-var (car vars) tenv)))
    (type-senv-add-vars (cdr vars) tenv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-senv-add-def ((var ispace-varp)
                             (ispace ispacep)
                             (ienv ispace-senvp))
  :returns (new-ienv ispace-senvp)
  :short "Add an ispace variable with its ispace definition
          to the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with a present associated ispace,
     namely its definition;
     this is the case for variables bound by @('let')s.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-ispace-senv ienv
                      :ispaces (omap::update (ispace-var-fix var)
                                             (ispace-fix ispace)
                                             (ispace-senv->ispaces ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-senv-add-def ((var type-varp) (type typep) (tenv type-senvp))
  :returns (new-tenv type-senvp)
  :short "Add a type variable with its type definition
          to the type static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with a present associated type,
     namely its definition;
     this is the case for variables bound by @('let')s.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-type-senv tenv
                    :types (omap::update (type-var-fix var)
                                         (type-fix type)
                                         (type-senv->types tenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-senv-add-var ((var stringp) (type typep) (eenv expr-senvp))
  :returns (new-eenv expr-senvp)
  :short "Add a variable with a type to the expression static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since variables are expressions, the type must be an array type.
     So we auto-lift atom types to scalar array types if needed.")
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-senv eenv
                    :exprs (omap::update (str::str-fix var)
                                         (type-ensure-array type)
                                         (expr-senv->exprs eenv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-senv-add-vars ((vars+types var+type?-listp) (eenv expr-senvp))
  :guard (no-duplicatesp-equal (var+type?-list->var vars+types))
  :returns (new-eenv expr-senv-resultp)
  :short "Add zero or more variables with types
          to the expression static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function actually takes a list of variables with optional types,
     but it fails if some type is missing.")
   (xdoc::p
    "This repeatedly calls @(tsee expr-senv-add-var).
     The guard ensures that the order of the list does not matter.")
   (xdoc::p
    "Since we do not perform type inference yet,
     this fails if any of the variables has no type."))
  (b* (((when (endp vars+types)) (expr-senv-fix eenv))
       (vt (car vars+types))
       ((ok type) (var+type?->type-or-err vt))
       (eenv (expr-senv-add-var (var+type?->var vt) type eenv)))
    (expr-senv-add-vars (cdr vars+types) eenv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-ispace-subst ((map ispace-var-ispace-option-mapp))
  :returns (subst stringdimmap+stringshapemap-p)
  :short "Turn a map from ispace variables to optional ispaces
          into the ispace variable substitution
          determined by the definitions in the map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn
     the map in an ispace static environment
     into a dimension substitution and a shape substitution,
     consisting of the variables that have a definition
     (i.e. a present optional ispace);
     variables without an ispace do not contribute.
     A dimension variable maps to the dimension of its (dimension) ispace,
     and a shape variable maps to the shape of its (shape) ispace.")
   (xdoc::p
    "It should never be the case that the map violates sorts,
     i.e. associates a dimension variable to a shape ispace
     or a shape variable to a dimension ispace.
     But we do not have that static invariant yet,
     so we defensively throw an error if that happens."))
  (b* (((when (omap::emptyp (ispace-var-ispace-option-map-fix map)))
        (make-stringdimmap+stringshapemap :dim-map nil :shape-map nil))
       ((mv var ispace?) (omap::head map))
       ((stringdimmap+stringshapemap subst-rest)
        (senv-ispace-subst (omap::tail map))))
    (ispace-option-case
     ispace?
     :none subst-rest
     :some
     (ispace-var-case
      var
      :dim (ispace-case
            ispace?.val
            :dim (change-stringdimmap+stringshapemap
                  subst-rest
                  :dim-map (omap::update var.name
                                         ispace?.val.dim
                                         subst-rest.dim-map))
            :shape (prog2$ (raise "Internal error: ~
                                   dimension variable ~x0 ~
                                   is associated with ~
                                   shape ispace ~x1."
                                  var ispace?.val)
                           subst-rest))
      :shape (ispace-case
              ispace?.val
              :dim (prog2$ (raise "Internal error: ~
                                   shape variable ~x0 ~
                                   is associated with ~
                                   dimension ispace ~x1."
                                  var ispace?.val)
                           subst-rest)
              :shape (change-stringdimmap+stringshapemap
                      subst-rest
                      :shape-map (omap::update var.name
                                               ispace?.val.shape
                                               subst-rest.shape-map))))))
  :no-function nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-type-subst ((map type-var-type-option-mapp))
  :returns (subst string-type-map-pairp)
  :short "Turn a map from type variables to optional types
          into the type variable substitution
          determined by the definitions in the map."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn
     the map in a type static environment
     into an atom-kind type substitution and an array-kind type substitution,
     consisting of the variables that have a definition
     (i.e. a present optional type);
     variables without a type do not contribute.
     An atom type variable maps to its (atom-kind) type,
     and an array type variable maps to its (array-kind) type.")
   (xdoc::p
    "It should never be the case that the map violates kinds,
     i.e. associates an atom type variable to an array-kind type
     or an array type variable to an atom-kind type.
     But we do not have that static invariant yet,
     so we defensively throw an error if that happens."))
  (b* (((when (omap::emptyp (type-var-type-option-map-fix map)))
        (make-string-type-map-pair :1st nil :2nd nil))
       ((mv var type?) (omap::head map))
       ((string-type-map-pair subst-rest)
        (senv-type-subst (omap::tail map))))
    (type-option-case
     type?
     :none subst-rest
     :some
     (type-var-case
      var
      :atom (if (type-atom-kindp type?.val)
                (change-string-type-map-pair
                 subst-rest
                 :1st (omap::update var.name type?.val subst-rest.1st))
              (prog2$ (raise "Internal error: ~
                              atom type variable ~x0 ~
                              is associated with ~
                              array-kind type ~x1."
                             var type?.val)
                      subst-rest))
      :array (if (type-atom-kindp type?.val)
                 (prog2$ (raise "Internal error: ~
                                 array type variable ~x0 ~
                                 is associated with ~
                                 atom-kind type ~x1."
                                var type?.val)
                         subst-rest)
               (change-string-type-map-pair
                subst-rest
                :2nd (omap::update var.name type?.val subst-rest.2nd))))))
  :no-function nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-shape ((shape shapep) (ienv ispace-senvp))
  :returns (new-shape shapep)
  :short "Expand a shape using the ispace definitions
          in the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the shape
     with its definition (see @(tsee senv-ispace-subst)).
     Since shapes contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (senv-ispace-subst (ispace-senv->ispaces ienv))))
    (shape-subst-ispace-vars shape subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-ispace ((ispace ispacep) (ienv ispace-senvp))
  :returns (new-ispace ispacep)
  :short "Expand an ispace using the ispace definitions
          in the ispace static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined ispace variable in the ispace
     with its definition (see @(tsee senv-ispace-subst)).
     Since ispaces contain no binders, this substitution cannot capture."))
  (b* (((stringdimmap+stringshapemap subst)
        (senv-ispace-subst (ispace-senv->ispaces ienv))))
    (ispace-subst-ispace-vars ispace subst.dim-map subst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection senv-expand-ispace-list ((x ispace-listp)
                                             (ienv ispace-senvp))
  :returns (new-ispaces ispace-listp)
  :short "Lift @(tsee senv-expand-ispace) to lists of ispaces."
  (senv-expand-ispace x ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-expand-type ((type typep) (ienv ispace-senvp) (tenv type-senvp))
  :returns (new-type type-resultp)
  :short "Expand a type using the definitions in the static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "We replace every defined type variable and ispace variable in the type
     with its definition
     (see @(tsee senv-type-subst) and @(tsee senv-ispace-subst)).
     We substitute the type variables first, and the ispace variables second.
     Since types may contain ispaces but not vice versa,
     substituting the type definitions first may expose
     additional ispace variables, occurring in those definitions,
     which the subsequent ispace substitution then replaces.
     Since the definitions in the static environments are fully expanded
     (i.e. they contain no defined variables),
     the result would be the same with the opposite order;
     but this order does not rely on
     the definitions in the static environments being fully expanded.")
   (xdoc::p
    "Because types contain binders (universal, product, and sum types),
     the substitution could result in variable capture;
     the capture-avoiding substitutions
     @(tsee type-subst-type-vars-alpha) and @(tsee type-subst-ispace-vars-alpha)
     automatically alpha-rename the bound variables as needed to avoid it."))
  (b* (((string-type-map-pair tsubst)
        (senv-type-subst (type-senv->types tenv)))
       (type (type-subst-type-vars-alpha type tsubst.1st tsubst.2nd))
       ((stringdimmap+stringshapemap isubst)
        (senv-ispace-subst (ispace-senv->ispaces ienv))))
    (type-subst-ispace-vars-alpha type isubst.dim-map isubst.shape-map)))

;;;;;;;;;;;;;;;;;;;;

(define senv-expand-type-list ((types type-listp)
                               (ienv ispace-senvp)
                               (tenv type-senvp))
  :returns (new-types type-list-resultp
                      :hints
                      (("Goal"
                        :induct t
                        :in-theory (enable type-listp-when-result-not-error))))
  :short "Lift @(tsee senv-expand-type) to lists."
  (b* (((when (endp types)) nil)
       ((ok type) (senv-expand-type (car types) ienv tenv))
       ((ok types) (senv-expand-type-list (cdr types) ienv tenv)))
    (cons type types))
  :verify-guards :after-returns)
