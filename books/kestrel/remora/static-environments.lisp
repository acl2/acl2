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
    "Our static environments correspond to the combination of
     the sort environment @($\\Theta$),
     the kind environment @($\\Delta$), and
     the type environment @($\\Gamma$)
     in [thesis], [arxiv], and [esop]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senv
  :short "Fixtype of static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of:")
   (xdoc::ul
    (xdoc::li
     "A map from the ispace variables in scope to optional ispaces.
      This corresponds to @($\\Theta$);
      since our ispace variables include their own sort,
      the keys suffice to capture the sorts,
      as opposed to a map from variables to sorts.
      The optional ispace associated to a variable is absent
      when the variable is bound by an abstraction,
      i.e. it does not stand for any specific ispace;
      it is present when the variable is bound by a @('let')
      to a specific ispace, which is then its definition.
      The definitions are taken into account
      by ispace and type equivalence.")
    (xdoc::li
     "A map from the type variables in scope to optional types.
      This corresponds to @($\\Delta$);
      since our type variables include their own kind,
      the keys suffice to capture the kinds,
      as opposed to a map from variables to kinds.
      The optional type is absent or present,
      and is used analogously to the ispace variables described above.")
    (xdoc::li
     "A map from the expression variables in scope to their types.
      This corresponds to @($\\Gamma$)."))
   (xdoc::p
    "Variables are in five separate name spaces:
     one for dimension variables,
     one for shape variables,
     one for atom types,
     one for array types,
     and one for expression variables.
     E.g. @('$x'), @('@x'), @('&x'), @('*x'), and @('x')
     are all distinct variables, despite the common @('x') part;
     indeed, they are distinguished by the prefixes.
     The variables in a static environment are similarly separated,
     in the three components and via fixtype sum tags."))
  ((ispace-vars ispace-var-ispace-option-map)
   (type-vars type-var-type-option-map)
   (expr-vars string-type-map))
  :pred senvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult senv-result
  :short "Fixtype of static environments and errors."
  :ok senv
  :pred senv-resultp)

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
     and thus part of the initial static environment.")
   (xdoc::p
    "Each operation's name (the map key) is its surface name
     in [impl]'s prelude (the file @('RemoraPrelude.hs'));
     the dynamic semantics of these operations
     is formalized in @(see primitives-evaluation).
     This is an initial selection of primitive operations;
     more will be added as the formalization grows.")
   (xdoc::p
    "The operations from @('+') to @('bool->f') have monomorphic types:
     zero-rank array types of function types between base types.
     The @('head'), @('tail'), @('length'),
     @('append'), and @('reverse') operations
     have polymorphic types:
     a universal type of a product type of a function type, as in [impl].
     Like the monomorphic types,
     the whole type is a zero-rank array type,
     but the bodies of the universal and product types
     need no zero-rank array wrapping,
     because atom types are auto-lifted to array types in those places."))
  (b* ((int-binop-type
        (t[] (t-> (:int :int) :int) (shp)))
       (int-unop-type
        (t[] (t-> (:int) :int) (shp)))
       (int-relop-type
        (t[] (t-> (:int :int) :bool) (shp)))
       (int-to-float-type
        (t[] (t-> (:int) :float) (shp)))
       (int-to-bool-type
        (t[] (t-> (:int) :bool) (shp)))
       (float-binop-type
        (t[] (t-> (:float :float) :float) (shp)))
       (float-unop-type
        (t[] (t-> (:float) :float) (shp)))
       (float-relop-type
        (t[] (t-> (:float :float) :bool) (shp)))
       (float-to-int-type
        (t[] (t-> (:float) :int) (shp)))
       (bool-unop-type
        (t[] (t-> (:bool) :bool) (shp)))
       (bool-binop-type
        (t[] (t-> (:bool :bool) :bool) (shp)))
       (bool-to-int-type
        (t[] (t-> (:bool) :int) (shp)))
       (bool-to-float-type
        (t[] (t-> (:bool) :float) (shp)))
       (head-type
        (t[] (tforall ("&t")
                      (tpi ("$d" "@s")
                           (t-> ((t[] "&t" (shape++ (dim+ 1 "$d") "@s")))
                                (t[] "&t" "@s"))))
             (shp)))
       (tail-type
        (t[] (tforall ("&t")
                      (tpi ("$d" "@s")
                           (t-> ((t[] "&t" (shape++ (dim+ 1 "$d") "@s")))
                                (t[] "&t" (shape++ "$d" "@s")))))
             (shp)))
       (length-type
        (t[] (tforall ("&t")
                      (tpi ("$d" "@s")
                           (t-> ((t[] "&t" (shape++ "$d" "@s")))
                                :int)))
             (shp)))
       (append-type
        (t[] (tforall ("&t")
                      (tpi ("$m" "$n" "@s")
                           (t-> ((t[] "&t" (shape++ "$m" "@s"))
                                 (t[] "&t" (shape++ "$n" "@s")))
                                (t[] "&t" (shape++ (dim+ "$m" "$n") "@s")))))
             (shp)))
       (reverse-type
        (t[] (tforall ("&t")
                      (tpi ("$d" "@s")
                           (t-> ((t[] "&t" (shape++ "$d" "@s")))
                                (t[] "&t" (shape++ "$d" "@s")))))
             (shp))))
    (omap::from-alist
     (list (cons "+" int-binop-type)
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
           (cons "reverse" reverse-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-senv ()
  :short "Initial static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, static environment.
     It only contains the primitive operations in scope."))
  (make-senv :ispace-vars nil
             :type-vars nil
             :expr-vars (primop-types)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-ispace-var ((var ispace-varp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add an ispace variable to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with an absent associated ispace,
     because it does not stand for any specific ispace;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-senv senv
               :ispace-vars (omap::update (ispace-var-fix var)
                                          nil
                                          (senv->ispace-vars senv))))

;;;;;;;;;;;;;;;;;;;;

(define senv-add-ispace-vars ((vars ispace-var-listp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add zero or more ispace variables to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee senv-add-ispace-var),
     which this function repeats for each variable."))
  (b* (((when (endp vars)) (senv-fix senv))
       (senv (senv-add-ispace-var (car vars) senv)))
    (senv-add-ispace-vars (cdr vars) senv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-type-var ((var type-varp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add a type variable to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with an absent associated type,
     because it does not stand for any specific type;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (change-senv senv
               :type-vars (omap::update (type-var-fix var)
                                        nil
                                        (senv->type-vars senv))))

;;;;;;;;;;;;;;;;;;;;

(define senv-add-type-vars ((vars type-var-listp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add zero or more type variables to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee senv-add-type-var),
     which this function repeats for each variable."))
  (b* (((when (endp vars)) (senv-fix senv))
       (senv (senv-add-type-var (car vars) senv)))
    (senv-add-type-vars (cdr vars) senv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-ispace-def ((var ispace-varp) (ispace ispacep) (senv senvp))
  :returns (new-senv senvp)
  :short "Add an ispace variable with its ispace definition
          to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with a present associated ispace,
     namely its definition;
     this is the case for variables bound by @('let')s.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (b* ((new-ispace-vars (omap::update (ispace-var-fix var)
                                      (ispace-fix ispace)
                                      (senv->ispace-vars senv))))
    (change-senv senv :ispace-vars new-ispace-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-type-def ((var type-varp) (type typep) (senv senvp))
  :returns (new-senv senvp)
  :short "Add a type variable with its type definition
          to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable is added with a present associated type,
     namely its definition;
     this is the case for variables bound by @('let')s.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (b* ((new-type-vars (omap::update (type-var-fix var)
                                    (type-fix type)
                                    (senv->type-vars senv))))
    (change-senv senv :type-vars new-type-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-var+type ((var stringp) (type typep) (senv senvp))
  :returns (new-senv senvp)
  :short "Add a variable with a type to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since variables are expressions, the type must be an array type.
     So we auto-lift atom types to scalar array types if needed.")
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (b* ((expr-vars (senv->expr-vars senv))
       (new-expr-vars (omap::update (str::str-fix var)
                                    (type-ensure-array type)
                                    expr-vars)))
    (change-senv senv :expr-vars new-expr-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-vars+types ((vars+types var+type?-listp) (senv senvp))
  :guard (no-duplicatesp-equal (var+type?-list->var vars+types))
  :returns (new-senv senv-resultp)
  :short "Add zero or more variables with types to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function actually takes a list of variables with optional types,
     but it fails if some type is missing.")
   (xdoc::p
    "This repeatedly calls @(tsee senv-add-var+type).
     The guard ensures that the order of the list does not matter.")
   (xdoc::p
    "Since we do not perform type inference yet,
     this fails if any of the variables has no type."))
  (b* (((when (endp vars+types)) (senv-fix senv))
       (vt (car vars+types))
       ((ok type) (var+type?->type-or-err vt))
       (senv (senv-add-var+type (var+type?->var vt) type senv)))
    (senv-add-vars+types (cdr vars+types) senv)))
