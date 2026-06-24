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
    (xdoc::seetopic "dynamic-environments" "dynamic environment")
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
      by ispace and type equivalence.
      (Currently the optional ispace is always absent,
      because @('let') bindings of ispace variables
      are not yet type-checked.)")
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
     more will be added as the formalization grows."))
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
        (t[] (t-> (:bool) :float) (shp))))
    (omap::from-alist
     (list (cons "+" int-binop-type)
           (cons "-" int-binop-type)
           (cons "*" int-binop-type)
           (cons "div" int-binop-type)
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
           (cons "bool->f" bool-to-float-type)))))

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

(define senv-add-ispace-vars ((vars ispace-var-listp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add zero or more ispace variables to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are added with an absent associated ispace,
     because they do not stand for any specific ispace;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (b* (((when (endp vars)) (senv-fix senv))
       (new-ispace-vars (omap::update (ispace-var-fix (car vars))
                                      nil
                                      (senv->ispace-vars senv)))
       (senv (change-senv senv :ispace-vars new-ispace-vars)))
    (senv-add-ispace-vars (cdr vars) senv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-type-vars ((vars type-var-listp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add zero or more type variables to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variables are added with an absent associated type,
     because they do not stand for any specific type;
     this is the case for variables bound by abstractions.
     A variable already present is overwritten,
     which realizes the intended shadowing."))
  (b* (((when (endp vars)) (senv-fix senv))
       (new-type-vars (omap::update (type-var-fix (car vars))
                                    nil
                                    (senv->type-vars senv)))
       (senv (change-senv senv :type-vars new-type-vars)))
    (senv-add-type-vars (cdr vars) senv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-var+type ((var stringp) (type typep) (senv senvp))
  :returns (new-senv senvp)
  :short "Add a variable with a type to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (b* ((expr-vars (senv->expr-vars senv))
       (new-expr-vars (omap::update (str::str-fix var)
                                    (type-fix type)
                                    expr-vars)))
    (change-senv senv :expr-vars new-expr-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-vars+types ((vars+types var+type-listp) (senv senvp))
  :guard (no-duplicatesp-equal (var+type-list->var vars+types))
  :returns (new-senv senvp)
  :short "Add zero or more variables with types to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This repeatedly calls @(tsee senv-add-var+type).
     The guard ensures that the order of the list does not matter."))
  (b* (((when (endp vars+types)) (senv-fix senv))
       ((var+type var+type) (car vars+types))
       (senv (senv-add-var+type var+type.var var+type.type senv)))
    (senv-add-vars+types (cdr vars+types) senv)))
