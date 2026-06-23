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
     "The set of ispace variables in scope.
      This corresponds to @($\\Theta$),
      but since our ispace variables include their own sort,
      a set suffices, as opposed to a map from variables to sorts.")
    (xdoc::li
     "The set of type variables in scope.
      This corresponds to @($\\Delta$),
      but since our type variables include their own kind,
      a set suffices, as opposed to a map from variables to kinds.")
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
  ((ispace-vars ispace-var-set)
   (type-vars type-var-set)
   (expr-vars string-type-map))
  :pred senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-types ()
  :returns (term-vars string-type-mapp)
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
    "Variables already present have no effect."))
  (b* ((ispace-vars (senv->ispace-vars senv))
       (new-ispace-vars (set::union (set::mergesort (ispace-var-list-fix vars))
                                    ispace-vars)))
    (change-senv senv :ispace-vars new-ispace-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define senv-add-type-vars ((vars type-var-listp) (senv senvp))
  :returns (new-senv senvp)
  :short "Add zero or more type variables to the static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Variables already present have no effect."))
  (b* ((type-vars (senv->type-vars senv))
       (new-type-vars (set::union (set::mergesort (type-var-list-fix vars))
                                  type-vars)))
    (change-senv senv :type-vars new-type-vars)))

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
