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
     and thus part of the initial static environment."))
  (b* ((add/sub/mul/div-type
        (t[] (t-> (:int :int) :int) (shp)))
       (append-type
        (t[] (tforall ("&t")
                      (tpi ("$n" "$m" "@s")
                           (t-> ((t[] "&t" (shape++ (shp "$m")
                                                    "@s"))
                                 (t[] "&t" (shape++ (shp "$n")
                                                    "@s")))
                                (t[] "&t" (shape++ (shp (dim+ "$m"
                                                                "$n"))
                                                   "@s")))))
             (shp)))
       (reduce-type
        (t[] (tforall ("&t")
                      (tpi ("@s" "$d")
                           (t-> ((t[] (t-> ((t[] "&t" "@s")
                                            (t[] "&t" "@s"))
                                           (t[] "&t" "@s"))
                                      (shp))
                                 (t[] "&t" (shape++ (shp (dim+ 1
                                                                 "$d"))
                                                    "@s")))
                                (t[] "&t" "@s"))))
             (shp)))
       (iota-type
        (t[] (tpi ("$d")
                  (t-> ((t[] :int (shp "$d")))
                       (tsigma ("@s") (t[] :int "@s"))))
             (shp))))
    (omap::from-alist
     (list (cons "add" add/sub/mul/div-type)
           (cons "sub" add/sub/mul/div-type)
           (cons "mul" add/sub/mul/div-type)
           (cons "div" add/sub/mul/div-type)
           (cons "append" append-type)
           (cons "reduce" reduce-type)
           (cons "iota" iota-type)))))

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
