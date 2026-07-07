; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values")

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-environments
  :parents (dynamic-semantics)
  :short "Dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A dynamic environment consists of
     the contextual information needed to execute ASTs.
     It is the dynamic counterpart of a "
    (xdoc::seetopic "static-environments" "static environment")
    ".")
   (xdoc::p
    "Our dynamic environments have no direct counterpart
     in [thesis], [arxiv], and [esop],
     which use beta reduction rules to substitute variables
     (for expressions, types, and ispaces).
     Our dynamic environment is needed
     to express conveniently an interpretive dynamic semantics;
     they may be also needed or convenient
     for a rule-based small-step operational semantics,
     which we plan to do at some point.
     It may also facilitate expressing and proving type soundness.
     If Remora is extended with top-level definitions
     (now there are only @('let') expressions),
     a dynamic environment would keep track of those definitions;
     we already have implicit definitions of the primitive operations in fact.
     But we will investigate all of this as we progress in our work."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap ispace-var-ispace-value-map
  :short "Fixtype of maps from ispace variables to ispace values."
  :key-type ispace-var
  :val-type ispace-value
  :pred ispace-var-ispace-value-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ispace-denv
  :short "Fixtype of ispace dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a map from ispace variables to ispace values.
     They are the ispace variables in scope, with the associated values.")
   (xdoc::p
    "We wrap the map into a fixtype for abstraction.
     We may want to replace this with two maps,
     one for dimensions and one for shapes."))
  ((ispaces ispace-var-ispace-value-map))
  :pred ispace-denvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-denv-result
  :short "Fixtype of ispace dynamic environments and errors."
  :ok ispace-denv
  :pred ispace-denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap type-var-type-value-map
  :short "Fixtype of maps from type variables to type values."
  :key-type type-var
  :val-type type-value
  :pred type-var-type-value-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type-denv
  :short "Fixtype of type dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This includes an ispace environment,
     because types contain ispaces.
     And it has a map from type variables to type values,
     which are the type variables in scope with the associated values.")
   (xdoc::p
    "We wrap the type map into a fixtype for abstraction.
     We may want to replace this with two maps,
     one for atom types and one for array types."))
  ((ienv ispace-denv)
   (types type-var-type-value-map))
  :pred type-denvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-denv-result
  :short "Fixtype of type dynamic environments and errors."
  :ok type-denv
  :pred type-denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-expr-value-map
  :short "Fixtype of maps from strings to expression values."
  :key-type string
  :val-type expr-value
  :pred string-expr-value-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-denv
  :short "Fixtype of expression dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "This includes a type dynamic environment,
     because expressions contain types;
     and the type dynamic environment includes an ispace dynamic environment.
     Additionally, we have a map from expression variables to expression values,
     which are the expression variables in scope with the associated values."))
  ((tenv type-denv)
   (exprs string-expr-value-map))
  :pred expr-denvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-denv-result
  :short "Fixtype of expression dynamic environments and errors."
  :ok expr-denv
  :pred expr-denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-expr-value-map-wfp ((map string-expr-value-mapp))
  :returns (yes/no booleanp)
  :short "Check that all the expression values
          in a string-to-expression-value map
          are well-formed."
  (or (omap::emptyp (string-expr-value-map-fix map))
      (and (expr-value-wfp (omap::head-val map))
           (string-expr-value-map-wfp (omap::tail map))))

  ///

  (defruled expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp
    (implies (and (string-expr-value-mapp map)
                  (string-expr-value-map-wfp map)
                  (omap::assoc key map))
             (expr-value-wfp (cdr (omap::assoc key map))))
    :induct t
    :enable omap::assoc)

  (defruled string-expr-value-map-wfp-of-update
    (implies (and (string-expr-value-mapp map)
                  (string-expr-value-map-wfp map)
                  (expr-value-wfp val))
             (string-expr-value-map-wfp (omap::update key val map)))
    :induct (string-expr-value-map-wfp map)
    :expand ((string-expr-value-map-wfp (omap::update key val map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-wfp ((denv expr-denvp))
  :returns (yes/no booleanp)
  :short "Check that the expression values in an expression dynamic environment
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an initial notion of well-formedness,
     concerning just the expression values bound to expression variables.
     We may extend it, or fold it into a broader notion,
     when we introduce well-formedness conditions
     on the ispace and type variables as well."))
  (string-expr-value-map-wfp (expr-denv->exprs denv))

  ///

  (defruled expr-value-wfp-of-cdr-of-assoc-when-expr-denv-wfp
    (implies (and (expr-denv-wfp denv)
                  (omap::assoc key (expr-denv->exprs denv)))
             (expr-value-wfp (cdr (omap::assoc key (expr-denv->exprs denv)))))
    :enable (expr-denv-wfp
             expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-denv-add-ispace ((var ispace-varp)
                                (ival ispace-valuep)
                                (denv ispace-denvp))
  :returns (new-denv ispace-denvp)
  :short "Add an ispace variable, with an associated ispace value,
          to an ispace dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-ispace-denv denv
                      :ispaces (omap::update (ispace-var-fix var)
                                             (ispace-value-fix ival)
                                             (ispace-denv->ispaces denv))))

;;;;;;;;;;;;;;;;;;;;

(define ispace-denv-add-ispaces ((vars ispace-var-listp)
                                 (ivals ispace-value-listp)
                                 (denv ispace-denvp))
  :guard (equal (len vars) (len ivals))
  :returns (new-denv ispace-denvp)
  :short "Add zero or more ispace variables, with associated ispace values,
          to an ispace dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (ispace-denv-fix denv))
       ((unless (mbt (consp ivals))) (ispace-denv-fix denv))
       (denv (ispace-denv-add-ispace (car vars) (car ivals) denv)))
    (ispace-denv-add-ispaces (cdr vars) (cdr ivals) denv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-denv-add-ispace ((var ispace-varp)
                              (ival ispace-valuep)
                              (denv type-denvp))
  :returns (new-denv type-denvp)
  :short "Add an ispace variable, with an associated ispace value,
          to a type dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-type-denv denv
                    :ienv (ispace-denv-add-ispace var
                                                  ival
                                                  (type-denv->ienv denv))))

;;;;;;;;;;;;;;;;;;;;

(define type-denv-add-ispaces ((vars ispace-var-listp)
                               (ivals ispace-value-listp)
                               (denv type-denvp))
  :guard (equal (len vars) (len ivals))
  :returns (new-denv type-denvp)
  :short "Add zero or more ispace variables, with associated ispace values,
          to a type dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (change-type-denv denv
                    :ienv (ispace-denv-add-ispaces vars
                                                   ivals
                                                   (type-denv->ienv denv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-denv-add-type ((var type-varp)
                            (tval type-valuep)
                            (denv type-denvp))
  :returns (new-denv type-denvp)
  :short "Add a type variable, with an associated type value,
          to a type dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-type-denv denv
                    :types (omap::update (type-var-fix var)
                                         (type-value-fix tval)
                                         (type-denv->types denv))))

;;;;;;;;;;;;;;;;;;;;

(define type-denv-add-types ((vars type-var-listp)
                             (tvals type-value-listp)
                             (denv type-denvp))
  :guard (equal (len vars) (len tvals))
  :returns (new-denv type-denvp)
  :short "Add zero or more type variables, with associated type values,
          to a type dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (type-denv-fix denv))
       ((unless (mbt (consp tvals))) (type-denv-fix denv))
       (denv (type-denv-add-type (car vars) (car tvals) denv)))
    (type-denv-add-types (cdr vars) (cdr tvals) denv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-ispace ((var ispace-varp)
                              (ival ispace-valuep)
                              (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Add an ispace variable, with an associated ispace value,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-ispace var
                                                ival
                                                (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-ispace
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-ispaces ((vars ispace-var-listp)
                               (ivals ispace-value-listp)
                               (denv expr-denvp))
  :guard (equal (len vars) (len ivals))
  :returns (new-denv expr-denvp)
  :short "Add zero or more ispace variables, with associated ispace values,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-ispaces vars
                                                 ivals
                                                 (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-ispaces
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-type ((var type-varp)
                            (tval type-valuep)
                            (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Add a type variable, with an associated type value,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-type var
                                              tval
                                              (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-type
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-types ((vars type-var-listp)
                             (tvals type-value-listp)
                             (denv expr-denvp))
  :guard (equal (len vars) (len tvals))
  :returns (new-denv expr-denvp)
  :short "Add zero or more type variables, with associated type values,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :tenv (type-denv-add-types vars
                                               tvals
                                               (expr-denv->tenv denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-types
    (implies (expr-denv-wfp denv)
             (expr-denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-expr ((var stringp) (val expr-valuep) (denv expr-denvp))
  :returns (new-denv expr-denvp)
  :short "Add an expression variable,
          with an associated expression value,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-expr-denv denv
                    :exprs (omap::update (str-fix var)
                                         (expr-value-fix val)
                                         (expr-denv->exprs denv)))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-expr
    (implies (and (expr-denv-wfp denv)
                  (expr-value-wfp val))
             (expr-denv-wfp new-denv))
    :hints (("Goal"
             :in-theory (enable expr-denv-wfp
                                string-expr-value-map-wfp-of-update)))))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-add-exprs ((vars string-listp)
                             (vals expr-value-listp)
                             (denv expr-denvp))
  :guard (equal (len vars) (len vals))
  :returns (new-denv expr-denvp)
  :short "Add zero or more expression variables,
          with associated expression values,
          to an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (expr-denv-fix denv))
       ((unless (mbt (consp vals))) (expr-denv-fix denv))
       (denv (expr-denv-add-expr (car vars) (car vals) denv)))
    (expr-denv-add-exprs (cdr vars) (cdr vals) denv))

  ///

  (defret expr-denv-wfp-of-expr-denv-add-exprs
    (implies (and (expr-denv-wfp denv)
                  (expr-value-list-wfp vals))
             (expr-denv-wfp new-denv))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-denv-lookup-ispace ((var ispace-varp) (denv ispace-denvp))
  :returns (ispace-val ispace-value-resultp)
  :short "Lookup an ispace variable in an ispace dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (b* ((var+val (omap::assoc (ispace-var-fix var)
                             (ispace-denv->ispaces denv))))
    (if var+val
        (cdr var+val)
      (reserr nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-denv-lookup-ispace ((var ispace-varp) (denv type-denvp))
  :returns (ispace-val ispace-value-resultp)
  :short "Lookup an ispace variable in a type dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (ispace-denv-lookup-ispace var (type-denv->ienv denv)))

;;;;;;;;;;;;;;;;;;;;

(define type-denv-lookup-type ((var type-varp) (denv type-denvp))
  :returns (type-val type-value-resultp)
  :short "Lookup a type variable in a type dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (b* ((var+val (omap::assoc (type-var-fix var) (type-denv->types denv))))
    (if var+val
        (cdr var+val)
      (reserr nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-denv-lookup-ispace ((var ispace-varp) (denv expr-denvp))
  :returns (ispace-val ispace-value-resultp)
  :short "Lookup an ispace variable in an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (type-denv-lookup-ispace var (expr-denv->tenv denv)))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-lookup-type ((var type-varp) (denv expr-denvp))
  :returns (type-val type-value-resultp)
  :short "Lookup a type variable in an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (type-denv-lookup-type var (expr-denv->tenv denv)))

;;;;;;;;;;;;;;;;;;;;

(define expr-denv-lookup-expr ((var stringp) (denv expr-denvp))
  :returns (expr-val expr-value-resultp)
  :short "Lookup an expression variable in an expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if the variable is not in the environment."))
  (b* ((var+val (omap::assoc (str-fix var) (expr-denv->exprs denv))))
    (if var+val
        (cdr var+val)
      (reserr nil)))

  ///

  (defret expr-value-wfp-of-expr-denv-lookup-expr
    (implies (not (reserrp expr-val))
             (expr-value-wfp expr-val))
    :hyp (expr-denv-wfp denv)
    :hints
    (("Goal"
      :in-theory
      (enable expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp
              expr-denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-values ()
  :returns (expr-var-val-map string-expr-value-mapp)
  :short "Association of primitive operations to their values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee primop-types):
     it associates each variable that denotes a primitive operation
     to the value of that variable,
     which is a scalar @(':primop') expression value
     (see @(tsee primop-value)).
     These variables are implicitly in scope,
     and thus part of the initial dynamic environment
     (see @(tsee init-expr-denv)).")
   (xdoc::p
    "The names (the map keys) are the surface names [impl],
     exactly as in @(tsee primop-types).
     A polymorphic operation like @('length')
     is associated to its uninstantiated stage."))
  (omap::from-alist
   (list (cons "+" (expr-value-primop (primop-value-int-add)))
         (cons "-" (expr-value-primop (primop-value-int-sub)))
         (cons "*" (expr-value-primop (primop-value-int-mul)))
         (cons "div" (expr-value-primop (primop-value-int-div)))
         (cons "mod" (expr-value-primop (primop-value-int-mod)))
         (cons "max" (expr-value-primop (primop-value-int-max)))
         (cons "min" (expr-value-primop (primop-value-int-min)))
         (cons "bit-and" (expr-value-primop (primop-value-int-bit-and)))
         (cons "bit-or" (expr-value-primop (primop-value-int-bit-or)))
         (cons "bit-xor" (expr-value-primop (primop-value-int-bit-xor)))
         (cons "shl" (expr-value-primop (primop-value-int-shl)))
         (cons "shr" (expr-value-primop (primop-value-int-shr)))
         (cons "bit-not" (expr-value-primop (primop-value-int-bit-not)))
         (cons "popc" (expr-value-primop (primop-value-int-popc)))
         (cons "==" (expr-value-primop (primop-value-int-eq)))
         (cons "!=" (expr-value-primop (primop-value-int-neq)))
         (cons "<" (expr-value-primop (primop-value-int-lt)))
         (cons ">" (expr-value-primop (primop-value-int-gt)))
         (cons "<=" (expr-value-primop (primop-value-int-leq)))
         (cons ">=" (expr-value-primop (primop-value-int-geq)))
         (cons "i->f" (expr-value-primop (primop-value-int-to-float)))
         (cons "i->bool" (expr-value-primop (primop-value-int-to-bool)))
         (cons "f.+" (expr-value-primop (primop-value-float-add)))
         (cons "f.-" (expr-value-primop (primop-value-float-sub)))
         (cons "f.*" (expr-value-primop (primop-value-float-mul)))
         (cons "f./" (expr-value-primop (primop-value-float-div)))
         (cons "f.^" (expr-value-primop (primop-value-float-expt)))
         (cons "f.max" (expr-value-primop (primop-value-float-max)))
         (cons "f.min" (expr-value-primop (primop-value-float-min)))
         (cons "sqrt" (expr-value-primop (primop-value-float-sqrt)))
         (cons "f.==" (expr-value-primop (primop-value-float-eq)))
         (cons "f.!=" (expr-value-primop (primop-value-float-neq)))
         (cons "f.<" (expr-value-primop (primop-value-float-lt)))
         (cons "f.>" (expr-value-primop (primop-value-float-gt)))
         (cons "f.<=" (expr-value-primop (primop-value-float-leq)))
         (cons "f.>=" (expr-value-primop (primop-value-float-geq)))
         (cons "truncate" (expr-value-primop (primop-value-float-truncate)))
         (cons "round" (expr-value-primop (primop-value-float-round)))
         (cons "ceiling" (expr-value-primop (primop-value-float-ceiling)))
         (cons "floor" (expr-value-primop (primop-value-float-floor)))
         (cons "not" (expr-value-primop (primop-value-bool-not)))
         (cons "and" (expr-value-primop (primop-value-bool-and)))
         (cons "or" (expr-value-primop (primop-value-bool-or)))
         (cons "bool.==" (expr-value-primop (primop-value-bool-eq)))
         (cons "bool.!=" (expr-value-primop (primop-value-bool-neq)))
         (cons "bool->i" (expr-value-primop (primop-value-bool-to-int)))
         (cons "bool->f" (expr-value-primop (primop-value-bool-to-float)))
         (cons "length" (expr-value-primop (primop-value-length))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-expr-denv ()
  :returns (denv expr-denvp)
  :short "Initial expression dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, expression dynamic environment.
     It only contains the primitive operations in scope.
     It is the dynamic counterpart of @(tsee init-senv)."))
  (make-expr-denv :tenv (make-type-denv :ienv (make-ispace-denv :ispaces nil)
                                        :types nil)
                  :exprs (primop-values))

  ///

  (defret expr-denv-wfp-of-init-expr-denv
    (expr-denv-wfp denv)))
