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
     Our dynamic environment seems needed
     to express conveniently an interpretive dynamic semantics,
     which we plan to do first;
     they may be also needed or convenient
     for a rule-based small-step operational semantics,
     which we plan to do after that.
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

(fty::defomap type-var-type-value-map
  :short "Fixtype of maps from type variables to type values."
  :key-type type-var
  :val-type type-value
  :pred type-var-type-value-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-expr-value-map
  :short "Fixtype of maps from strings to expression values."
  :key-type string
  :val-type expr-value
  :pred string-expr-value-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod denv
  :short "Fixtype of dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A dynamic environment consists of:")
   (xdoc::ul
    (xdoc::li
     "A map from ispace variables to ispace values.
      This consists of the ispace variables in scope,
      with the associated ispace values.")
    (xdoc::li
     "A map from type variables to type values.
      This consists of the type variables in scope,
      with the associated type values.")
    (xdoc::li
     "A map from (expression) variables to (array) expression values.
      This consists of the variables in scope,
      with the associated expression values."))
   (xdoc::p
    "As noted in "
    (xdoc::seetopic "static-environments" "static environment")
    ", variables are in five separate name spaces:
     dimensions, shapes, atom types, array types, and expressions."))
  ((ispace-vars ispace-var-ispace-value-map)
   (type-vars type-var-type-value-map)
   (expr-vars string-expr-value-map))
  :pred denvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult denv-result
  :short "Fixtype of dynamic environments and errors."
  :ok denv
  :pred denv-resultp)

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

(define denv-wfp ((denv denvp))
  :returns (yes/no booleanp)
  :short "Check that the expression values in a dynamic environment
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an initial notion of well-formedness,
     concerning just the expression values bound to expression variables.
     We may extend it, or fold it into a broader notion,
     when we introduce well-formedness conditions
     on the ispace and type variables as well."))
  (string-expr-value-map-wfp (denv->expr-vars denv))

  ///

  (defruled expr-value-wfp-of-cdr-of-assoc-when-denv-wfp
    (implies (and (denv-wfp denv)
                  (omap::assoc key (denv->expr-vars denv)))
             (expr-value-wfp (cdr (omap::assoc key (denv->expr-vars denv)))))
    :enable (denv-wfp
             expr-value-wfp-of-cdr-of-assoc-when-string-expr-value-map-wfp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define denv-add-ispace-var ((var ispace-varp) (ival ispace-valuep) (denv denvp))
  :returns (new-denv denvp)
  :short "Add an ispace variable, with an associated ispace value,
          to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-denv denv
               :ispace-vars (omap::update (ispace-var-fix var)
                                          (ispace-value-fix ival)
                                          (denv->ispace-vars denv)))

  ///

  (defret denv->type-vars-of-denv-add-ispace-var
    (equal (denv->type-vars new-denv)
           (denv->type-vars denv)))

  (defret denv->expr-vars-of-denv-add-ispace-var
    (equal (denv->expr-vars new-denv)
           (denv->expr-vars denv)))

  (defret denv-wfp-of-denv-add-ispace-var
    (implies (denv-wfp denv)
             (denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define denv-add-ispace-vars ((vars ispace-var-listp)
                              (ivals ispace-value-listp)
                              (denv denvp))
  :guard (equal (len vars) (len ivals))
  :returns (new-denv denvp)
  :short "Add zero or more ispace variables, with associated ispace values,
          to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (denv-fix denv))
       ((unless (mbt (consp ivals))) (denv-fix denv))
       (denv (denv-add-ispace-var (car vars) (car ivals) denv)))
    (denv-add-ispace-vars (cdr vars) (cdr ivals) denv))

  ///

  (defret denv->type-vars-of-denv-add-ispace-vars
    (equal (denv->type-vars new-denv)
           (denv->type-vars denv))
    :hints (("Goal" :induct t)))

  (defret denv->expr-vars-of-denv-add-ispace-vars
    (equal (denv->expr-vars new-denv)
           (denv->expr-vars denv))
    :hints (("Goal" :induct t)))

  (defret denv-wfp-of-denv-add-ispace-vars
    (implies (denv-wfp denv)
             (denv-wfp new-denv))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define denv-add-type-vars ((vars type-var-listp)
                            (tvals type-value-listp)
                            (denv denvp))
  :guard (equal (len vars) (len tvals))
  :returns (new-denv denvp)
  :short "Add zero or more type variables, with associated type values,
          to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (denv-fix denv))
       ((unless (mbt (consp tvals))) (denv-fix denv))
       (denv (change-denv
              denv
              :type-vars (omap::update (type-var-fix (car vars))
                                       (type-value-fix (car tvals))
                                       (denv->type-vars denv)))))
    (denv-add-type-vars (cdr vars) (cdr tvals) denv))

  ///

  (defret denv->ispace-vars-of-denv-add-type-vars
    (equal (denv->ispace-vars new-denv)
           (denv->ispace-vars denv))
    :hints (("Goal" :induct t)))

  (defret denv->expr-vars-of-denv-add-type-vars
    (equal (denv->expr-vars new-denv)
           (denv->expr-vars denv))
    :hints (("Goal" :induct t)))

  (defret denv-wfp-of-denv-add-type-vars
    (implies (denv-wfp denv)
             (denv-wfp new-denv))
    :hints (("Goal" :in-theory (enable denv-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define denv-add-expr-var ((var stringp) (val expr-valuep) (denv denvp))
  :returns (new-denv denvp)
  :short "Add an expression variable,
          with an associated expression value,
          to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override an existing variable,
     which is intended hiding behavior."))
  (change-denv denv
               :expr-vars (omap::update (str::str-fix var)
                                        (expr-value-fix val)
                                        (denv->expr-vars denv)))

  ///

  (defret denv->ispace-vars-of-denv-add-expr-var
    (equal (denv->ispace-vars new-denv)
           (denv->ispace-vars denv)))

  (defret denv->type-vars-of-denv-add-expr-var
    (equal (denv->type-vars new-denv)
           (denv->type-vars denv)))

  (defret denv-wfp-of-denv-add-expr-var
    (implies (and (denv-wfp denv)
                  (expr-value-wfp val))
             (denv-wfp new-denv))
    :hints (("Goal"
             :in-theory (enable denv-wfp
                                string-expr-value-map-wfp-of-update)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define denv-add-expr-vars ((vars string-listp)
                            (vals expr-value-listp)
                            (denv denvp))
  :guard (equal (len vars) (len vals))
  :returns (new-denv denvp)
  :short "Add zero or more expression variables,
          with associated expression values,
          to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This may override existing variables,
     which is intended hiding behavior."))
  (b* (((when (endp vars)) (denv-fix denv))
       ((unless (mbt (consp vals))) (denv-fix denv))
       (denv (denv-add-expr-var (car vars) (car vals) denv)))
    (denv-add-expr-vars (cdr vars) (cdr vals) denv))

  ///

  (defret denv->ispace-vars-of-denv-add-expr-vars
    (equal (denv->ispace-vars new-denv)
           (denv->ispace-vars denv))
    :hints (("Goal" :induct t)))

  (defret denv->type-vars-of-denv-add-expr-vars
    (equal (denv->type-vars new-denv)
           (denv->type-vars denv))
    :hints (("Goal" :induct t)))

  (defret denv-wfp-of-denv-add-expr-vars
    (implies (and (denv-wfp denv)
                  (expr-value-list-wfp vals))
             (denv-wfp new-denv))
    :hints (("Goal" :induct t))))
