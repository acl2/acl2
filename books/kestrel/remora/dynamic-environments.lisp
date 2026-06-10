; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "dynamic-values")

(local (include-book "std/lists/len" :dir :system))

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

(fty::defomap string-value-map
  :short "Fixtype of maps from strings to values."
  :key-type string
  :val-type value
  :pred string-value-mapp)

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
      with the associated values.")
    (xdoc::li
     "A map from type variables to type values.
      This consists of the type variables in scope,
      with the associated values.")
    (xdoc::li
     "A map from (expression) variables to (array) values.
      This consists of the variables in scope,
      with the associated values."))
   (xdoc::p
    "As noted in "
    (xdoc::seetopic "static-environments" "static environment")
    ", variables are in five separate name spaces:
     dimensions, shapes, atom types, array types, and expressions."))
  ((ispace-vars ispace-var-ispace-value-map)
   (type-vars type-var-type-value-map)
   (expr-vars string-value-map))
  :pred denvp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult denv-result
  :short "Fixtype of dynamic environments and errors."
  :ok denv
  :pred denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-value-map-wfp ((map string-value-mapp))
  :returns (yes/no booleanp)
  :short "Check that all the values in a string-to-value map are well-formed."
  (or (omap::emptyp (string-value-map-fix map))
      (and (value-wfp (omap::head-val map))
           (string-value-map-wfp (omap::tail map))))

  ///

  (defruled value-wfp-of-cdr-of-assoc-when-string-value-map-wfp
    (implies (and (string-value-mapp map)
                  (string-value-map-wfp map)
                  (omap::assoc key map))
             (value-wfp (cdr (omap::assoc key map))))
    :induct t
    :enable omap::assoc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define denv-wfp ((denv denvp))
  :returns (yes/no booleanp)
  :short "Check that the (expression) values in a dynamic environment
          are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an initial notion of well-formedness,
     concerning just the values bound to expression variables.
     We may extend it, or fold it into a broader notion,
     when we introduce well-formedness conditions
     on the ispace and type variables as well."))
  (string-value-map-wfp (denv->expr-vars denv))

  ///

  (defruled value-wfp-of-cdr-of-assoc-when-denv-wfp
    (implies (and (denv-wfp denv)
                  (omap::assoc key (denv->expr-vars denv)))
             (value-wfp (cdr (omap::assoc key (denv->expr-vars denv)))))
    :enable (denv-wfp
             value-wfp-of-cdr-of-assoc-when-string-value-map-wfp)))

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
    "This may override an existing variable,
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
