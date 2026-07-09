; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-values-and-environments")

(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-values-and-environments
  :parents (dynamic-semantics)
  :short "Type values and type dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Types (ASTs) evaluate to type values.
     Type dynamic environments capture
     the type variables in scope and their associated type values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes type-values/denv
  :short "Fixtypes of type values and type dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type values and type dynamic environments are mutually recursive
     because some type values are (type-level) closures
     that contain dynamic environments."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum type-value
    :parents (type-values-and-environments type-values/denv)
    :short "Fixtype of type values."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is like a normalized ground form of type ASTs:
       if there are no free variables,
       a type is a base type,
       or an array with a type value element with a list of dimensions,
       or a function type with input and output type values,
       or a universal, product, or sum type.
       The latter three categories of types do not use type values in bodies,
       but they have the full type ASTs,
       because they are like lambda abstractions,
       and their evaluation is deferred.")
     (xdoc::p
      "Critically, universal, product, and sum types
       contain environments for their free ispace and type variables.
       This fixtype currently does not enforce the constraint that
       the environments contain exactly those free variables."))
    (:base ((type base-type)))
    (:array ((elem type-value)
             (dims nat-list)))
    (:fun ((in type-value-list)
           (out type-value)))
    (:forall ((params type-var-list)
              (body type)
              (denv type-denv)))
    (:pi ((params ispace-var-list)
          (body type)
          (denv type-denv)))
    (:sigma ((params ispace-var-list)
             (body type)
             (denv type-denv)))
    :pred type-valuep
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist type-value-list
    :parents (type-values-and-environments type-values/denv)
    :short "Fixtype of lists of type values."
    :elt-type type-value
    :true-listp t
    :elementp-of-nil nil
    :pred type-value-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defomap type-var-type-value-map
    :parents (type-values-and-environments type-values/denv)
    :short "Fixtype of maps from type variables to type values."
    :key-type type-var
    :val-type type-value
    :pred type-var-type-value-mapp
    :measure (two-nats-measure (acl2-count x) 0)

    ///

    (defrule type-var-type-value-mapp-of-restrict
      (implies (type-var-type-value-mapp map)
               (type-var-type-value-mapp (omap::restrict keys map)))
      :induct t
      :enable omap::restrict))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::defprod type-denv
    :parents (type-values-and-environments type-values/denv)
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
    :pred type-denvp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist type-value-list-case-array (x)
  :short "Check if all the type values in a list
          are in the @(':array') summand."
  :guard (type-value-listp x)
  (type-value-case x :array))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-value-array-list->dims ((x type-value-listp))
  :guard (type-value-list-case-array x)
  :returns (shapes nat-list-listp)
  :short "Lift @(tsee type-value-array->dims) to lists."
  (type-value-array->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption type-value-option
  type-value
  :short "Fixtype of optional type values."
  :pred type-value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-value-result
  :short "Fixtype of type values and errors."
  :ok type-value
  :pred type-value-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-value-list-result
  :short "Fixtype of (i) lists of type values and (ii) errors."
  :ok type-value-list
  :pred type-value-list-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-denv-result
  :short "Fixtype of type dynamic environments and errors."
  :ok type-denv
  :pred type-denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dims-of-type-value ((tval type-valuep))
  :returns (dims nat-listp)
  :short "Dimensions of a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "Atom type values have the empty list of dimensions.
     Array type values have explicit dimensions.")
   (xdoc::p
    "Recall that scalar (i.e. 0-rank) array types are
     equivalent to their atom element types."))
  (type-value-case
   tval
   :base nil
   :array tval.dims
   :fun nil
   :forall nil
   :pi nil
   :sigma nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dims-of-type-value-list ((x type-value-listp))
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee dims-of-type-value) to lists."
  (dims-of-type-value x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-values-match-type-vars-p ((tvals type-value-listp)
                                       (vars type-var-listp))
  :returns (yes/no booleanp)
  :short "Check that type values match type variables
          in number and kind."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and, element-wise, each type value must match
     the kind of the corresponding type variable:
     an @(':atom') type variable must be matched by an atom type value,
     and an @(':array') type variable by an array type value.
     A type value has the array kind when it is an @(':array');
     every other type value has the atom kind.")
   (xdoc::p
    "This is used to evaluate type applications,
     where the type values that a type lambda is applied to
     must match the type parameters of the type lambda."))
  (b* (((when (endp tvals)) (endp vars))
       ((when (endp vars)) nil)
       (tval (car tvals))
       (var (car vars)))
    (and (type-var-case var
                        :atom (not (type-value-case tval :array))
                        :array (type-value-case tval :array))
         (type-values-match-type-vars-p (cdr tvals) (cdr vars))))

  ///

  (defrule len-equal-when-type-values-match-type-vars-p
    (implies (type-values-match-type-vars-p tvals vars)
             (equal (len tvals) (len vars)))
    :rule-classes :forward-chaining
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var+typevalue
  :short "Fixtype of variables with type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee var+type?),
     but with the type being present:
     a pair consisting of a variable name and an associated type value.
     In the name of this fixtype,
     we join `type' and `value' into `typevalue',
     so that the name reads better in terms of visual grouping.
     The field for the type value is named just @('type'),
     which is clear in the context of this fixtype."))
  ((var string)
   (type type-value))
  :pred var+typevalue-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var+typevalue-list
  :short "Fixtype of lists of variables with type values."
  :elt-type var+typevalue
  :true-listp t
  :elementp-of-nil nil
  :pred var+typevalue-listp)

;;;;;;;;;;

(std::defprojection var+typevalue-list->var ((x var+typevalue-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee var+typevalue->var) to lists."
  (var+typevalue->var x))

;;;;;;;;;;

(std::defprojection var+typevalue-list->type ((x var+typevalue-listp))
  :returns (tvals type-value-listp)
  :short "Lift @(tsee var+typevalue->type) to lists."
  (var+typevalue->type x))

;;;;;;;;;;;;;;;;;;;;

(fty::defresult var+typevalue-result
  :short "Fixtype of (i) variables with type values and (ii) errors."
  :ok var+typevalue
  :pred var+typevalue-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult var+typevalue-list-result
  :short "Fixtype of (i) lists of variables with type values and (ii) errors."
  :ok var+typevalue-list
  :pred var+typevalue-list-resultp)

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

;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;

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

(define type-denv-restrict ((ivars ispace-var-setp)
                            (tvars type-var-setp)
                            (denv type-denvp))
  :returns (new-denv type-denvp)
  :short "Restrict a type dynamic environment
          to a set of ispace variables and a set of type variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We restrict the underlying ispace dynamic environment
     to the first given set,
     and we remove from the environment
     the type variables not in the second given set."))
  (change-type-denv denv
                    :ienv (ispace-denv-restrict ivars (type-denv->ienv denv))
                    :types (omap::restrict (type-var-set-fix tvars)
                                           (type-denv->types denv))))
