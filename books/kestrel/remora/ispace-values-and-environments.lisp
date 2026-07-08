; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/nat-list-list" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-values-and-environments
  :parents (dynamic-semantics)
  :short "Ispace values and ispace dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ispaces (ASTs) evaluate to ispace values.
     Ispace dynamic environments capture
     the ispace variables in scope and their associated ispace values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ispace-value
  :short "Fixtype of ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like a normalized ground form of ispace ASTs:
     if there are no free variables,
     a dimension can be reduced to a natural number,
     and a shape can be reduced to a list of natural numbers."))
  (:dim ((val nat)))
  (:shape ((val nat-list)))
  :pred ispace-valuep)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption ispace-value-option
  ispace-value
  :short "Fixtype of optional ispace values."
  :pred ispace-value-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-value-result
  :short "Fixtype of ispace values and errors."
  :ok ispace-value
  :pred ispace-value-resultp
  :prepwork ((local (in-theory (enable ispace-value-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ispace-value-list
  :short "Fixtype of lists of ispace values."
  :elt-type ispace-value
  :true-listp t
  :elementp-of-nil nil
  :pred ispace-value-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-value-list-result
  :short "Fixtype of (i) lists of ispace values and (ii) errors."
  :ok ispace-value-list
  :pred ispace-value-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-value-to-dims ((ival ispace-valuep))
  :returns (dims nat-listp)
  :short "Turn an ispace value into a list of dimensions."
  (ispace-value-case
   ival
   :dim (list ival.val)
   :shape ival.val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-value-list-to-dims ((x ispace-value-listp))
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee ispace-value-to-dims) to lists."
  (ispace-value-to-dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-values-match-ispace-vars-p ((ivals ispace-value-listp)
                                           (vars ispace-var-listp))
  :returns (yes/no booleanp)
  :short "Check that ispace values match ispace variables
          in number and sort."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists must have the same length,
     and, element-wise, each ispace value must match
     the sort of the corresponding ispace variable:
     a @(':dim') ispace variable must be matched by a @(':dim') ispace value,
     and a @(':shape') ispace variable by a @(':shape') ispace value.")
   (xdoc::p
    "This is used to evaluate ispace applications,
     where the ispace values that an ispace lambda is applied to
     must match the ispace parameters of the ispace lambda."))
  (b* (((when (endp ivals)) (endp vars))
       ((when (endp vars)) nil)
       (ival (car ivals))
       (var (car vars)))
    (and (ispace-var-case var
                          :dim (ispace-value-case ival :dim)
                          :shape (ispace-value-case ival :shape))
         (ispace-values-match-ispace-vars-p (cdr ivals) (cdr vars))))

  ///

  (defrule len-equal-when-ispace-values-match-ispace-vars-p
    (implies (ispace-values-match-ispace-vars-p ivals vars)
             (equal (len ivals) (len vars)))
    :rule-classes :forward-chaining
    :induct t))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
