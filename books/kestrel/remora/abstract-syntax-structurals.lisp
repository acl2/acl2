; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-core")
(include-book "abstract-syntax-derived-fixtypes")
(include-book "lists")

(include-book "defsort/duplicated-members" :dir :system)
(include-book "kestrel/fty/string-set" :dir :system)
(include-book "kestrel/typed-lists-light/nat-list-listp" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable* ast-corep-rules)))

(local (in-theory (enable typep-when-result-not-error
                          type-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-structurals
  :parents (abstract-syntax)
  :short "Structural operations and theorems on ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are purely structural operations and theorems,
     e.g. lifting from elements to lists.
     At least some of these could be generated from the fixtype definitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist dim-list-case-const (x)
  :short "Check if all the dimensions in a list
          are in the @(':const') summand."
  :guard (dim-listp x)
  (dim-case x :const))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist shape-list-case-append (x)
  :short "Check if all the shapes in a list
          are in the @(':append') summand."
  :guard (shape-listp x)
  (shape-case x :append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist ispace-list-case-shape (x)
  :short "Check if all the ispaces in a list
          are in the @(':shape') summand."
  :guard (ispace-listp x)
  (ispace-case x :shape))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-list-case-array (x)
  :short "Check if all the expressions in a list
          are in the @(':array') summand."
  :guard (expr-listp x)
  (expr-case x :array))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-list-case-frame (x)
  :short "Check if all the expressions in a list
          are in the @(':frame') summand."
  :guard (expr-listp x)
  (expr-case x :frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dim-const-list ((x nat-listp))
  :returns (dims dim-listp)
  :short "Lift @(tsee dim-const) to lists."
  (dim-const x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection shape-dims-list ((x dim-list-listp))
  :returns (shapes shape-listp)
  :short "Lift @(tsee shape-dims) to lists."
  (shape-dims x)

  ///

  (defruled shape-list-corep-of-shape-dims-list-of-list-to-singletons
    (shape-list-corep (shape-dims-list (list-to-singletons dims)))
    :induct t
    :enable (list-to-singletons
             shape-corep-when-dims-and-singleton)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-shape-list ((x shape-listp))
  :returns (ispaces ispace-listp)
  :short "Lift @(tsee ispace-shape) to lists."
  (ispace-shape x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection base-lit-int-list ((x int-lit-listp))
  :returns (lits base-lit-listp)
  :short "Lift @(tsee base-lit-int) to lists."
  (base-lit-int x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection atom-base-list ((x base-lit-listp))
  :returns (atoms atom-listp)
  :short "Lift @(tsee atom-base) to lists."
  (atom-base x)

  ///

  (defrule atom-list-corep-of-atom-base-list
    (atom-list-corep (atom-base-list lits))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection dim-const-list->val ((x dim-listp))
  :guard (dim-list-case-const x)
  :returns (vals nat-listp)
  :short "Lift @(tsee dim-const->val) to lists."
  (dim-const->val x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-array-list->dims ((x expr-listp))
  :guard (expr-list-case-array x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee expr-array->dims) to lists."
  (expr-array->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-array-list->atoms ((x expr-listp))
  :guard (expr-list-case-array x)
  :returns (atomss atom-list-listp)
  :short "Lift @(tsee expr-array->atoms) to lists."
  (expr-array->atoms x)

  ///

  (defrule atom-list-list-corep-of-expr-array-list->atoms
    (implies (and (expr-list-corep exprs)
                  (expr-list-case-array exprs))
             (atom-list-list-corep (expr-array-list->atoms exprs)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-frame-list->dims ((x expr-listp))
  :guard (expr-list-case-frame x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee expr-frame->dims) to lists."
  (expr-frame->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-frame-list->exprs ((x expr-listp))
  :guard (expr-list-case-frame x)
  :returns (exprss expr-list-listp)
  :short "Lift @(tsee expr-frame->exprs) to lists."
  (expr-frame->exprs x)

  ///

  (defrule expr-list-list-corep-of-expr-frame-list->exprs
    (implies (and (expr-list-corep exprs)
                  (expr-list-case-frame exprs))
             (expr-list-list-corep (expr-frame-list->exprs exprs)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection shape-append-list->shapes ((x shape-listp))
  :guard (shape-list-case-append x)
  :returns (shapess shape-list-listp)
  :short "Lift @(tsee shape-append->shapes) to lists."
  (shape-append->shapes x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-shape-list->shape ((x ispace-listp))
  :guard (ispace-list-case-shape x)
  :returns (shapes shape-listp)
  :short "Lift @(tsee ispace-shape->shape) to lists."
  (ispace-shape->shape x)

  ///

  (defrule shape-list-corep-of-ispace-shape-list->shape
    (implies (and (ispace-list-corep ispaces)
                  (ispace-list-case-shape ispaces))
             (shape-list-corep (ispace-shape-list->shape ispaces)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection var+type?-list->var ((x var+type?-listp))
  :returns (strings string-listp)
  :short "Lift @(tsee var+type?->var) to lists."
  (var+type?->var x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var+type?->type-or-err ((vt var+type?-p))
  :returns (type type-resultp)
  :short "Extract the type from a variable with an optional type,
          returning an error if the type is absent."
  (b* ((type? (var+type?->type? vt)))
    (type-option-case
     type?
     :none (reserr nil)
     :some type?.val))

  ///

  (defruled type-corep-of-var+type?->type-or-err
    (implies (and (var+type?-corep x)
                  (not (reserrp (var+type?->type-or-err x))))
             (type-corep (var+type?->type-or-err x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var+type?-list->type-list-or-err ((x var+type?-listp))
  :returns (types type-list-resultp)
  :short "Extract the types from a list of variables with optional types,
          returning an error if any type is absent."
  (b* (((when (endp x)) nil)
       ((ok type) (var+type?->type-or-err (car x)))
       ((ok types) (var+type?-list->type-list-or-err (cdr x))))
    (cons type types))

  ///

  (defruled type-list-corep-of-var+type?-list->type-list
    (implies (and (var+type?-list-corep x)
                  (not (reserrp (var+type?-list->type-list-or-err x))))
             (type-list-corep (var+type?-list->type-list-or-err x)))
    :induct t
    :enable (var+type?-list->type-list-or-err
             type-corep-of-var+type?->type-or-err)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+shape-list->type ((x type+shape-listp))
  :returns (types type-listp)
  :short "Lift @(tsee type+shape->type) to lists."
  (type+shape->type x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+shape-list->shape ((x type+shape-listp))
  :returns (ispaces shape-listp)
  :short "Lift @(tsee type+shape->shape) to lists."
  (type+shape->shape x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+ispace-list->type ((x type+ispace-listp))
  :returns (types type-listp)
  :short "Lift @(tsee type+ispace->type) to lists."
  (type+ispace->type x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type+ispace-list->ispace ((x type+ispace-listp))
  :returns (ispaces ispace-listp)
  :short "Lift @(tsee type+ispace->ispace) to lists."
  (type+ispace->ispace x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var->name ((var ispace-varp))
  :returns (name stringp)
  :short "Name of an ispace variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both summands have a string field,
     which is the name of the variable."))
  (ispace-var-case var
                   :dim var.name
                   :shape var.name))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-var-list->name ((x ispace-var-listp))
  :returns (names string-listp)
  :short "Lift @(tsee ispace-var->name) to lists."
  (ispace-var->name x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var->name ((var type-varp))
  :returns (name stringp)
  :short "Name of a type variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both summands have a string field,
     which is the name of the variable."))
  (type-var-case var
                 :atom var.name
                 :array var.name))

;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-var-list->name ((x type-var-listp))
  :returns (names string-listp)
  :short "Lift @(tsee type-var->name) to lists."
  (type-var->name x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-atomp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type has the atom kind."
  (type-case type
             :var (type-var-case type.var :atom)
             :base t
             :array nil
             :bracket nil
             :fun t
             :forall t
             :pi t
             :sigma t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-names-of-ispace-vars ((vars ispace-var-setp))
  :returns (mv (dim-names string-setp) (shape-names string-setp))
  :short "Extract the sets of dimension and shape variable names
          from a set of ispace variables."
  (b* (((when (set::emptyp (ispace-var-set-fix vars))) (mv nil nil))
       ((mv dim-vars shape-vars)
        (dim/shape-names-of-ispace-vars (set::tail vars)))
       (param (set::head vars)))
    (ispace-var-case
     param
     :dim (mv (set::insert param.name dim-vars) shape-vars)
     :shape (mv dim-vars (set::insert param.name shape-vars))))
  :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-names-of-type-vars ((vars type-var-setp))
  :returns (mv (atom-names string-setp) (array-names string-setp))
  :short "Extract the sets of atom and array type variable names
          from a set of type variables."
  (b* (((when (set::emptyp (type-var-set-fix vars))) (mv nil nil))
       ((mv atom-vars array-vars)
        (atom/array-names-of-type-vars (set::tail vars)))
       (var (set::head vars)))
    (type-var-case
     var
     :atom (mv (set::insert var.name atom-vars) array-vars)
     :array (mv atom-vars (set::insert var.name array-vars))))
  :prepwork ((local (in-theory (enable emptyp-of-type-var-set-fix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var+type?-list-set-vars ((vars string-listp) (var+types var+type?-listp))
  :returns (new-var+types var+type?-listp)
  :short "Replace, in a list of variables with optional types,
          the variables with given ones, keeping the optional types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists are expected to have the same length.
     We should make this a guard."))
  (b* (((when (endp var+types)) nil)
       ((when (endp vars)) (var+type?-list-fix var+types))
       (vt (car var+types)))
    (cons (make-var+type? :var (car vars) :type? (var+type?->type? vt))
          (var+type?-list-set-vars (cdr vars) (cdr var+types)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-dims-from-names ((names string-setp))
  :returns (vars ispace-var-setp)
  :short "Set of dimension ispace variables with the given names."
  (cond ((set::emptyp (string-sfix names)) nil)
        (t (set::insert (ispace-var-dim (set::head names))
                        (ispace-var-dims-from-names (set::tail names)))))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-string-sfix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define ispace-var-shapes-from-names ((names string-setp))
  :returns (vars ispace-var-setp)
  :short "Set of shape ispace variables with the given names."
  (cond ((set::emptyp (string-sfix names)) nil)
        (t (set::insert (ispace-var-shape (set::head names))
                        (ispace-var-shapes-from-names (set::tail names)))))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-string-sfix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define type-var-atoms-from-names ((names string-setp))
  :returns (vars type-var-setp)
  :short "Set of atom-kind type variables with the given names."
  (cond ((set::emptyp (string-sfix names)) nil)
        (t (set::insert (type-var-atom (set::head names))
                        (type-var-atoms-from-names (set::tail names)))))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-string-sfix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define type-var-arrays-from-names ((names string-setp))
  :returns (vars type-var-setp)
  :short "Set of array-kind type variables with the given names."
  (cond ((set::emptyp (string-sfix names)) nil)
        (t (set::insert (type-var-array (set::head names))
                        (type-var-arrays-from-names (set::tail names)))))
  :prepwork ((local (in-theory (enable acl2::emptyp-of-string-sfix))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule expr-listp-of-append-all
  :short "Type of @(tsee append-all) applied to lists of lists of expressions."
  (implies (expr-list-listp lists)
           (expr-listp (append-all lists)))
  :induct t
  :enable append-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule atom-listp-of-append-all
  :short "Type of @(tsee append-all) applied to lists of lists of atoms."
  (implies (atom-list-listp lists)
           (atom-listp (append-all lists)))
  :induct t
  :enable append-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule shape-listp-of-mv-nth-1-of-list-prefix-join
  :short "Type of the join returned by @(tsee list-prefix-join)
          on a list of lists of shapes."
  (implies (shape-list-listp lists)
           (shape-listp (mv-nth 1 (list-prefix-join lists))))
  :induct t
  :enable list-prefix-join)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule dim-list-listp-of-list-to-singleton
  :short "Type of @(tsee list-to-singletons) on a list of dimensions."
  (implies (dim-listp dims)
           (dim-list-listp (list-to-singletons dims)))
  :induct t
  :enable list-to-singletons)
