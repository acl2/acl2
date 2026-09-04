; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-well-formedness")
(include-book "abstract-syntax-derived-fixtypes")
(include-book "lists")

(include-book "defsort/duplicated-members" :dir :system)
(include-book "kestrel/fty/string-set" :dir :system)
(include-book "kestrel/typed-lists-light/nat-list-listp" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* typep-when-result-not-error
                           type-listp-when-result-not-error
                           ast-wfp-rules)))

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

  (defret shape-list-wfp-of-shape-dims-list
    (equal (shape-list-wfp (shape-dims-list dimss))
           (dim-list-list-wfp dimss))
    :hints (("Goal" :induct t))))

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

  (defret atom-list-wfp-of-atom-base-list
    (atom-list-wfp atoms)
    :hints (("Goal" :induct t))))

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
  (expr-array->atoms x))

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
  (expr-frame->exprs x))

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

  (defret shape-list-wfp-of-ispace-shape-list->shape
    (shape-list-wfp shapes)
    :hyp (and (ispace-list-case-shape x)
              (ispace-list-wfp x))
    :hints (("Goal" :induct t)))

  (defrule shape-list-count-of-ispace-shape-list->shape
    (implies (ispace-list-case-shape x)
             (<= (shape-list-count (ispace-shape-list->shape x))
                 (ispace-list-count x)))
    :rule-classes :linear
    :induct t
    :expand ((:free (a b) (shape-list-count (cons a b)))
             (ispace-list-count x))))

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

  (defret type-wfp-of-var+type?->type-or-err
    (implies (not (reserrp type))
             (type-wfp type))
    :hyp (var+type?-wfp vt)
    :hints (("Goal" :in-theory (enable var+type?-wfp
                                       type-option-wfp
                                       type-option-some->val)))))

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

  (defret type-list-wfp-of-var+type?-list->type-list-or-err
    (implies (not (reserrp types))
             (type-list-wfp types))
    :hyp (var+type?-list-wfp x)
    :hints (("Goal"
             :induct t
            ))))

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

(define shape-from-ispace ((ispace ispacep))
  :returns (shape shapep)
  :short "Turn an ispace into a shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the ispace is already a shape, it is unchanged.
     Otherwise, we turn the dimension into a singleton shape."))
  (ispace-case
   ispace
   :dim (shape-dims (list ispace.dim))
   :shape ispace.shape))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection shape-list-from-ispace-list ((x ispace-listp))
  :returns (shapes shape-listp)
  :short "Lift @(tsee shape-from-ispace) to lists."
  (shape-from-ispace x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-atom-kindp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type has the atom kind."
  :long
  (xdoc::topstring
   (xdoc::p
    "Function types are atom-kinded,
     except that a nullary function type stands for its output type
     (see @(tsee type)),
     and thus it has the kind of its output type."))
  (type-case type
             :var (type-var-case type.var :atom)
             :base t
             :array nil
             :bracket nil
             :fun t
             :funn (if (consp type.in)
                       t
                     (type-atom-kindp type.out))
             :forall t
             :foralln t
             :pi t
             :pin t
             :sigma t
             :sigman t)
  :measure (type-count type))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-list-atom-kindp (x)
  :guard (type-listp x)
  :short "Lift @(tsee type-atom-kindp) to lists."
  (type-atom-kindp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-array-kindp ((type typep))
  :returns (yes/no booleanp)
  :short "Check if a type has the array kind."
  (not (type-atom-kindp type))

  ///

  (defruled type-array-kindp-alt-def
    (equal (type-array-kindp type)
           (type-case type
                      :var (type-var-case type.var :array)
                      :base nil
                      :array t
                      :bracket t
                      :fun nil
                      :funn (if (consp type.in)
                                nil
                              (type-array-kindp type.out))
                      :forall nil
                      :foralln nil
                      :pi nil
                      :pin nil
                      :sigma nil
                      :sigman nil))
    :hints (("Goal"
             :expand ((type-atom-kindp type))
             :in-theory (enable type-array-kindp)))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist type-list-array-kindp (x)
  :guard (type-listp x)
  :short "Lift @(tsee type-array-kindp) to lists."
  (type-array-kindp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-scalar ((type typep))
  :guard (type-atom-kindp type)
  :returns (scalar-type typep)
  :short "Lift an atom type to a scalar (i.e. zero-ranked) array type."
  (make-type-array :elem type :ispace (ispace-shape (shape-dims nil)))

  ///

  (defret type-array-kindp-of-type-scalar
    (type-array-kindp scalar-type)
    :hints (("Goal" :in-theory (enable type-array-kindp-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-ensure-array ((type typep))
  :returns (type1 typep)
  :short "Ensure that a type is an array type,
          lifting atom types to scalar array types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Remora's syntax allows atom types where array types are expected,
     with those atom types being regarded as scalar (i.e. 0-rank) array types.
     This function explicates this optional lifting:
     it leaves array types unchanged,
     and it turns atom types
     into scalar array types (i.e. with no dimensions)."))
  (if (type-atom-kindp type)
      (make-type-array :elem type :ispace (ispace-shape (shape-dims nil)))
    (type-fix type)))

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
          (var+type?-list-set-vars (cdr vars) (cdr var+types))))

  ///

  (defret len-of-var+type?-list-set-vars
    (equal (len new-var+types)
           (len var+types))
    :hints (("Goal" :induct t :in-theory (enable len)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-fun-types ((in type-listp) (out typep))
  :returns (type typep)
  :short "Nest zero or more unary function types,
          from zero or more input types and one final output type."
  (cond ((endp in) (type-fix out))
        (t (make-type-fun :in (car in)
                          :out (nest-fun-types (cdr in) out))))
  :verify-guards :after-returns

  ///

  (defret type-wfp-of-nest-fun-types
    (equal (type-wfp type)
           (and (type-list-wfp in)
                (type-wfp out)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-forall-types ((params type-var-listp) (body typep))
  :returns (type typep)
  :short "Nest zero or more unary universal types,
          from zero or more parameters and one final body type."
  (cond ((endp params) (type-fix body))
        (t (make-type-forall :param (car params)
                             :body (nest-forall-types (cdr params) body))))
  :verify-guards :after-returns

  ///

  (defret type-wfp-of-nest-forall-types
    (equal (type-wfp type)
           (and (type-var-list-wfp params)
                (type-wfp body)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-pi-types ((params ispace-var-listp) (body typep))
  :returns (type typep)
  :short "Nest zero or more unary product types,
          from zero or more parameters and one final body type."
  (cond ((endp params) (type-fix body))
        (t (make-type-pi :param (car params)
                         :body (nest-pi-types (cdr params) body))))
  :verify-guards :after-returns

  ///

  (defret type-wfp-of-nest-pi-types
    (equal (type-wfp type)
           (and (ispace-var-list-wfp params)
                (type-wfp body)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-sigma-types ((params ispace-var-listp) (body typep))
  :returns (type typep)
  :short "Nest zero or more unary sum types,
          from zero or more parameters and one final body type."
  (cond ((endp params) (type-fix body))
        (t (make-type-sigma :param (car params)
                            :body (nest-sigma-types (cdr params) body))))
  :verify-guards :after-returns

  ///

  (defret type-wfp-of-nest-sigma-types
    (equal (type-wfp type)
           (and (ispace-var-list-wfp params)
                (type-wfp body)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-app-exprs ((fun exprp) (args expr-listp))
  :returns (expr exprp)
  :short "Nest zero or more unary term applications,
          from one initial function expression
          and zero or more argument expressions."
  (cond ((endp args) (expr-fix fun))
        (t (nest-app-exprs (make-expr-app :fun fun :arg (car args))
                           (cdr args))))

  ///

  (defret expr-wfp-of-nest-app-exprs
    (equal (expr-wfp expr)
           (and (expr-wfp fun)
                (expr-list-wfp args)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-tapp-exprs ((fun exprp) (args type-listp))
  :returns (expr exprp)
  :short "Nest zero or more unary type applications,
          from one initial function expression
          and zero or more argument types."
  (cond ((endp args) (expr-fix fun))
        (t (nest-tapp-exprs (make-expr-tapp :fun fun :arg (car args))
                            (cdr args))))

  ///

  (defret expr-wfp-of-nest-tapp-exprs
    (equal (expr-wfp expr)
           (and (expr-wfp fun)
                (type-list-wfp args)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-iapp-exprs ((fun exprp) (args ispace-listp))
  :returns (expr exprp)
  :short "Nest zero or more unary ispace applications,
          from one initial function expression
          and zero or more argument ispaces."
  (cond ((endp args) (expr-fix fun))
        (t (nest-iapp-exprs (make-expr-iapp :fun fun :arg (car args))
                            (cdr args))))

  ///

  (defret expr-wfp-of-nest-iapp-exprs
    (equal (expr-wfp expr)
           (and (expr-wfp fun)
                (ispace-list-wfp args)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-lambda-exprs ((params var+type?-listp)
                           (body exprp)
                           (type? type-optionp))
  :returns (expr exprp)
  :short "Nest zero or more unary expression abstractions,
          from zero or more parameters,
          one final body expression,
          and the optional type of that body."
  :long
  (xdoc::topstring
   (xdoc::p
    "The optional type annotation applies to the body,
     so it travels with the innermost abstraction,
     as in @(tsee lambda-curried-body);
     the outer abstractions carry no annotation."))
  (cond ((endp params) (expr-fix body))
        (t (make-expr-array
            :dims nil
            :atoms (list (make-atom-lambda
                          :param (car params)
                          :body (nest-lambda-exprs (cdr params) body type?)
                          :type? (if (endp (cdr params)) type? nil))))))
  :verify-guards :after-returns

  ///

  (defret expr-wfp-of-nest-lambda-exprs
    (equal (expr-wfp expr)
           (if (consp params)
               (and (var+type?-list-wfp params)
                    (expr-wfp body)
                    (type-option-wfp type?))
             (expr-wfp body)))
    :hints (("Goal" :induct t :in-theory (enable expr-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-tlambda-exprs ((params type-var-listp) (body exprp))
  :returns (expr exprp)
  :short "Nest zero or more unary type abstractions,
          from zero or more parameters and one final body expression."
  (cond ((endp params) (expr-fix body))
        (t (make-expr-array
            :dims nil
            :atoms (list (make-atom-tlambda
                          :param (car params)
                          :body (nest-tlambda-exprs (cdr params) body))))))
  :verify-guards :after-returns

  ///

  (defret expr-wfp-of-nest-tlambda-exprs
    (equal (expr-wfp expr)
           (and (type-var-list-wfp params)
                (expr-wfp body)))
    :hints (("Goal" :induct t :in-theory (enable expr-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-ilambda-exprs ((params ispace-var-listp) (body exprp))
  :returns (expr exprp)
  :short "Nest zero or more unary ispace abstractions,
          from zero or more parameters and one final body expression."
  (cond ((endp params) (expr-fix body))
        (t (make-expr-array
            :dims nil
            :atoms (list (make-atom-ilambda
                          :param (car params)
                          :body (nest-ilambda-exprs (cdr params) body))))))
  :verify-guards :after-returns

  ///

  (defret expr-wfp-of-nest-ilambda-exprs
    (equal (expr-wfp expr)
           (and (ispace-var-list-wfp params)
                (expr-wfp body)))
    :hints (("Goal" :induct t :in-theory (enable expr-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-unbox-exprs ((ispaces ispace-var-listp)
                          (var stringp)
                          (target exprp)
                          (body exprp)
                          (type? type-optionp))
  :returns (expr exprp)
  :short "Nest zero or more unary unboxing expressions,
          from zero or more ispace variables,
          one bound variable,
          one target expression,
          one final body expression,
          and the optional type of the whole expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only the outermost unboxing has the target expression
     and the optional type,
     which is the type of the whole unboxing expression;
     each inner one unboxes the bound variable itself
     and carries no type.
     Since a target is outside the scope of the binding,
     the variable used as target at each inner level
     refers to the binding of the enclosing level,
     and the final body sees the fully unboxed value."))
  (cond ((endp ispaces) (expr-fix body))
        (t (make-expr-unbox
            :ispace (car ispaces)
            :var var
            :target target
            :body (nest-unbox-exprs-loop (cdr ispaces) var body)
            :type? type?)))

  :prepwork
  ((define nest-unbox-exprs-loop ((ispaces ispace-var-listp)
                                  (var stringp)
                                  (body exprp))
     :returns (expr exprp)
     :parents nil
     (cond ((endp ispaces) (expr-fix body))
           (t (make-expr-unbox
               :ispace (car ispaces)
               :var var
               :target (expr-var var)
               :body (nest-unbox-exprs-loop (cdr ispaces) var body)
               :type? nil)))
     :verify-guards :after-returns

     ///

     (defret expr-wfp-of-nest-unbox-exprs-loop
       (equal (expr-wfp expr)
              (if (consp ispaces)
                  (and (ispace-var-list-wfp ispaces)
                       (valid-identifier-string-p (str-fix var))
                       (expr-wfp body))
                (expr-wfp body)))
       :hints (("Goal" :induct t :in-theory (enable expr-wfp))))))

  ///

  (defret expr-wfp-of-nest-unbox-exprs
    (equal (expr-wfp expr)
           (if (consp ispaces)
               (and (ispace-var-list-wfp ispaces)
                    (valid-identifier-string-p (str-fix var))
                    (expr-wfp target)
                    (expr-wfp body)
                    (type-option-wfp type?))
             (expr-wfp body)))
    :hints (("Goal" :in-theory (enable expr-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nest-box-exprs ((ispaces ispace-listp) (body exprp))
  :returns (expr exprp)
  :short "Nest zero or more unary boxing atoms without types,
          from zero or more ispaces and one final body expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each boxing atom is wrapped into a zero-rank array expression.
     The boxing atoms have no types:
     this function builds the inner boxes of
     the nest that an n-ary boxing atom desugars to,
     whose types can only be computed during type checking
     (see @(tsee atom))."))
  (cond ((endp ispaces) (expr-fix body))
        (t (make-expr-array
            :dims nil
            :atoms (list (make-atom-box
                          :ispace (car ispaces)
                          :array (nest-box-exprs (cdr ispaces) body)
                          :type? nil)))))
  :verify-guards :after-returns

  ///

  (defret expr-wfp-of-nest-box-exprs
    (equal (expr-wfp expr)
           (and (ispace-list-wfp ispaces)
                (expr-wfp body)))
    :hints (("Goal" :induct t :in-theory (enable expr-wfp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-type-forall/foralln ((params type-var-listp) (body typep))
  :guard (consp params)
  :returns (type typep)
  :short "Construct a unary or n-ary universal type,
          depending on the number of parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one parameter, as required by the guard.
     If there is exactly one parameter,
     we construct a unary universal type over that parameter;
     if there are two or more parameters,
     we construct an n-ary universal type,
     consistently with the requirement that
     n-ary universal types have two or more parameters
     (see @(tsee type))."))
  (if (endp (cdr params))
      (make-type-forall :param (car params) :body body)
    (make-type-foralln :params params :body body))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-type-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-type-pi/pin ((params ispace-var-listp) (body typep))
  :guard (consp params)
  :returns (type typep)
  :short "Construct a unary or n-ary product type,
          depending on the number of parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one parameter, as required by the guard.
     If there is exactly one parameter,
     we construct a unary product type over that parameter;
     if there are two or more parameters,
     we construct an n-ary product type,
     consistently with the requirement that
     n-ary product types have two or more parameters
     (see @(tsee type))."))
  (if (endp (cdr params))
      (make-type-pi :param (car params) :body body)
    (make-type-pin :params params :body body))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-ispace-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-type-sigma/sigman ((params ispace-var-listp) (body typep))
  :guard (consp params)
  :returns (type typep)
  :short "Construct a unary or n-ary sum type,
          depending on the number of parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one parameter, as required by the guard.
     If there is exactly one parameter,
     we construct a unary sum type over that parameter;
     if there are two or more parameters,
     we construct an n-ary sum type,
     consistently with the requirement that
     n-ary sum types have two or more parameters
     (see @(tsee type))."))
  (if (endp (cdr params))
      (make-type-sigma :param (car params) :body body)
    (make-type-sigman :params params :body body))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-ispace-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-atom-lambda/lambdan ((params var+type?-listp)
                                  (body exprp)
                                  (type? type-optionp))
  :guard (consp params)
  :returns (atom atomp)
  :short "Construct a unary or n-ary expression lambda abstraction,
          depending on the number of parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one parameter, as required by the guard.
     If there is exactly one parameter,
     we construct a unary lambda abstraction over that parameter;
     if there are two or more parameters,
     we construct an n-ary lambda abstraction,
     consistently with the requirement that
     n-ary lambda abstractions have two or more parameters
     (see @(tsee atom))."))
  (if (endp (cdr params))
      (make-atom-lambda :param (car params) :body body :type? type?)
    (make-atom-lambdan :params params :body body :type? type?))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-var+type?-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-atom-tlambda/tlambdan ((params type-var-listp) (body exprp))
  :guard (consp params)
  :returns (atom atomp)
  :short "Construct a unary or n-ary type lambda abstraction,
          depending on the number of parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one parameter, as required by the guard.
     If there is exactly one parameter,
     we construct a unary type lambda abstraction over that parameter;
     if there are two or more parameters,
     we construct an n-ary type lambda abstraction,
     consistently with the requirement that
     n-ary type lambda abstractions have two or more parameters
     (see @(tsee atom))."))
  (if (endp (cdr params))
      (make-atom-tlambda :param (car params) :body body)
    (make-atom-tlambdan :params params :body body))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-type-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-atom-ilambda/ilambdan ((params ispace-var-listp) (body exprp))
  :guard (consp params)
  :returns (atom atomp)
  :short "Construct a unary or n-ary ispace lambda abstraction,
          depending on the number of parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one parameter, as required by the guard.
     If there is exactly one parameter,
     we construct a unary ispace lambda abstraction over that parameter;
     if there are two or more parameters,
     we construct an n-ary ispace lambda abstraction,
     consistently with the requirement that
     n-ary ispace lambda abstractions have two or more parameters
     (see @(tsee atom))."))
  (if (endp (cdr params))
      (make-atom-ilambda :param (car params) :body body)
    (make-atom-ilambdan :params params :body body))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-ispace-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-binders-count ((type typep))
  :returns (count natp)
  :short "Number of variables bound by the binder of a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for the binder of universal, product, and sum types.
     We return 0 for the other types."))
  (type-case type
             :var 0
             :base 0
             :array 0
             :bracket 0
             :fun 0
             :funn 0
             :forall 1
             :foralln (len type.params)
             :pi 1
             :pin (len type.params)
             :sigma 1
             :sigman (len type.params)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-curried-out ((in type-listp) (out typep))
  :guard (consp in)
  :returns (new-out typep)
  :short "Peel the first input type from an n-ary function type
          and return the remaining function type."
  :long
  (xdoc::topstring
   (xdoc::p
    "An n-ary function type with one or more input types
     is sugar for a nested sequence of unary function types.
     This function treats an n-ary function type
     with at least one input type as that sequence,
     and it returns the output of the outermost unary function type.
     This is the output type of the whole function type
     when there is just one input type,
     otherwise it is another function type,
     without the first input type.
     This is analogous to @(tsee forall-curried-body),
     with input types in place of bound variables."))
  (cond ((endp (cdr in)) (type-fix out))
        (t (make-type-funn :in (cdr in) :out out)))
  :hooks ((:fix :hints (("Goal" :in-theory (enable cdr-of-type-list-fix)))))

  ///

  (defrule type-count-of-fun-curried-out
    (implies (and (type-case type :funn)
                  (consp (type-funn->in type)))
             (< (type-count (fun-curried-out (type-funn->in type)
                                             (type-funn->out type)))
                (type-count type)))
    :rule-classes :linear
    :enable fun-curried-out
    :expand ((type-count type)
             (type-list-count (type-funn->in type))
             (type-count (type-funn (cdr (type-funn->in type))
                                    (type-funn->out type))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define forall-curried-body ((params type-var-listp) (body typep))
  :guard (>= (len params) 2)
  :returns (new-body typep)
  :short "Peel the first parameter from a universal type
          and return the remaining body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A universal type with two or more parameters
     is sugar for a nested sequence of one-parameter universal types.
     This function treats an n-ary universal type with at least two parameters
     as that sequence,
     and it returns the body of the outermost universal type."))
  (cond ((endp (cdr params)) (prog2$ (impossible) (type-fix body)))
        (t (make-type-forall/foralln (cdr params) body)))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-type-var-list-fix)))))

  ///

  (defrule type-count-of-forall-curried-body
    (implies (type-case type :foralln)
             (<= (type-count (forall-curried-body (type-foralln->params type)
                                                  (type-foralln->body type)))
                 (type-count type)))
    :rule-classes :linear
    :enable (forall-curried-body
             make-type-forall/foralln)
    :expand ((type-count type)
             (type-count (type-forall (cadr (type-foralln->params type))
                                      (type-foralln->body type)))
             (type-count (type-foralln (cdr (type-foralln->params type))
                                       (type-foralln->body type)))))

  (defrule type-binders-count-of-forall-curried-body
    (implies
     (and (type-case type :foralln)
          (equal (type-count (forall-curried-body (type-foralln->params type)
                                                  (type-foralln->body type)))
                 (type-count type)))
     (< (type-binders-count (forall-curried-body (type-foralln->params type)
                                                 (type-foralln->body type)))
        (type-binders-count type)))
    :rule-classes :linear
    :enable (forall-curried-body
             type-binders-count
             make-type-forall/foralln
             len)
    :expand ((type-count type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pi-curried-body ((params ispace-var-listp) (body typep))
  :guard (>= (len params) 2)
  :returns (new-body typep)
  :short "Peel the first parameter from a product type
          and return the remaining body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee forall-curried-body)."))
  (cond ((endp (cdr params)) (prog2$ (impossible) (type-fix body)))
        (t (make-type-pi/pin (cdr params) body)))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-ispace-var-list-fix)))))

  ///

  (defrule type-count-of-pi-curried-body
    (implies (type-case type :pin)
             (<= (type-count (pi-curried-body (type-pin->params type)
                                              (type-pin->body type)))
                 (type-count type)))
    :rule-classes :linear
    :enable (pi-curried-body
             make-type-pi/pin)
    :expand ((type-count type)
             (type-count (type-pi (cadr (type-pin->params type))
                                  (type-pin->body type)))
             (type-count (type-pin (cdr (type-pin->params type))
                                   (type-pin->body type)))))

  (defrule type-binders-count-of-pi-curried-body
    (implies
     (and (type-case type :pin)
          (equal (type-count (pi-curried-body (type-pin->params type)
                                              (type-pin->body type)))
                 (type-count type)))
     (< (type-binders-count (pi-curried-body (type-pin->params type)
                                             (type-pin->body type)))
        (type-binders-count type)))
    :rule-classes :linear
    :enable (pi-curried-body type-binders-count make-type-pi/pin len)
    :expand ((type-count type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sigma-curried-body ((params ispace-var-listp) (body typep))
  :guard (consp params)
  :returns (new-body typep)
  :short "Peel the first parameter from a sum type
          and return the remaining body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee pi-curried-body)."))
  (cond ((endp (cdr params)) (type-fix body))
        (t (make-type-sigma/sigman (cdr params) body)))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-ispace-var-list-fix)))))

  ///

  (defrule type-count-of-sigma-curried-body
    (implies (type-case type :sigman)
             (<= (type-count (sigma-curried-body (type-sigman->params type)
                                                 (type-sigman->body type)))
                 (type-count type)))
    :rule-classes :linear
    :enable (sigma-curried-body
             make-type-sigma/sigman)
    :expand ((type-count type)
             (type-count (type-sigma (cadr (type-sigman->params type))
                                     (type-sigman->body type)))
             (type-count (type-sigman (cdr (type-sigman->params type))
                                      (type-sigman->body type)))))

  (defrule type-binders-count-of-sigma-curried-body
    (implies
     (and (type-case type :sigman)
          (equal (type-count (sigma-curried-body (type-sigman->params type)
                                                 (type-sigman->body type)))
                 (type-count type)))
     (< (type-binders-count (sigma-curried-body (type-sigman->params type)
                                                (type-sigman->body type)))
        (type-binders-count type)))
    :rule-classes :linear
    :enable (sigma-curried-body type-binders-count make-type-sigma/sigman len)
    :expand ((type-count type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lambda-curried-body ((params var+type?-listp)
                             (body exprp)
                             (type? type-optionp))
  :guard (consp params)
  :returns (new-body exprp)
  :short "Peel the first parameter from a lambda abstraction
          and return the remaining body expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee forall-curried-body).")
   (xdoc::p
    "The optional body type annotation applies to the body,
     so it travels with the innermost lambda abstraction:
     if there are two or more parameters,
     the returned lambda abstraction carries the annotation;
     if there is just one parameter,
     the annotation pertains to the returned body,
     and it is up to the caller to use it as appropriate."))
  (cond ((endp (cdr params)) (expr-fix body))
        (t (expr-atom (make-atom-lambda/lambdan (cdr params) body type?))))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-var+type?-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tlambda-curried-body ((params type-var-listp) (body exprp))
  :guard (consp params)
  :returns (new-body exprp)
  :short "Peel the first parameter from a type lambda abstraction
          and return the remaining body expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee forall-curried-body)."))
  (cond ((endp (cdr params)) (expr-fix body))
        (t (expr-atom (make-atom-tlambda/tlambdan (cdr params) body))))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-type-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ilambda-curried-body ((params ispace-var-listp) (body exprp))
  :guard (consp params)
  :returns (new-body exprp)
  :short "Peel the first parameter from an ispace lambda abstraction
          and return the remaining body expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee forall-curried-body)."))
  (cond ((endp (cdr params)) (expr-fix body))
        (t (expr-atom (make-atom-ilambda/ilambdan (cdr params) body))))
  :hooks ((:fix :hints (("Goal"
                         :in-theory (enable cdr-of-ispace-var-list-fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule atom-count-when-box-gap
  :short "The count of a unary boxing atom exceeds
          the count of its array expression by more than one."
  :long
  (xdoc::topstring
   (xdoc::p
    "The automatically generated linear rules only provide
     an excess of one.
     The larger gap serves to justify measures of the form
     @('(+ 1 (expr-count ...))') over the array expression,
     as used by recursive functions that,
     given the array expression of a boxing atom,
     may both recursively descend into it
     and pass it whole to a mutually recursive companion."))
  (implies (atom-case atom :box)
           (< (+ 1 (expr-count (atom-box->array atom)))
              (atom-count atom)))
  :rule-classes :linear
  :expand ((atom-count atom)))
