; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(include-book "kestrel/fty/deffold-map" :dir :system)
(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/fty/string-set" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-variable-operations
  :parents (abstract-syntax)
  :short "Operations on ASTs related to variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include
     collection of (bound, free, and all) variables,
     substitutions of variables with other ASTs,
     and variable renamings.")
   (xdoc::p
    "The substitutions are represented as maps
     from strings (variable names) to ASTs.
     Since ispaces have distinct dimension and shape variables,
     we use two separate maps for ispace variable substitutions,
     one for dimension variables and one for shape variables.")
   (xdoc::p
    "The renamings are represented as maps from strings to strings.")
   (xdoc::p
    "Dimensions contain dimension variables,
     but no shape or type or expression variables;
     so they only need one substitution or renaming map.
     All the variables in a dimension are free,
     because dimensions have no binders.")
   (xdoc::p
    "Shapes and ispaces contain dimension and shape variables,
     but no type or expression variables;
     so they need two substitution or renaming maps.
     All the variables in a shape or ispace are free,
     because shapes and ispaces have no binders.")
   (xdoc::p
    "Types contain ispace (dimension and shape) and type variables,
     but no expression variables;
     so they need three substitution or renaming maps in general,
     but we provide separate substitution and renaming operations
     for ispace and type variables in types.
     Types have binders for both ispace and type variables,
     so the operations apply to the free ispace and type variables;
     when encountering bound variables,
     they are removed from the substitution and renaming maps.")
   (xdoc::p
    "We also plan to add substitution and renaming operations
     on expressions and atoms,
     involving not only ispace and type variables,
     but also expression variables.")
   (xdoc::p
    "The current substitution and renaming operations
     do not check for variable capture,
     either statically (i.e. in the guard) or dynamically.
     However, we provide predicates to check that no variable is captured.
     See the specific documentation of the substitution and renaming operations
     for more details.")
   (xdoc::p
    "We need to double-check, and possibly revise,
     the treatment of the boxing and unboxing constructs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-ispace-vars ((bind bindp))
  :returns (vars ispace-var-setp)
  :short "Set of ispace variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only an ispace binding binds an ispace variable.
     An ispace function binding does not bind ispace variables:
     it binds an expression variable;
     the ispace parameters of the function are handled separately,
     in the calculation of the free variables of the binding itself."))
  (bind-case
   bind
   :ispace (set::insert bind.var nil)
   :type nil
   :val nil
   :fun nil
   :tfun nil
   :ifun nil
   :cfun nil))

;;;;;;;;;;;;;;;;;;;;

(define bind-list-bound-ispace-vars ((binds bind-listp))
  :returns (vars ispace-var-setp)
  :short "Set of ispace variables bound in a list of bindings."
  (cond ((endp binds) nil)
        (t (set::union (bind-bound-ispace-vars (car binds))
                       (bind-list-bound-ispace-vars (cdr binds)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-type-vars ((bind bindp))
  :returns (vars type-var-setp)
  :short "Set of type variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Only a type binding binds a type variable.
     A type function binding does not bind type variables:
     it binds an expression variable;
     the type parameters of the function are handled separately,
     in the calculation of the free variables of the binding itself."))
  (bind-case
   bind
   :ispace nil
   :type (set::insert bind.var nil)
   :val nil
   :fun nil
   :tfun nil
   :ifun nil
   :cfun nil))

;;;;;;;;;;;;;;;;;;;;

(define bind-list-bound-type-vars ((binds bind-listp))
  :returns (vars type-var-setp)
  :short "Set of type variables bound in a list of bindings."
  (cond ((endp binds) nil)
        (t (set::union (bind-bound-type-vars (car binds))
                       (bind-list-bound-type-vars (cdr binds)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-bound-expr-vars ((bind bindp))
  :returns (vars string-setp)
  :short "Set of expression variables bound in a binding."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value and function bindings each bind an expression variable;
     the ispace and type bindings do not bind expression variables.
     The parameters of the @(':fun') and @(':cfun') bindings
     are not included here:
     they are bound within the function's own body,
     and are handled separately
     in the calculation of the free variables of the binding itself."))
  (bind-case
   bind
   :ispace nil
   :type nil
   :val (set::insert bind.var nil)
   :fun (set::insert bind.var nil)
   :tfun (set::insert bind.var nil)
   :ifun (set::insert bind.var nil)
   :cfun (set::insert bind.var nil)))

;;;;;;;;;;;;;;;;;;;;

(define bind-list-bound-expr-vars ((binds bind-listp))
  :returns (vars string-setp)
  :short "Set of expression variables bound in a list of bindings."
  (cond ((endp binds) nil)
        (t (set::union (bind-bound-expr-vars (car binds))
                       (bind-list-bound-expr-vars (cdr binds)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-ispace-vars
  :short "Set of free ispace variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The free variables of a binder are the ones
     in the thing that the variable is bound to.
     Thus, for the ispace and combined function binders,
     we remove the parameters,
     because the thing that the variable is bound to
     is like a lambda abstraction."))
  :types (dims
          shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog
          string-dim-map
          string-shape-map)
  :result ispace-var-setp
  :default nil
  :combine set::union
  :override
  ((dim :var (set::insert (ispace-var-dim dim.name) nil))
   (shape :var (set::insert (ispace-var-shape shape.name) nil))
   (type :pi
         (set::difference (type-free-ispace-vars type.body)
                          (set::mergesort type.params)))
   (type :sigma
         (set::difference (type-free-ispace-vars type.body)
                          (set::mergesort type.params)))
   (expr :unbox
         (set::union (expr-free-ispace-vars expr.target)
                     (set::difference (expr-free-ispace-vars expr.body)
                                      (set::mergesort expr.ispaces))))
   (expr :let
         (set::union
          (bind-list-free-ispace-vars expr.binds)
          (set::difference (expr-free-ispace-vars expr.body)
                           (bind-list-bound-ispace-vars expr.binds))))
   (atom :ilambda
         (set::difference (expr-free-ispace-vars atom.body)
                          (set::mergesort atom.params)))
   (bind :ifun
         (set::difference (set::union (type-option-free-ispace-vars bind.type?)
                                      (expr-free-ispace-vars bind.expr))
                          (set::mergesort bind.params)))
   (bind :cfun
         (set::difference (set::union
                           (var+type-list-free-ispace-vars bind.params)
                           (set::union (type-free-ispace-vars bind.type)
                                       (expr-free-ispace-vars bind.expr)))
                          (ispace-var-list-option-case
                           bind.iparams?
                           :some (set::mergesort bind.iparams?.val)
                           :none nil))))
  :name ast-free-ispace-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce free-type-vars
  :short "Set of free type variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The free variables of a binder are the ones
     in the thing that the variable is bound to.
     Thus, for the type and combined function binders,
     we remove the parameters,
     because the thing that the variable is bound to
     is like a lambda abstraction."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog
          string-type-map)
  :result type-var-setp
  :default nil
  :combine set::union
  :override
  ((type :var (set::insert type.var nil))
   (type :forall (set::difference (type-free-type-vars type.body)
                                  (set::mergesort type.params)))
   (expr :let
         (set::union (bind-list-free-type-vars expr.binds)
                     (set::difference (expr-free-type-vars expr.body)
                                      (bind-list-bound-type-vars expr.binds))))
   (atom :tlambda
         (set::difference (expr-free-type-vars atom.body)
                          (set::mergesort atom.params)))
   (bind :tfun
         (set::difference (set::union (type-option-free-type-vars bind.type?)
                                      (expr-free-type-vars bind.expr))
                          (set::mergesort bind.params)))
   (bind :cfun
         (set::difference (set::union
                           (var+type-list-free-type-vars bind.params)
                           (set::union (type-free-type-vars bind.type)
                                       (expr-free-type-vars bind.expr)))
                          (type-var-list-option-case
                           bind.tparams?
                           :some (set::mergesort bind.tparams?.val)
                           :none nil))))
  :name ast-free-type-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce all-ispace-vars
  :short "Set of all (i.e. free and bound) ispace variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the variables that occur anywhere,
     including the parameters of product and sum types
     and the ispace variables introduced by ispace binders."))
  :types (dims
          shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :result ispace-var-setp
  :default nil
  :combine set::union
  :override
  ((dim :var (set::insert (ispace-var-dim dim.name) nil))
   (shape :var (set::insert (ispace-var-shape shape.name) nil))
   (type :pi
         (set::union (set::mergesort type.params)
                     (type-all-ispace-vars type.body)))
   (type :sigma
         (set::union (set::mergesort type.params)
                     (type-all-ispace-vars type.body)))
   (bind :ifun
         (set::union (set::mergesort bind.params)
                     (set::union (type-option-all-ispace-vars bind.type?)
                                 (expr-all-ispace-vars bind.expr))))
   (bind :cfun
         (set::union
          (ispace-var-list-option-case
           bind.iparams?
           :some (set::mergesort bind.iparams?.val)
           :none nil)
          (set::union (var+type-list-all-ispace-vars bind.params)
                      (set::union (type-all-ispace-vars bind.type)
                                  (expr-all-ispace-vars bind.expr))))))
  :name ast-all-ispace-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce all-type-vars
  :short "Set of all (i.e. free and bound) type variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the variables that occur anywhere,
     including the parameters of universal types
     and the type variables introduced by type binders."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :result type-var-setp
  :default nil
  :combine set::union
  :override
  ((type :var (set::insert type.var nil))
   (type :forall (set::union (set::mergesort type.params)
                             (type-all-type-vars type.body)))
   (atom :tlambda (set::union (set::mergesort atom.params)
                              (expr-all-type-vars atom.body)))
   (bind :type (set::insert bind.var
                            (type-all-type-vars bind.type)))
   (bind :tfun (set::union (set::mergesort bind.params)
                           (set::union (type-option-all-type-vars bind.type?)
                                       (expr-all-type-vars bind.expr))))
   (bind :cfun (set::union
                (type-var-list-option-case
                 bind.tparams?
                 :some (set::mergesort bind.tparams?.val)
                 :none nil)
                (set::union (var+type-list-all-type-vars bind.params)
                            (set::union (type-all-type-vars bind.type)
                                        (expr-all-type-vars bind.expr))))))
  :name ast-all-type-vars)

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

(define dim/shape-subst-remove-bound ((vars ispace-var-setp)
                                      (dim-subst string-dim-mapp)
                                      (shape-subst string-shape-mapp))
  :returns (mv (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Remove a set of bound ispace variables from
          a dimension substitution and a shape substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a substitution of ispace variables descends under a construct
     that binds the ispace variables in @('vars'),
     those bound variables must not be substituted under the binder.
     Accordingly, we remove them from the domains of the substitution maps:
     the dimension variables in @('vars')
     are removed from the dimension substitution,
     and the shape variables in @('vars')
     are removed from the shape substitution.
     We use @(tsee dim/shape-names-of-ispace-vars)
     to split @('vars') into its dimension and shape variable names.")
   (xdoc::p
    "This is shared by the operations that
     substitute ispace variables in ASTs and that
     check the absence of variable capture by such substitutions."))
  (b* (((mv bound-dim-vars bound-shape-vars)
        (dim/shape-names-of-ispace-vars vars)))
    (mv (omap::delete* bound-dim-vars (string-dim-map-fix dim-subst))
        (omap::delete* bound-shape-vars (string-shape-map-fix shape-subst))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-subst-remove-bound ((vars type-var-setp)
                                       (atom-subst string-type-mapp)
                                       (array-subst string-type-mapp))
  :returns (mv (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Remove a set of bound type variables from
          an atom-kind and an array-kind type substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a substitution of type variables descends under a construct
     that binds the type variables in @('vars'),
     those bound variables must not be substituted under the binder.
     Accordingly, we remove them from the domains of the substitution maps:
     the atom-kind type variables in @('vars')
     are removed from the atom-kind type substitution,
     and the array-kind type variables in @('vars')
     are removed from the array-kind type substitution.
     We use @(tsee atom/array-names-of-type-vars) to split @('vars')
     into its atom-kind and array-kind type variable names.")
   (xdoc::p
    "This is shared by the operations that
     substitute type variables in ASTs and that
     check the absence of variable capture by such substitutions."))
  (b* (((mv bound-atom-vars bound-array-vars)
        (atom/array-names-of-type-vars vars)))
    (mv (omap::delete* bound-atom-vars (string-type-map-fix atom-subst))
        (omap::delete* bound-array-vars (string-type-map-fix array-subst))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-subst-no-capture-p ((vars ispace-var-setp)
                                      (dim-subst string-dim-mapp)
                                      (shape-subst string-shape-mapp))
  :returns (yes/no booleanp)
  :short "Check that a set of bound ispace variables is not captured
          by a dimension substitution and a shape substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a substitution of ispace variables descends under a construct
     that binds the ispace variables in @('vars'),
     after those bound variables have been removed from the substitution
     (see @(tsee dim/shape-subst-remove-bound)),
     none of the bound variables must occur free
     among the values of the resulting substitution maps,
     otherwise substituting under the binder would capture them.
     We check that @('vars') is disjoint from the free ispace variables
     of the dimension and shape substitutions.")
   (xdoc::p
    "This is shared by the cases of @(tsee ast-subst-ispace-vars-no-capture-p)
     for the constructs that bind ispace variables."))
  (set::emptyp
   (set::intersect
    (ispace-var-set-fix vars)
    (set::union (string-dim-map-free-ispace-vars dim-subst)
                (string-shape-map-free-ispace-vars shape-subst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-subst-no-capture-p ((vars type-var-setp)
                                       (atom-subst string-type-mapp)
                                       (array-subst string-type-mapp))
  :returns (yes/no booleanp)
  :short "Check that a set of bound type variables is not captured
          by an atom-kind and an array-kind type substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a substitution of type variables descends under a construct
     that binds the type variables in @('vars'),
     after those bound variables have been removed from the substitution
     (see @(tsee atom/array-subst-remove-bound)),
     none of the bound variables must occur free
     among the values of the resulting substitution maps,
     otherwise substituting under the binder would capture them.
     We check that @('vars') is disjoint from the free type variables
     of the atom-kind and array-kind type substitutions.")
   (xdoc::p
    "This is shared by the cases of @(tsee ast-subst-type-vars-no-capture-p)
     for the constructs that bind type variables."))
  (set::emptyp
   (set::intersect
    (type-var-set-fix vars)
    (set::union (string-type-map-free-type-vars atom-subst)
                (string-type-map-free-type-vars array-subst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce subst-ispace-vars-no-capture-p
  :short "Check that substituting free ispace variables in ASTs
          does not result in variable capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitution consists of two maps,
     one for dimension variables and one for shape variables,
     as in @(tsee ast-subst-ispace-vars).")
   (xdoc::p
    "At each ispace-binding construct,
     we remove the bound variables from the domain of the substitution
     (since they do not get substituted under the binder)
     and we check that those bound parameters do not appear
     among the free ispace variables of the values
     of the resulting (restricted) substitution.
     We then recurse into the body of the binder
     with the restricted substitution.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the substitution
     are actually free in the body of each binder."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :pi
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort type.params)
                                             dim-subst
                                             shape-subst)))
           (and (dim/shape-subst-no-capture-p (set::mergesort type.params)
                                              dim-subst
                                              shape-subst)
                (type-subst-ispace-vars-no-capture-p type.body
                                                     dim-subst
                                                     shape-subst))))
   (type :sigma
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort type.params)
                                             dim-subst
                                             shape-subst)))
           (and (dim/shape-subst-no-capture-p (set::mergesort type.params)
                                              dim-subst
                                              shape-subst)
                (type-subst-ispace-vars-no-capture-p type.body
                                                     dim-subst
                                                     shape-subst))))
   (expr :unbox
         (and (expr-subst-ispace-vars-no-capture-p expr.target
                                                   dim-subst
                                                   shape-subst)
              (b* (((mv dim-subst shape-subst)
                    (dim/shape-subst-remove-bound (set::mergesort expr.ispaces)
                                                  dim-subst
                                                  shape-subst)))
                (and (dim/shape-subst-no-capture-p (set::mergesort expr.ispaces)
                                                   dim-subst
                                                   shape-subst)
                     (expr-subst-ispace-vars-no-capture-p expr.body
                                                          dim-subst
                                                          shape-subst)))))
   (expr :let
         (and (bind-list-subst-ispace-vars-no-capture-p expr.binds
                                                        dim-subst
                                                        shape-subst)
              (b* ((bound-ispace-vars (bind-list-bound-ispace-vars expr.binds))
                   ((mv dim-subst shape-subst)
                    (dim/shape-subst-remove-bound bound-ispace-vars
                                                  dim-subst
                                                  shape-subst)))
                (and (dim/shape-subst-no-capture-p bound-ispace-vars
                                                   dim-subst
                                                   shape-subst)
                     (expr-subst-ispace-vars-no-capture-p expr.body
                                                          dim-subst
                                                          shape-subst)))))
   (atom :ilambda
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort atom.params)
                                             dim-subst
                                             shape-subst)))
           (and (dim/shape-subst-no-capture-p (set::mergesort atom.params)
                                              dim-subst
                                              shape-subst)
                (expr-subst-ispace-vars-no-capture-p atom.body
                                                     dim-subst
                                                     shape-subst))))
   (bind :ifun
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort bind.params)
                                             dim-subst
                                             shape-subst)))
           (and (dim/shape-subst-no-capture-p (set::mergesort bind.params)
                                              dim-subst
                                              shape-subst)
                (type-option-subst-ispace-vars-no-capture-p bind.type?
                                                            dim-subst
                                                            shape-subst)
                (expr-subst-ispace-vars-no-capture-p bind.expr
                                                     dim-subst
                                                     shape-subst))))
   (bind :cfun
         (ispace-var-list-option-case
          bind.iparams?
          :some (b* (((mv dim-subst shape-subst)
                      (dim/shape-subst-remove-bound
                       (set::mergesort bind.iparams?.val)
                       dim-subst
                       shape-subst)))
                  (and (dim/shape-subst-no-capture-p
                        (set::mergesort bind.iparams?.val)
                        dim-subst
                        shape-subst)
                       (var+type-list-subst-ispace-vars-no-capture-p
                        bind.params
                        dim-subst
                        shape-subst)
                       (type-subst-ispace-vars-no-capture-p bind.type
                                                            dim-subst
                                                            shape-subst)
                       (expr-subst-ispace-vars-no-capture-p bind.expr
                                                            dim-subst
                                                            shape-subst)))
          :none (and (var+type-list-subst-ispace-vars-no-capture-p bind.params
                                                                   dim-subst
                                                                   shape-subst)
                     (type-subst-ispace-vars-no-capture-p bind.type
                                                          dim-subst
                                                          shape-subst)
                     (expr-subst-ispace-vars-no-capture-p bind.expr
                                                          dim-subst
                                                          shape-subst)))))
  :name ast-subst-ispace-vars-no-capture-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce subst-type-vars-no-capture-p
  :short "Check that substituting type variables in ASTs
          does not result in variable capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitution consists of two maps,
     one for atom-kind type variables and one for array-kind type variables,
     as in @(tsee ast-subst-type-vars).")
   (xdoc::p
    "At each type-binding construct,
     we remove the bound variables from the domain of the substitution
     (since they do not get substituted under the binder)
     and we check that those bound parameters do not appear
     among the free type variables of the values
     of the resulting (restricted) substitution.
     We then recurse into the body of the binder
     with the restricted substitution.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the substitution
     are actually free in the body of each binder."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((atom-subst string-type-mapp)
               (array-subst string-type-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort type.params)
                                              atom-subst
                                              array-subst)))
           (and (atom/array-subst-no-capture-p (set::mergesort type.params)
                                               atom-subst
                                               array-subst)
                (type-subst-type-vars-no-capture-p type.body
                                                   atom-subst
                                                   array-subst))))
   (expr :let
         (and (bind-list-subst-type-vars-no-capture-p expr.binds
                                                      atom-subst
                                                      array-subst)
              (b* ((bound-type-vars (bind-list-bound-type-vars expr.binds))
                   ((mv atom-subst array-subst)
                    (atom/array-subst-remove-bound bound-type-vars
                                                   atom-subst
                                                   array-subst)))
                (and (atom/array-subst-no-capture-p bound-type-vars
                                                    atom-subst
                                                    array-subst)
                     (expr-subst-type-vars-no-capture-p expr.body
                                                        atom-subst
                                                        array-subst)))))
   (atom :tlambda
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort atom.params)
                                              atom-subst
                                              array-subst)))
           (and (atom/array-subst-no-capture-p (set::mergesort atom.params)
                                               atom-subst
                                               array-subst)
                (expr-subst-type-vars-no-capture-p atom.body
                                                   atom-subst
                                                   array-subst))))
   (bind :tfun
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort bind.params)
                                              atom-subst
                                              array-subst)))
           (and (atom/array-subst-no-capture-p (set::mergesort bind.params)
                                               atom-subst
                                               array-subst)
                (type-option-subst-type-vars-no-capture-p bind.type?
                                                          atom-subst
                                                          array-subst)
                (expr-subst-type-vars-no-capture-p bind.expr
                                                   atom-subst
                                                   array-subst))))
   (bind :cfun
         (type-var-list-option-case
          bind.tparams?
          :some (b* (((mv atom-subst array-subst)
                      (atom/array-subst-remove-bound
                       (set::mergesort bind.tparams?.val)
                       atom-subst
                       array-subst)))
                  (and (atom/array-subst-no-capture-p
                        (set::mergesort bind.tparams?.val)
                        atom-subst
                        array-subst)
                       (var+type-list-subst-type-vars-no-capture-p
                        bind.params
                        atom-subst
                        array-subst)
                       (type-subst-type-vars-no-capture-p bind.type
                                                          atom-subst
                                                          array-subst)
                       (expr-subst-type-vars-no-capture-p bind.expr
                                                          atom-subst
                                                          array-subst)))
          :none (and (var+type-list-subst-type-vars-no-capture-p bind.params
                                                                 atom-subst
                                                                 array-subst)
                     (type-subst-type-vars-no-capture-p bind.type
                                                        atom-subst
                                                        array-subst)
                     (expr-subst-type-vars-no-capture-p bind.expr
                                                        atom-subst
                                                        array-subst)))))
  :name ast-subst-type-vars-no-capture-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-dim-vars
  :short "Substitute free dimension variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This only covers dimensions, which only contain dimension variables,
     because other ASTs contain both dimension and shape variables,
     and thus need two substitution maps."))
  :types (dims)
  :extra-args ((subst string-dim-mapp))
  :override
  ((dim :var (b* ((subst (string-dim-map-fix subst))
                  (var+dim (omap::assoc dim.name subst)))
               (if var+dim
                   (cdr var+dim)
                 (dim-var dim.name)))))
  :name ast-subst-dim-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-ispace-vars
  :short "Substitute free ispace variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be guarded by @(tsee ast-subst-ispace-vars-no-capture-p),
     but currently @(tsee fty::deffold-map) does not support such guards.
     One should call the @(tsee ast-subst-ispace-vars-no-capture-p) predicates
     prior to applying these substitution operations, for the time being."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp))
  :override
  ((shape :var (b* ((shape-subst (string-shape-map-fix shape-subst))
                    (var+shape (omap::assoc shape.name shape-subst)))
                 (if var+shape
                     (cdr var+shape)
                   (shape-var shape.name))))
   (shape :dim (shape-dim (dim-subst-dim-vars shape.dim dim-subst)))
   (shape :dims (shape-dims (dim-list-subst-dim-vars shape.dims dim-subst)))
   (ispace :dim (ispace-dim (dim-subst-dim-vars ispace.dim dim-subst)))
   (type :pi (b* (((mv dim-subst shape-subst)
                   (dim/shape-subst-remove-bound (set::mergesort type.params)
                                                 dim-subst
                                                 shape-subst)))
               (make-type-pi
                :params type.params
                :body (type-subst-ispace-vars type.body
                                              dim-subst
                                              shape-subst))))
   (type :sigma (b* (((mv dim-subst shape-subst)
                      (dim/shape-subst-remove-bound (set::mergesort type.params)
                                                    dim-subst
                                                    shape-subst)))
                  (make-type-sigma
                   :params type.params
                   :body (type-subst-ispace-vars type.body
                                                 dim-subst
                                                 shape-subst))))
   (expr :unbox
         (b* ((target (expr-subst-ispace-vars expr.target
                                              dim-subst
                                              shape-subst))
              ((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort expr.ispaces)
                                             dim-subst
                                             shape-subst)))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var expr.var
            :target target
            :body (expr-subst-ispace-vars expr.body
                                          dim-subst
                                          shape-subst))))
   (expr :let
         (b* ((binds (bind-list-subst-ispace-vars expr.binds
                                                  dim-subst
                                                  shape-subst))
              (bound-ispace-vars (bind-list-bound-ispace-vars expr.binds))
              ((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound bound-ispace-vars
                                             dim-subst
                                             shape-subst)))
           (make-expr-let
            :binds binds
            :body (expr-subst-ispace-vars expr.body
                                          dim-subst
                                          shape-subst))))
   (atom :ilambda
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort atom.params)
                                             dim-subst
                                             shape-subst)))
           (make-atom-ilambda
            :params atom.params
            :body (expr-subst-ispace-vars atom.body
                                          dim-subst
                                          shape-subst))))
   (bind :ifun
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort bind.params)
                                             dim-subst
                                             shape-subst)))
           (make-bind-ifun
            :var bind.var
            :params bind.params
            :type? (type-option-subst-ispace-vars bind.type?
                                                  dim-subst
                                                  shape-subst)
            :expr (expr-subst-ispace-vars bind.expr
                                          dim-subst
                                          shape-subst))))
   (bind :cfun
         (ispace-var-list-option-case
          bind.iparams?
          :some (b* (((mv dim-subst shape-subst)
                      (dim/shape-subst-remove-bound
                       (set::mergesort bind.iparams?.val)
                       dim-subst
                       shape-subst)))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? bind.iparams?
                   :params (var+type-list-subst-ispace-vars bind.params
                                                            dim-subst
                                                            shape-subst)
                   :type (type-subst-ispace-vars bind.type
                                                 dim-subst
                                                 shape-subst)
                   :expr (expr-subst-ispace-vars bind.expr
                                                 dim-subst
                                                 shape-subst)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type-list-subst-ispace-vars bind.params
                                                          dim-subst
                                                          shape-subst)
                 :type (type-subst-ispace-vars bind.type
                                               dim-subst
                                               shape-subst)
                 :expr (expr-subst-ispace-vars bind.expr
                                               dim-subst
                                               shape-subst)))))
  :name ast-subst-ispace-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-type-vars
  :short "Substitute free type variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be guarded by @(tsee ast-subst-type-vars-no-capture-p),
     but currently @(tsee fty::deffold-map) does not support such guards.
     One should call the @(tsee ast-subst-type-vars-no-capture-p) predicates
     prior to applying these substitution operations, for the time being."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((atom-subst string-type-mapp)
               (array-subst string-type-mapp))
  :override
  ((type :var
         (type-var-case
          type.var
          :atom (b* ((atom-subst (string-type-map-fix atom-subst))
                     (var+type (omap::assoc type.var.name atom-subst)))
                  (if var+type
                      (cdr var+type)
                    (type-var (type-var-atom type.var.name))))
          :array (b* ((array-subst (string-type-map-fix array-subst))
                      (var+type (omap::assoc type.var.name array-subst)))
                   (if var+type
                       (cdr var+type)
                     (type-var (type-var-array type.var.name))))))
   (type :forall
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort type.params)
                                              atom-subst
                                              array-subst)))
           (make-type-forall
            :params type.params
            :body (type-subst-type-vars type.body
                                        atom-subst
                                        array-subst))))
   (expr :let
         (b* ((binds (bind-list-subst-type-vars expr.binds
                                                atom-subst
                                                array-subst))
              (bound-type-vars (bind-list-bound-type-vars expr.binds))
              ((mv atom-subst array-subst)
               (atom/array-subst-remove-bound bound-type-vars
                                              atom-subst
                                              array-subst)))
           (make-expr-let
            :binds binds
            :body (expr-subst-type-vars expr.body
                                        atom-subst
                                        array-subst))))
   (atom :tlambda
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort atom.params)
                                              atom-subst
                                              array-subst)))
           (make-atom-tlambda
            :params atom.params
            :body (expr-subst-type-vars atom.body
                                        atom-subst
                                        array-subst))))
   (bind :tfun
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort bind.params)
                                              atom-subst
                                              array-subst)))
           (make-bind-tfun
            :var bind.var
            :params bind.params
            :type? (type-option-subst-type-vars bind.type?
                                                atom-subst
                                                array-subst)
            :expr (expr-subst-type-vars bind.expr
                                        atom-subst
                                        array-subst))))
   (bind :cfun
         (type-var-list-option-case
          bind.tparams?
          :some (b* (((mv atom-subst array-subst)
                      (atom/array-subst-remove-bound
                       (set::mergesort bind.tparams?.val)
                       atom-subst
                       array-subst)))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? bind.iparams?
                   :params (var+type-list-subst-type-vars bind.params
                                                          atom-subst
                                                          array-subst)
                   :type (type-subst-type-vars bind.type
                                               atom-subst
                                               array-subst)
                   :expr (expr-subst-type-vars bind.expr
                                               atom-subst
                                               array-subst)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type-list-subst-type-vars bind.params
                                                        atom-subst
                                                        array-subst)
                 :type (type-subst-type-vars bind.type
                                             atom-subst
                                             array-subst)
                 :expr (expr-subst-type-vars bind.expr
                                             atom-subst
                                             array-subst)))))
  :name ast-subst-type-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define renaming-no-capture-p ((names string-setp) (renam string-string-mapp))
  :returns (yes/no booleanp)
  :short "Check that a set of bound variable names is not captured
          by a renaming represented as a string-to-string map."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a renaming of ispace or type variables descends under a construct
     that binds the variables whose names are in @('names'),
     after those bound variables have been removed from the renaming,
     none of the bound names must occur among the values of the renaming,
     otherwise renaming under the binder would capture them.
     We check that @('names') is disjoint from the omap values
     of the renaming map.")
   (xdoc::p
    "This operates on a single namespace, i.e. a single renaming map.
     Since dimension and shape variables are in separate namespaces,
     as are atom-kind and array-kind type variables,
     the cases of
     @(tsee ast-rename-ispace-vars-no-capture-p) and
     @(tsee ast-rename-type-vars-no-capture-p)
     that bind variables call this once per namespace:
     once for the dimension and once for the shape renaming
     in the ispace case,
     and once for the atom-kind and once for the array-kind renaming
     in the type case.
     It would be incorrect to put the names of the two namespaces together
     and check them against both maps,
     because a name bound in one namespace cannot be captured
     by a renaming in the other namespace."))
  (set::emptyp (set::intersect (string-sfix names)
                               (omap::values (string-string-map-fix renam)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce rename-ispace-vars-no-capture-p
  :short "Check that renaming free ispace variables in ASTs
          does not result in variable capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renaming consists of two maps,
     one for dimension variables and one for shape variables,
     as in @(tsee ast-rename-ispace-vars).")
   (xdoc::p
    "At each ispace-binding construct,
     we remove the bound variables from the domain of the renaming
     (since they do not get renamed under the binder)
     and we check that those bound variables do not appear
     among the omap values of the resulting (restricted) renaming.
     We then recurse into the body of the binder
     with the restricted renaming.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the renaming
     are actually free in the body of each binder."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((dim-renam string-string-mapp)
               (shape-renam string-string-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :pi
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort type.params)))
              (dim-renam (omap::delete* bound-dim-vars
                                        (string-string-map-fix dim-renam)))
              (shape-renam (omap::delete* bound-shape-vars
                                          (string-string-map-fix shape-renam))))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (type-rename-ispace-vars-no-capture-p type.body
                                                      dim-renam
                                                      shape-renam))))
   (type :sigma
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort type.params)))
              (dim-renam (omap::delete* bound-dim-vars
                                        (string-string-map-fix dim-renam)))
              (shape-renam (omap::delete* bound-shape-vars
                                          (string-string-map-fix shape-renam))))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (type-rename-ispace-vars-no-capture-p type.body
                                                      dim-renam
                                                      shape-renam))))
   (expr :unbox
         (and (expr-rename-ispace-vars-no-capture-p expr.target
                                                    dim-renam
                                                    shape-renam)
              (b* (((mv bound-dim-vars bound-shape-vars)
                    (dim/shape-names-of-ispace-vars
                     (set::mergesort expr.ispaces)))
                   (dim-renam (omap::delete* bound-dim-vars
                                             (string-string-map-fix dim-renam)))
                   (shape-renam (omap::delete*
                                 bound-shape-vars
                                 (string-string-map-fix shape-renam))))
                (and (renaming-no-capture-p bound-dim-vars dim-renam)
                     (renaming-no-capture-p bound-shape-vars shape-renam)
                     (expr-rename-ispace-vars-no-capture-p expr.body
                                                           dim-renam
                                                           shape-renam)))))
   (expr :let
         (and (bind-list-rename-ispace-vars-no-capture-p expr.binds
                                                         dim-renam
                                                         shape-renam)
              (b* ((bound-ispace-vars (bind-list-bound-ispace-vars expr.binds))
                   ((mv bound-dim-vars bound-shape-vars)
                    (dim/shape-names-of-ispace-vars bound-ispace-vars))
                   (dim-renam (omap::delete* bound-dim-vars
                                             (string-string-map-fix dim-renam)))
                   (shape-renam (omap::delete*
                                 bound-shape-vars
                                 (string-string-map-fix shape-renam))))
                (and (renaming-no-capture-p bound-dim-vars dim-renam)
                     (renaming-no-capture-p bound-shape-vars shape-renam)
                     (expr-rename-ispace-vars-no-capture-p expr.body
                                                           dim-renam
                                                           shape-renam)))))
   (atom :ilambda
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort atom.params)))
              (dim-renam (omap::delete* bound-dim-vars
                                        (string-string-map-fix dim-renam)))
              (shape-renam (omap::delete* bound-shape-vars
                                          (string-string-map-fix shape-renam))))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (expr-rename-ispace-vars-no-capture-p atom.body
                                                      dim-renam
                                                      shape-renam))))
   (bind :ifun
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort bind.params)))
              (dim-renam (omap::delete* bound-dim-vars
                                        (string-string-map-fix dim-renam)))
              (shape-renam (omap::delete* bound-shape-vars
                                          (string-string-map-fix shape-renam))))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (type-option-rename-ispace-vars-no-capture-p bind.type?
                                                             dim-renam
                                                             shape-renam)
                (expr-rename-ispace-vars-no-capture-p bind.expr
                                                      dim-renam
                                                      shape-renam))))
   (bind :cfun
         (ispace-var-list-option-case
          bind.iparams?
          :some (b* (((mv bound-dim-vars bound-shape-vars)
                      (dim/shape-names-of-ispace-vars
                       (set::mergesort bind.iparams?.val)))
                     (dim-renam (omap::delete*
                                 bound-dim-vars
                                 (string-string-map-fix dim-renam)))
                     (shape-renam (omap::delete*
                                   bound-shape-vars
                                   (string-string-map-fix shape-renam))))
                  (and (renaming-no-capture-p bound-dim-vars dim-renam)
                       (renaming-no-capture-p bound-shape-vars shape-renam)
                       (var+type-list-rename-ispace-vars-no-capture-p
                        bind.params
                        dim-renam
                        shape-renam)
                       (type-rename-ispace-vars-no-capture-p bind.type
                                                             dim-renam
                                                             shape-renam)
                       (expr-rename-ispace-vars-no-capture-p bind.expr
                                                             dim-renam
                                                             shape-renam)))
          :none (and (var+type-list-rename-ispace-vars-no-capture-p
                      bind.params
                      dim-renam
                      shape-renam)
                     (type-rename-ispace-vars-no-capture-p bind.type
                                                           dim-renam
                                                           shape-renam)
                     (expr-rename-ispace-vars-no-capture-p bind.expr
                                                           dim-renam
                                                           shape-renam)))))
  :name ast-rename-ispace-vars-no-capture-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce rename-type-vars-no-capture-p
  :short "Check that renaming type variables in ASTs
          does not result in variable capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renaming consists of two maps,
     one for atom-kind type variables and one for array-kind type variables,
     as in @(tsee ast-rename-type-vars).")
   (xdoc::p
    "At each type-binding construct,
     we remove the bound variables from the domain of the renaming
     (since they do not get renamed under the binder)
     and we check that those bound parameters do not appear
     among the omap values of the resulting (restricted) renaming.
     We then recurse into the body of the binder
     with the restricted renaming.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the renaming
     are actually free in the body of each binder."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((atom-renam string-string-mapp)
               (array-renam string-string-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall
         (b* (((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars (set::mergesort type.params)))
              (atom-renam (omap::delete* bound-atom-vars
                                         (string-string-map-fix atom-renam)))
              (array-renam (omap::delete* bound-array-vars
                                          (string-string-map-fix array-renam))))
           (and (renaming-no-capture-p bound-atom-vars atom-renam)
                (renaming-no-capture-p bound-array-vars array-renam)
                (type-rename-type-vars-no-capture-p type.body
                                                    atom-renam
                                                    array-renam))))
   (expr :let
         (and (bind-list-rename-type-vars-no-capture-p expr.binds
                                                       atom-renam
                                                       array-renam)
              (b* ((bound-type-vars (bind-list-bound-type-vars expr.binds))
                   ((mv bound-atom-vars bound-array-vars)
                    (atom/array-names-of-type-vars bound-type-vars))
                   (atom-renam (omap::delete*
                                bound-atom-vars
                                (string-string-map-fix atom-renam)))
                   (array-renam (omap::delete*
                                 bound-array-vars
                                 (string-string-map-fix array-renam))))
                (and (renaming-no-capture-p bound-atom-vars atom-renam)
                     (renaming-no-capture-p bound-array-vars array-renam)
                     (expr-rename-type-vars-no-capture-p expr.body
                                                         atom-renam
                                                         array-renam)))))
   (atom :tlambda
         (b* (((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars (set::mergesort atom.params)))
              (atom-renam (omap::delete* bound-atom-vars
                                         (string-string-map-fix atom-renam)))
              (array-renam (omap::delete* bound-array-vars
                                          (string-string-map-fix array-renam))))
           (and (renaming-no-capture-p bound-atom-vars atom-renam)
                (renaming-no-capture-p bound-array-vars array-renam)
                (expr-rename-type-vars-no-capture-p atom.body
                                                    atom-renam
                                                    array-renam))))
   (bind :tfun
         (b* (((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars (set::mergesort bind.params)))
              (atom-renam (omap::delete* bound-atom-vars
                                         (string-string-map-fix atom-renam)))
              (array-renam (omap::delete* bound-array-vars
                                          (string-string-map-fix array-renam))))
           (and (renaming-no-capture-p bound-atom-vars atom-renam)
                (renaming-no-capture-p bound-array-vars array-renam)
                (type-option-rename-type-vars-no-capture-p bind.type?
                                                           atom-renam
                                                           array-renam)
                (expr-rename-type-vars-no-capture-p bind.expr
                                                    atom-renam
                                                    array-renam))))
   (bind :cfun
         (type-var-list-option-case
          bind.tparams?
          :some (b* (((mv bound-atom-vars bound-array-vars)
                      (atom/array-names-of-type-vars
                       (set::mergesort bind.tparams?.val)))
                     (atom-renam (omap::delete*
                                  bound-atom-vars
                                  (string-string-map-fix atom-renam)))
                     (array-renam (omap::delete*
                                   bound-array-vars
                                   (string-string-map-fix array-renam))))
                  (and (renaming-no-capture-p bound-atom-vars atom-renam)
                       (renaming-no-capture-p bound-array-vars array-renam)
                       (var+type-list-rename-type-vars-no-capture-p
                        bind.params
                        atom-renam
                        array-renam)
                       (type-rename-type-vars-no-capture-p bind.type
                                                           atom-renam
                                                           array-renam)
                       (expr-rename-type-vars-no-capture-p bind.expr
                                                           atom-renam
                                                           array-renam)))
          :none (and (var+type-list-rename-type-vars-no-capture-p
                      bind.params
                      atom-renam
                      array-renam)
                     (type-rename-type-vars-no-capture-p bind.type
                                                         atom-renam
                                                         array-renam)
                     (expr-rename-type-vars-no-capture-p bind.expr
                                                         atom-renam
                                                         array-renam)))))
  :name ast-rename-type-vars-no-capture-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-dim-vars
  :short "Rename dimension variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This only covers dimensions, which only contain dimension variables,
     because other ASTs contain both dimension and shape variables,
     and thus need two renaming maps."))
  :types (dims)
  :extra-args ((renam string-string-mapp))
  :override
  ((dim :var (b* ((renam (string-string-map-fix renam))
                  (var+name (omap::assoc dim.name renam)))
               (if var+name
                   (dim-var (cdr var+name))
                 (dim-var dim.name)))))
  :name ast-rename-dim-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-ispace-vars
  :short "Rename free ispace variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be guarded by @(tsee ast-rename-ispace-vars-no-capture-p),
     but currently @(tsee fty::deffold-map) does not support such guards.
     One should call the @(tsee ast-rename-ispace-vars-no-capture-p) predicates
     prior to applying these renaming operations, for the time being."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((dim-renam string-string-mapp)
               (shape-renam string-string-mapp))
  :override
  ((shape :var (b* ((shape-renam (string-string-map-fix shape-renam))
                    (var+name (omap::assoc shape.name shape-renam)))
                 (if var+name
                     (shape-var (cdr var+name))
                   (shape-var shape.name))))
   (shape :dim (shape-dim (dim-rename-dim-vars shape.dim dim-renam)))
   (shape :dims (shape-dims (dim-list-rename-dim-vars shape.dims dim-renam)))
   (ispace :dim (ispace-dim (dim-rename-dim-vars ispace.dim dim-renam)))
   (type :pi
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort type.params)))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-type-pi
            :params type.params
            :body (type-rename-ispace-vars type.body
                                           dim-renam
                                           shape-renam))))
   (type :sigma
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort type.params)))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-type-sigma
            :params type.params
            :body (type-rename-ispace-vars type.body
                                           dim-renam
                                           shape-renam))))
   (expr :unbox
         (b* ((target (expr-rename-ispace-vars expr.target
                                               dim-renam
                                               shape-renam))
              ((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort expr.ispaces)))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var expr.var
            :target target
            :body (expr-rename-ispace-vars expr.body
                                           dim-renam
                                           shape-renam))))
   (expr :let
         (b* ((binds (bind-list-rename-ispace-vars expr.binds
                                                   dim-renam
                                                   shape-renam))
              (bound-ispace-vars (bind-list-bound-ispace-vars expr.binds))
              ((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars bound-ispace-vars))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-expr-let
            :binds binds
            :body (expr-rename-ispace-vars expr.body
                                           dim-renam
                                           shape-renam))))
   (atom :ilambda
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort atom.params)))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-atom-ilambda
            :params atom.params
            :body (expr-rename-ispace-vars atom.body
                                           dim-renam
                                           shape-renam))))
   (bind :ifun
         (b* (((mv bound-dim-vars bound-shape-vars)
               (dim/shape-names-of-ispace-vars (set::mergesort bind.params)))
              (dim-renam
               (omap::delete* bound-dim-vars
                              (string-string-map-fix dim-renam)))
              (shape-renam
               (omap::delete* bound-shape-vars
                              (string-string-map-fix shape-renam))))
           (make-bind-ifun
            :var bind.var
            :params bind.params
            :type? (type-option-rename-ispace-vars bind.type?
                                                   dim-renam
                                                   shape-renam)
            :expr (expr-rename-ispace-vars bind.expr
                                           dim-renam
                                           shape-renam))))
   (bind :cfun
         (ispace-var-list-option-case
          bind.iparams?
          :some (b* (((mv bound-dim-vars bound-shape-vars)
                      (dim/shape-names-of-ispace-vars
                       (set::mergesort bind.iparams?.val)))
                     (dim-renam
                      (omap::delete* bound-dim-vars
                                     (string-string-map-fix dim-renam)))
                     (shape-renam
                      (omap::delete* bound-shape-vars
                                     (string-string-map-fix shape-renam))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? bind.iparams?
                   :params (var+type-list-rename-ispace-vars bind.params
                                                             dim-renam
                                                             shape-renam)
                   :type (type-rename-ispace-vars bind.type
                                                  dim-renam
                                                  shape-renam)
                   :expr (expr-rename-ispace-vars bind.expr
                                                  dim-renam
                                                  shape-renam)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type-list-rename-ispace-vars bind.params
                                                           dim-renam
                                                           shape-renam)
                 :type (type-rename-ispace-vars bind.type
                                                dim-renam
                                                shape-renam)
                 :expr (expr-rename-ispace-vars bind.expr
                                                dim-renam
                                                shape-renam)))))
  :name ast-rename-ispace-vars)

;;;;;;;;;;;;;;;;;;;;

(defsection types-count-of-rename-ispace-vars
  :short "Renaming ispace variables does not change the measure of types."

  (defret-mutual type-count-of-rename-ispace-vars
    (defret type-count-of-type-rename-ispace-vars
      (equal (type-count result)
             (type-count type))
      :fn type-rename-ispace-vars)
    (defret type-list-count-of-type-list-rename-ispace-vars
      (equal (type-list-count result)
             (type-list-count type-list))
      :fn type-list-rename-ispace-vars)
    :mutual-recursion types-rename-ispace-vars
    :hints (("Goal" :in-theory (enable type-rename-ispace-vars
                                       type-list-rename-ispace-vars
                                       type-count
                                       type-list-count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-type-vars
  :short "Rename free type variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be guarded by @(tsee ast-rename-type-vars-no-capture-p),
     but currently @(tsee fty::deffold-map) does not support such guards.
     One should call the @(tsee ast-rename-type-vars-no-capture-p) predicates
     prior to applying these renaming operations, for the time being."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :extra-args ((atom-renam string-string-mapp)
               (array-renam string-string-mapp))
  :override
  ((type :var
         (type-var-case
          type.var
          :atom (b* ((atom-renam (string-string-map-fix atom-renam))
                     (var+name (omap::assoc type.var.name atom-renam)))
                  (if var+name
                      (type-var (type-var-atom (cdr var+name)))
                    (type-var (type-var-atom type.var.name))))
          :array (b* ((array-renam (string-string-map-fix array-renam))
                      (var+name (omap::assoc type.var.name array-renam)))
                   (if var+name
                       (type-var (type-var-array (cdr var+name)))
                     (type-var (type-var-array type.var.name))))))
   (type :forall
         (b* (((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars (set::mergesort type.params)))
              (atom-renam
               (omap::delete* bound-atom-vars
                              (string-string-map-fix atom-renam)))
              (array-renam
               (omap::delete* bound-array-vars
                              (string-string-map-fix array-renam))))
           (make-type-forall
            :params type.params
            :body (type-rename-type-vars type.body
                                         atom-renam
                                         array-renam))))
   (expr :let
         (b* ((binds (bind-list-rename-type-vars expr.binds
                                                 atom-renam
                                                 array-renam))
              (bound-type-vars (bind-list-bound-type-vars expr.binds))
              ((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars bound-type-vars))
              (atom-renam
               (omap::delete* bound-atom-vars
                              (string-string-map-fix atom-renam)))
              (array-renam
               (omap::delete* bound-array-vars
                              (string-string-map-fix array-renam))))
           (make-expr-let
            :binds binds
            :body (expr-rename-type-vars expr.body
                                         atom-renam
                                         array-renam))))
   (atom :tlambda
         (b* (((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars (set::mergesort atom.params)))
              (atom-renam
               (omap::delete* bound-atom-vars
                              (string-string-map-fix atom-renam)))
              (array-renam
               (omap::delete* bound-array-vars
                              (string-string-map-fix array-renam))))
           (make-atom-tlambda
            :params atom.params
            :body (expr-rename-type-vars atom.body
                                         atom-renam
                                         array-renam))))
   (bind :tfun
         (b* (((mv bound-atom-vars bound-array-vars)
               (atom/array-names-of-type-vars (set::mergesort bind.params)))
              (atom-renam
               (omap::delete* bound-atom-vars
                              (string-string-map-fix atom-renam)))
              (array-renam
               (omap::delete* bound-array-vars
                              (string-string-map-fix array-renam))))
           (make-bind-tfun
            :var bind.var
            :params bind.params
            :type? (type-option-rename-type-vars bind.type?
                                                 atom-renam
                                                 array-renam)
            :expr (expr-rename-type-vars bind.expr
                                         atom-renam
                                         array-renam))))
   (bind :cfun
         (type-var-list-option-case
          bind.tparams?
          :some (b* (((mv bound-atom-vars bound-array-vars)
                      (atom/array-names-of-type-vars
                       (set::mergesort bind.tparams?.val)))
                     (atom-renam
                      (omap::delete* bound-atom-vars
                                     (string-string-map-fix atom-renam)))
                     (array-renam
                      (omap::delete* bound-array-vars
                                     (string-string-map-fix array-renam))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? bind.iparams?
                   :params (var+type-list-rename-type-vars bind.params
                                                           atom-renam
                                                           array-renam)
                   :type (type-rename-type-vars bind.type
                                                atom-renam
                                                array-renam)
                   :expr (expr-rename-type-vars bind.expr
                                                atom-renam
                                                array-renam)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type-list-rename-type-vars bind.params
                                                         atom-renam
                                                         array-renam)
                 :type (type-rename-type-vars bind.type
                                              atom-renam
                                              array-renam)
                 :expr (expr-rename-type-vars bind.expr
                                              atom-renam
                                              array-renam)))))
  :name ast-rename-type-vars)

;;;;;;;;;;;;;;;;;;;;

(defsection types-count-of-rename-type-vars
  :short "Renaming type variables does not change the measure of types."

  (defret-mutual type-count-of-rename-type-vars
    (defret type-count-of-type-rename-type-vars
      (equal (type-count result)
             (type-count type))
      :fn type-rename-type-vars)
    (defret type-list-count-of-type-list-rename-type-vars
      (equal (type-list-count result)
             (type-list-count type-list))
      :fn type-list-rename-type-vars)
    :mutual-recursion types-rename-type-vars
    :hints (("Goal" :in-theory (enable type-rename-type-vars
                                       type-list-rename-type-vars
                                       type-count
                                       type-list-count)))))
