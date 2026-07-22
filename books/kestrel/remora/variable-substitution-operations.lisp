; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "bound-and-free-variable-operations")

(include-book "kestrel/fty/deffold-map" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variable-substitution-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for substituting variables with other ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitutions are represented as maps
     from strings (variable names) to ASTs.
     Since ispaces have distinct dimension and shape variables,
     we use two separate maps for ispace variable substitutions,
     one for dimension variables and one for shape variables."))
  :order-subtopics t
  :default-parent t)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-subst-no-capture-p ((vars string-setp) (subst string-expr-mapp))
  :returns (yes/no booleanp)
  :short "Check that a set of bound expression variables is not captured
          by an expression substitution."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a substitution of expression variables descends under a construct
     that binds the expression variables in @('vars'),
     after those bound variables have been removed from the substitution,
     none of the bound variables must occur free
     among the values of the resulting substitution,
     otherwise substituting under the binder would capture them.
     We check that @('vars') is disjoint from the free expression variables
     of the substitution.")
   (xdoc::p
    "This is shared by the cases of @(tsee ast-subst-expr-vars-no-capture-p)
     for the constructs that bind expression variables."))
  (set::emptyp (set::intersect (string-sfix vars)
                               (string-expr-map-free-expr-vars subst))))

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
     and we check that those bound variables do not appear
     among the free ispace variables of the values
     of the resulting (restricted) substitution.
     We then recurse into the body of the binder
     with the restricted substitution.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     after checking the @(tsee car) of the list under the current substitution,
     we remove from the substitution the variables bound in the @(tsee car)
     (checking that they are not captured)
     before checking the @(tsee cdr) of the list.
     The body of a @('let') is then checked with
     all the variables bound in the bindings removed from the substitution.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the substitution
     are actually free in the body of each binder."))
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :pi
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::insert type.param nil)
                                             dim-subst
                                             shape-subst)))
           (and (dim/shape-subst-no-capture-p (set::insert type.param nil)
                                              dim-subst
                                              shape-subst)
                (type-subst-ispace-vars-no-capture-p type.body
                                                     dim-subst
                                                     shape-subst))))
   (type :pin
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
               (dim/shape-subst-remove-bound (set::insert atom.param nil)
                                             dim-subst
                                             shape-subst)))
           (and (dim/shape-subst-no-capture-p (set::insert atom.param nil)
                                              dim-subst
                                              shape-subst)
                (expr-subst-ispace-vars-no-capture-p atom.body
                                                     dim-subst
                                                     shape-subst))))
   (atom :ilambdan
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
                       (var+type?-list-subst-ispace-vars-no-capture-p
                        bind.params
                        dim-subst
                        shape-subst)
                       (type-subst-ispace-vars-no-capture-p bind.type
                                                            dim-subst
                                                            shape-subst)
                       (expr-subst-ispace-vars-no-capture-p bind.expr
                                                            dim-subst
                                                            shape-subst)))
          :none (and (var+type?-list-subst-ispace-vars-no-capture-p bind.params
                                                                    dim-subst
                                                                    shape-subst)
                     (type-subst-ispace-vars-no-capture-p bind.type
                                                          dim-subst
                                                          shape-subst)
                     (expr-subst-ispace-vars-no-capture-p bind.expr
                                                          dim-subst
                                                          shape-subst))))
   (bind-list
    (b* (((when (endp bind-list)) t)
         (bind (car bind-list)))
      (and (bind-subst-ispace-vars-no-capture-p bind dim-subst shape-subst)
           (b* ((bound (bind-bound-ispace-vars bind))
                ((mv dim-subst shape-subst)
                 (dim/shape-subst-remove-bound bound dim-subst shape-subst)))
             (and (dim/shape-subst-no-capture-p bound dim-subst shape-subst)
                  (bind-list-subst-ispace-vars-no-capture-p (cdr bind-list)
                                                            dim-subst
                                                            shape-subst)))))))
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
     and we check that those bound variables do not appear
     among the free type variables of the values
     of the resulting (restricted) substitution.
     We then recurse into the body of the binder
     with the restricted substitution.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     after checking the @(tsee car) of the list under the current substitution,
     we remove from the substitution the variables bound in the @(tsee car)
     (checking that they are not captured)
     before checking the @(tsee cdr) of the list.
     The body of a @('let') is then checked with
     all the variables bound in the bindings removed from the substitution.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the substitution
     are actually free in the body of each binder."))
  :types (types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((atom-subst string-type-mapp)
               (array-subst string-type-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::insert type.param nil)
                                              atom-subst
                                              array-subst)))
           (and (atom/array-subst-no-capture-p (set::insert type.param nil)
                                               atom-subst
                                               array-subst)
                (type-subst-type-vars-no-capture-p type.body
                                                   atom-subst
                                                   array-subst))))
   (type :foralln
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
               (atom/array-subst-remove-bound (set::insert atom.param nil)
                                              atom-subst
                                              array-subst)))
           (and (atom/array-subst-no-capture-p (set::insert atom.param nil)
                                               atom-subst
                                               array-subst)
                (expr-subst-type-vars-no-capture-p atom.body
                                                   atom-subst
                                                   array-subst))))
   (atom :tlambdan
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
                       (var+type?-list-subst-type-vars-no-capture-p
                        bind.params
                        atom-subst
                        array-subst)
                       (type-subst-type-vars-no-capture-p bind.type
                                                          atom-subst
                                                          array-subst)
                       (expr-subst-type-vars-no-capture-p bind.expr
                                                          atom-subst
                                                          array-subst)))
          :none (and (var+type?-list-subst-type-vars-no-capture-p bind.params
                                                                  atom-subst
                                                                  array-subst)
                     (type-subst-type-vars-no-capture-p bind.type
                                                        atom-subst
                                                        array-subst)
                     (expr-subst-type-vars-no-capture-p bind.expr
                                                        atom-subst
                                                        array-subst))))
   (bind-list
    (b* (((when (endp bind-list)) t)
         (bind (car bind-list)))
      (and (bind-subst-type-vars-no-capture-p bind atom-subst array-subst)
           (b* ((bound (bind-bound-type-vars bind))
                ((mv atom-subst array-subst)
                 (atom/array-subst-remove-bound bound atom-subst array-subst)))
             (and (atom/array-subst-no-capture-p bound atom-subst array-subst)
                  (bind-list-subst-type-vars-no-capture-p (cdr bind-list)
                                                          atom-subst
                                                          array-subst)))))))
  :name ast-subst-type-vars-no-capture-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce subst-expr-vars-no-capture-p
  :short "Check that substituting expression variables in ASTs
          does not result in variable capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitution consists of one map,
     as in @(tsee ast-subst-expr-vars).")
   (xdoc::p
    "At each expression-binding construct,
     we remove the bound variables from the domain of the substitution
     (since they do not get substituted under the binder)
     and we check that those bound variables do not appear
     among the free expression variables of the values
     of the resulting (restricted) substitution.
     We then recurse into the body of the binder
     with the restricted substitution.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     after checking the @(tsee car) of the list under the current substitution,
     we remove from the substitution the variables bound in the @(tsee car)
     (checking that they are not captured)
     before checking the @(tsee cdr) of the list.
     The body of a @('let') is then checked with
     all the variables bound in the bindings removed from the substitution.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the substitution
     are actually free in the body of each binder."))
  :types (exprs/atoms/binds)
  :extra-args ((subst string-expr-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((expr :unbox
         (and (expr-subst-expr-vars-no-capture-p expr.target subst)
              (b* ((subst (omap::delete expr.var (string-expr-map-fix subst))))
                (and (expr-subst-no-capture-p (set::insert expr.var nil) subst)
                     (expr-subst-expr-vars-no-capture-p expr.body subst)))))
   (expr :let
         (and (bind-list-subst-expr-vars-no-capture-p expr.binds subst)
              (b* ((bound (bind-list-bound-expr-vars expr.binds))
                   (subst (omap::delete* bound (string-expr-map-fix subst))))
                (and (expr-subst-no-capture-p bound subst)
                     (expr-subst-expr-vars-no-capture-p expr.body subst)))))
   (atom :lambda
         (b* ((bound (set::insert (var+type?->var atom.param) nil))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (and (expr-subst-no-capture-p bound subst)
                (expr-subst-expr-vars-no-capture-p atom.body subst))))
   (atom :lambdan
         (b* ((bound (set::mergesort (var+type?-list->var atom.params)))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (and (expr-subst-no-capture-p bound subst)
                (expr-subst-expr-vars-no-capture-p atom.body subst))))
   (bind :fun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (and (expr-subst-no-capture-p bound subst)
                (expr-subst-expr-vars-no-capture-p bind.expr subst))))
   (bind :cfun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (and (expr-subst-no-capture-p bound subst)
                (expr-subst-expr-vars-no-capture-p bind.expr subst))))
   (bind-list
    (b* (((when (endp bind-list)) t)
         (bind (car bind-list)))
      (and (bind-subst-expr-vars-no-capture-p bind subst)
           (b* ((bound (bind-bound-expr-vars bind))
                (subst (omap::delete* bound (string-expr-map-fix subst))))
             (and (expr-subst-no-capture-p bound subst)
                  (bind-list-subst-expr-vars-no-capture-p (cdr bind-list)
                                                          subst)))))))
  :name ast-subst-expr-vars-no-capture-p)

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
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp))
  :override
  ((shape :var (b* ((shape-subst (string-shape-map-fix shape-subst))
                    (var+shape (omap::assoc shape.name shape-subst)))
                 (if var+shape
                     (cdr var+shape)
                   (shape-var shape.name))))
   (shape :dims (shape-dims (dim-list-subst-dim-vars shape.dims dim-subst)))
   (ispace :dim (ispace-dim (dim-subst-dim-vars ispace.dim dim-subst)))
   (type :pi (b* (((mv dim-subst shape-subst)
                   (dim/shape-subst-remove-bound (set::insert type.param nil)
                                                 dim-subst
                                                 shape-subst)))
               (make-type-pi
                :param type.param
                :body (type-subst-ispace-vars type.body
                                              dim-subst
                                              shape-subst))))
   (type :pin (b* (((mv dim-subst shape-subst)
                   (dim/shape-subst-remove-bound (set::mergesort type.params)
                                                 dim-subst
                                                 shape-subst)))
               (make-type-pin
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
              ;; The result type is outside the scope of the unboxed ispaces,
              ;; so we substitute it under the original (unreduced) maps.
              (type? (type-option-subst-ispace-vars expr.type?
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
                                          shape-subst)
            :type? type?)))
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
               (dim/shape-subst-remove-bound (set::insert atom.param nil)
                                             dim-subst
                                             shape-subst)))
           (make-atom-ilambda
            :param atom.param
            :body (expr-subst-ispace-vars atom.body
                                          dim-subst
                                          shape-subst))))
   (atom :ilambdan
         (b* (((mv dim-subst shape-subst)
               (dim/shape-subst-remove-bound (set::mergesort atom.params)
                                             dim-subst
                                             shape-subst)))
           (make-atom-ilambdan
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
                   :params (var+type?-list-subst-ispace-vars bind.params
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
                 :params (var+type?-list-subst-ispace-vars bind.params
                                                           dim-subst
                                                           shape-subst)
                 :type (type-subst-ispace-vars bind.type
                                               dim-subst
                                               shape-subst)
                 :expr (expr-subst-ispace-vars bind.expr
                                               dim-subst
                                               shape-subst))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-subst-ispace-vars bind dim-subst shape-subst))
         ((mv dim-subst shape-subst)
          (dim/shape-subst-remove-bound (bind-bound-ispace-vars bind)
                                        dim-subst
                                        shape-subst)))
      (cons new-bind
            (bind-list-subst-ispace-vars (cdr bind-list)
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
          var+type?
          var+type?-list
          exprs/atoms/binds)
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
               (atom/array-subst-remove-bound (set::insert type.param nil)
                                              atom-subst
                                              array-subst)))
           (make-type-forall
            :param type.param
            :body (type-subst-type-vars type.body
                                        atom-subst
                                        array-subst))))
   (type :foralln
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort type.params)
                                              atom-subst
                                              array-subst)))
           (make-type-foralln
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
               (atom/array-subst-remove-bound (set::insert atom.param nil)
                                              atom-subst
                                              array-subst)))
           (make-atom-tlambda
            :param atom.param
            :body (expr-subst-type-vars atom.body
                                        atom-subst
                                        array-subst))))
   (atom :tlambdan
         (b* (((mv atom-subst array-subst)
               (atom/array-subst-remove-bound (set::mergesort atom.params)
                                              atom-subst
                                              array-subst)))
           (make-atom-tlambdan
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
                   :params (var+type?-list-subst-type-vars bind.params
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
                 :params (var+type?-list-subst-type-vars bind.params
                                                         atom-subst
                                                         array-subst)
                 :type (type-subst-type-vars bind.type
                                             atom-subst
                                             array-subst)
                 :expr (expr-subst-type-vars bind.expr
                                             atom-subst
                                             array-subst))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-subst-type-vars bind atom-subst array-subst))
         ((mv atom-subst array-subst)
          (atom/array-subst-remove-bound (bind-bound-type-vars bind)
                                         atom-subst
                                         array-subst)))
      (cons new-bind
            (bind-list-subst-type-vars (cdr bind-list)
                                       atom-subst
                                       array-subst)))))
  :name ast-subst-type-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-expr-vars
  :short "Substitute free expression variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be guarded by @(tsee ast-subst-expr-vars-no-capture-p),
     but currently @(tsee fty::deffold-map) does not support such guards.
     One should call the @(tsee ast-subst-expr-vars-no-capture-p) predicates
     prior to applying these substitution operations, for the time being."))
  :types (exprs/atoms/binds)
  :extra-args ((subst string-expr-mapp))
  :override
  ((expr :var (b* ((subst (string-expr-map-fix subst))
                   (var+expr (omap::assoc expr.name subst)))
                (if var+expr
                    (cdr var+expr)
                  (expr-var expr.name))))
   (expr :unbox
         (b* ((target (expr-subst-expr-vars expr.target subst))
              (subst (omap::delete expr.var (string-expr-map-fix subst))))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var expr.var
            :target target
            :body (expr-subst-expr-vars expr.body subst)
            ;; the result type has no expression variables, so we carry it
            :type? expr.type?)))
   (expr :let
         (b* ((binds (bind-list-subst-expr-vars expr.binds subst))
              (bound (bind-list-bound-expr-vars expr.binds))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (make-expr-let
            :binds binds
            :body (expr-subst-expr-vars expr.body subst))))
   (atom :lambda
         (b* ((bound (set::insert (var+type?->var atom.param) nil))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (make-atom-lambda
            :param atom.param
            :body (expr-subst-expr-vars atom.body subst)
            :type? atom.type?)))
   (atom :lambdan
         (b* ((bound (set::mergesort (var+type?-list->var atom.params)))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (make-atom-lambdan
            :params atom.params
            :body (expr-subst-expr-vars atom.body subst)
            :type? atom.type?)))
   (bind :fun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (make-bind-fun
            :var bind.var
            :params bind.params
            :type? bind.type?
            :expr (expr-subst-expr-vars bind.expr subst))))
   (bind :cfun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (subst (omap::delete* bound (string-expr-map-fix subst))))
           (make-bind-cfun
            :var bind.var
            :tparams? bind.tparams?
            :iparams? bind.iparams?
            :params bind.params
            :type bind.type
            :expr (expr-subst-expr-vars bind.expr subst))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-subst-expr-vars bind subst))
         (bound (bind-bound-expr-vars bind))
         (subst (omap::delete* bound (string-expr-map-fix subst))))
      (cons new-bind
            (bind-list-subst-expr-vars (cdr bind-list) subst)))))
  :name ast-subst-expr-vars)
