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

(defxdoc+ variable-renaming-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for renaming variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renamings are represented as maps from strings to strings."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-rename-remove-bound ((vars ispace-var-setp)
                                       (dim-renam string-string-mapp)
                                       (shape-renam string-string-mapp))
  :returns (mv (bound-dim-vars string-setp)
               (bound-shape-vars string-setp)
               (new-dim-renam string-string-mapp)
               (new-shape-renam string-string-mapp))
  :short "Remove a set of bound ispace variables from
          a dimension renaming and a shape renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a renaming of ispace variables descends under a construct
     that binds the ispace variables in @('vars'),
     those bound variables must not be renamed under the binder.
     Accordingly, we remove them from the domains of the renaming maps:
     the dimension variables in @('vars')
     are removed from the dimension renaming,
     and the shape variables in @('vars')
     are removed from the shape renaming.
     We use @(tsee dim/shape-names-of-ispace-vars)
     to split @('vars') into its dimension and shape variable names,
     which we also return,
     since the capture check is performed one namespace at a time
     (via @(tsee renaming-no-capture-p)) and thus needs them separately.")
   (xdoc::p
    "This is shared by
     the operations that rename ispace variables in ASTs and
     the ones that check the absence of variable capture by such renamings.
     Only the latter uses the returned variable names."))
  (b* (((mv bound-dim-vars bound-shape-vars)
        (dim/shape-names-of-ispace-vars vars)))
    (mv bound-dim-vars
        bound-shape-vars
        (omap::delete* bound-dim-vars (string-string-map-fix dim-renam))
        (omap::delete* bound-shape-vars (string-string-map-fix shape-renam))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-rename-remove-bound ((vars type-var-setp)
                                        (atom-renam string-string-mapp)
                                        (array-renam string-string-mapp))
  :returns (mv (bound-atom-vars string-setp)
               (bound-array-vars string-setp)
               (new-atom-renam string-string-mapp)
               (new-array-renam string-string-mapp))
  :short "Remove a set of bound type variables from
          an atom-kind and an array-kind type renaming."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a renaming of type variables descends under a construct
     that binds the type variables in @('vars'),
     those bound variables must not be renamed under the binder.
     Accordingly, we remove them from the domains of the renaming maps:
     the atom-kind type variables in @('vars')
     are removed from the atom-kind type renaming,
     and the array-kind type variables in @('vars')
     are removed from the array-kind type renaming.
     We use @(tsee atom/array-names-of-type-vars)
     to split @('vars') into its atom-kind and array-kind type variable names,
     which we also return,
     since the capture check is performed one namespace at a time
     (via @(tsee renaming-no-capture-p)) and thus needs them separately.")
   (xdoc::p
    "This is shared by
     the operations that rename type variables in ASTs and
     the ones that check the absence of variable capture by such renamings.
     Only the latter uses the returned variable names."))
  (b* (((mv bound-atom-vars bound-array-vars)
        (atom/array-names-of-type-vars vars)))
    (mv bound-atom-vars
        bound-array-vars
        (omap::delete* bound-atom-vars (string-string-map-fix atom-renam))
        (omap::delete* bound-array-vars (string-string-map-fix array-renam))))
  :verify-guards :after-returns)

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
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     after checking the @(tsee car) of the list under the current renaming,
     we remove from the renaming the variables bound in the @(tsee car)
     (checking that they are not captured)
     before checking the @(tsee cdr) of the list.
     The body of a @('let') is then checked with
     all the variables bound in the bindings removed from the renaming.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the renaming
     are actually free in the body of each binder."))
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-renam string-string-mapp)
               (shape-renam string-string-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :pi
         (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort type.params)
                                              dim-renam
                                              shape-renam)))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (type-rename-ispace-vars-no-capture-p type.body
                                                      dim-renam
                                                      shape-renam))))
   (type :sigma
         (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort type.params)
                                              dim-renam
                                              shape-renam)))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (type-rename-ispace-vars-no-capture-p type.body
                                                      dim-renam
                                                      shape-renam))))
   (expr :unbox
         (and (expr-rename-ispace-vars-no-capture-p expr.target
                                                    dim-renam
                                                    shape-renam)
              (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
                    (dim/shape-rename-remove-bound (set::mergesort expr.ispaces)
                                                   dim-renam
                                                   shape-renam)))
                (and (renaming-no-capture-p bound-dim-vars dim-renam)
                     (renaming-no-capture-p bound-shape-vars shape-renam)
                     (expr-rename-ispace-vars-no-capture-p expr.body
                                                           dim-renam
                                                           shape-renam)))))
   (expr :let
         (and (bind-list-rename-ispace-vars-no-capture-p expr.binds
                                                         dim-renam
                                                         shape-renam)
              (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
                    (dim/shape-rename-remove-bound
                     (bind-list-bound-ispace-vars expr.binds)
                     dim-renam
                     shape-renam)))
                (and (renaming-no-capture-p bound-dim-vars dim-renam)
                     (renaming-no-capture-p bound-shape-vars shape-renam)
                     (expr-rename-ispace-vars-no-capture-p expr.body
                                                           dim-renam
                                                           shape-renam)))))
   (atom :ilambda
         (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::insert atom.param nil)
                                              dim-renam
                                              shape-renam)))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (expr-rename-ispace-vars-no-capture-p atom.body
                                                      dim-renam
                                                      shape-renam))))
   (atom :ilambdan
         (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort atom.params)
                                              dim-renam
                                              shape-renam)))
           (and (renaming-no-capture-p bound-dim-vars dim-renam)
                (renaming-no-capture-p bound-shape-vars shape-renam)
                (expr-rename-ispace-vars-no-capture-p atom.body
                                                      dim-renam
                                                      shape-renam))))
   (bind :ifun
         (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort bind.params)
                                              dim-renam
                                              shape-renam)))
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
          :some (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
                      (dim/shape-rename-remove-bound
                       (set::mergesort bind.iparams?.val)
                       dim-renam
                       shape-renam)))
                  (and (renaming-no-capture-p bound-dim-vars dim-renam)
                       (renaming-no-capture-p bound-shape-vars shape-renam)
                       (var+type?-list-rename-ispace-vars-no-capture-p
                        bind.params
                        dim-renam
                        shape-renam)
                       (type-rename-ispace-vars-no-capture-p bind.type
                                                             dim-renam
                                                             shape-renam)
                       (expr-rename-ispace-vars-no-capture-p bind.expr
                                                             dim-renam
                                                             shape-renam)))
          :none (and (var+type?-list-rename-ispace-vars-no-capture-p
                      bind.params
                      dim-renam
                      shape-renam)
                     (type-rename-ispace-vars-no-capture-p bind.type
                                                           dim-renam
                                                           shape-renam)
                     (expr-rename-ispace-vars-no-capture-p bind.expr
                                                           dim-renam
                                                           shape-renam))))
   (bind-list
    (b* (((when (endp bind-list)) t)
         (bind (car bind-list)))
      (and (bind-rename-ispace-vars-no-capture-p bind dim-renam shape-renam)
           (b* (((mv bound-dim-vars bound-shape-vars dim-renam shape-renam)
                 (dim/shape-rename-remove-bound (bind-bound-ispace-vars bind)
                                                dim-renam
                                                shape-renam)))
             (and (renaming-no-capture-p bound-dim-vars dim-renam)
                  (renaming-no-capture-p bound-shape-vars shape-renam)
                  (bind-list-rename-ispace-vars-no-capture-p (cdr bind-list)
                                                             dim-renam
                                                             shape-renam)))))))
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
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     after checking the @(tsee car) of the list under the current renaming,
     we remove from the renaming the variables bound in the @(tsee car)
     (checking that they are not captured)
     before checking the @(tsee cdr) of the list.
     The body of a @('let') is then checked with
     all the variables bound in the bindings removed from the renaming.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the renaming
     are actually free in the body of each binder."))
  :types (types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((atom-renam string-string-mapp)
               (array-renam string-string-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall
         (b* (((mv bound-atom-vars bound-array-vars atom-renam array-renam)
               (atom/array-rename-remove-bound (set::mergesort type.params)
                                               atom-renam
                                               array-renam)))
           (and (renaming-no-capture-p bound-atom-vars atom-renam)
                (renaming-no-capture-p bound-array-vars array-renam)
                (type-rename-type-vars-no-capture-p type.body
                                                    atom-renam
                                                    array-renam))))
   (expr :let
         (and (bind-list-rename-type-vars-no-capture-p expr.binds
                                                       atom-renam
                                                       array-renam)
              (b* (((mv bound-atom-vars bound-array-vars atom-renam array-renam)
                    (atom/array-rename-remove-bound
                     (bind-list-bound-type-vars expr.binds)
                     atom-renam
                     array-renam)))
                (and (renaming-no-capture-p bound-atom-vars atom-renam)
                     (renaming-no-capture-p bound-array-vars array-renam)
                     (expr-rename-type-vars-no-capture-p expr.body
                                                         atom-renam
                                                         array-renam)))))
   (atom :tlambda
         (b* (((mv bound-atom-vars bound-array-vars atom-renam array-renam)
               (atom/array-rename-remove-bound (set::mergesort atom.params)
                                               atom-renam
                                               array-renam)))
           (and (renaming-no-capture-p bound-atom-vars atom-renam)
                (renaming-no-capture-p bound-array-vars array-renam)
                (expr-rename-type-vars-no-capture-p atom.body
                                                    atom-renam
                                                    array-renam))))
   (bind :tfun
         (b* (((mv bound-atom-vars bound-array-vars atom-renam array-renam)
               (atom/array-rename-remove-bound (set::mergesort bind.params)
                                               atom-renam
                                               array-renam)))
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
          :some (b* (((mv bound-atom-vars bound-array-vars
                          atom-renam array-renam)
                      (atom/array-rename-remove-bound
                       (set::mergesort bind.tparams?.val)
                       atom-renam
                       array-renam)))
                  (and (renaming-no-capture-p bound-atom-vars atom-renam)
                       (renaming-no-capture-p bound-array-vars array-renam)
                       (var+type?-list-rename-type-vars-no-capture-p
                        bind.params
                        atom-renam
                        array-renam)
                       (type-rename-type-vars-no-capture-p bind.type
                                                           atom-renam
                                                           array-renam)
                       (expr-rename-type-vars-no-capture-p bind.expr
                                                           atom-renam
                                                           array-renam)))
          :none (and (var+type?-list-rename-type-vars-no-capture-p
                      bind.params
                      atom-renam
                      array-renam)
                     (type-rename-type-vars-no-capture-p bind.type
                                                         atom-renam
                                                         array-renam)
                     (expr-rename-type-vars-no-capture-p bind.expr
                                                         atom-renam
                                                         array-renam))))
   (bind-list
    (b* (((when (endp bind-list)) t)
         (bind (car bind-list)))
      (and (bind-rename-type-vars-no-capture-p bind atom-renam array-renam)
           (b* (((mv bound-atom-vars bound-array-vars atom-renam array-renam)
                 (atom/array-rename-remove-bound (bind-bound-type-vars bind)
                                                 atom-renam
                                                 array-renam)))
             (and (renaming-no-capture-p bound-atom-vars atom-renam)
                  (renaming-no-capture-p bound-array-vars array-renam)
                  (bind-list-rename-type-vars-no-capture-p (cdr bind-list)
                                                           atom-renam
                                                           array-renam)))))))
  :name ast-rename-type-vars-no-capture-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce rename-expr-vars-no-capture-p
  :short "Check that renaming expression variables in ASTs
          does not result in variable capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renaming consists of one map,
     as in @(tsee ast-rename-expr-vars).")
   (xdoc::p
    "At each expression-binding construct,
     we remove the bound variables from the domain of the renaming
     (since they do not get renamed under the binder)
     and we check that those bound variables do not appear
     among the omap values of the resulting (restricted) renaming.
     We then recurse into the body of the binder
     with the restricted renaming.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     after checking the @(tsee car) of the list under the current renaming,
     we remove from the renaming the variables bound in the @(tsee car)
     (checking that they are not captured)
     before checking the @(tsee cdr) of the list.
     The body of a @('let') is then checked with
     all the variables bound in the bindings removed from the renaming.")
   (xdoc::p
    "This is a conservative check:
     it does not depend on which keys of the renaming
     are actually free in the body of each binder."))
  :types (exprs/atoms/binds)
  :extra-args ((renam string-string-mapp))
  :result booleanp
  :default t
  :combine and
  :override
  ((expr :unbox
         (and (expr-rename-expr-vars-no-capture-p expr.target renam)
              (b* ((renam
                    (omap::delete expr.var (string-string-map-fix renam))))
                (and (renaming-no-capture-p (set::insert expr.var nil) renam)
                     (expr-rename-expr-vars-no-capture-p expr.body renam)))))
   (expr :let
         (and (bind-list-rename-expr-vars-no-capture-p expr.binds renam)
              (b* ((bound (bind-list-bound-expr-vars expr.binds))
                   (renam (omap::delete* bound (string-string-map-fix renam))))
                (and (renaming-no-capture-p bound renam)
                     (expr-rename-expr-vars-no-capture-p expr.body renam)))))
   (atom :lambda
         (b* ((bound (set::mergesort (var+type?-list->var atom.params)))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (and (renaming-no-capture-p bound renam)
                (expr-rename-expr-vars-no-capture-p atom.body renam))))
   (bind :fun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (and (renaming-no-capture-p bound renam)
                (expr-rename-expr-vars-no-capture-p bind.expr renam))))
   (bind :cfun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (and (renaming-no-capture-p bound renam)
                (expr-rename-expr-vars-no-capture-p bind.expr renam))))
   (bind-list
    (b* (((when (endp bind-list)) t)
         (bind (car bind-list)))
      (and (bind-rename-expr-vars-no-capture-p bind renam)
           (b* ((bound (bind-bound-expr-vars bind))
                (renam (omap::delete* bound (string-string-map-fix renam))))
             (and (renaming-no-capture-p bound renam)
                  (bind-list-rename-expr-vars-no-capture-p (cdr bind-list)
                                                           renam)))))))
  :name ast-rename-expr-vars-no-capture-p)

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
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-renam string-string-mapp)
               (shape-renam string-string-mapp))
  :override
  ((shape :var (b* ((shape-renam (string-string-map-fix shape-renam))
                    (var+name (omap::assoc shape.name shape-renam)))
                 (if var+name
                     (shape-var (cdr var+name))
                   (shape-var shape.name))))
   (shape :dims (shape-dims (dim-list-rename-dim-vars shape.dims dim-renam)))
   (ispace :dim (ispace-dim (dim-rename-dim-vars ispace.dim dim-renam)))
   (type :pi
         (b* (((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort type.params)
                                              dim-renam
                                              shape-renam)))
           (make-type-pi
            :params type.params
            :body (type-rename-ispace-vars type.body
                                           dim-renam
                                           shape-renam))))
   (type :sigma
         (b* (((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort type.params)
                                              dim-renam
                                              shape-renam)))
           (make-type-sigma
            :params type.params
            :body (type-rename-ispace-vars type.body
                                           dim-renam
                                           shape-renam))))
   (expr :unbox
         (b* ((target (expr-rename-ispace-vars expr.target
                                               dim-renam
                                               shape-renam))
              ;; The result type is outside the scope of the unboxed ispaces,
              ;; so we rename it under the original (unreduced) maps.
              (type? (type-option-rename-ispace-vars expr.type?
                                                     dim-renam
                                                     shape-renam))
              ((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort expr.ispaces)
                                              dim-renam
                                              shape-renam)))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var expr.var
            :target target
            :body (expr-rename-ispace-vars expr.body
                                           dim-renam
                                           shape-renam)
            :type? type?)))
   (expr :let
         (b* ((binds (bind-list-rename-ispace-vars expr.binds
                                                   dim-renam
                                                   shape-renam))
              ((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound
                (bind-list-bound-ispace-vars expr.binds)
                dim-renam
                shape-renam)))
           (make-expr-let
            :binds binds
            :body (expr-rename-ispace-vars expr.body
                                           dim-renam
                                           shape-renam))))
   (atom :ilambda
         (b* (((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::insert atom.param nil)
                                              dim-renam
                                              shape-renam)))
           (make-atom-ilambda
            :param atom.param
            :body (expr-rename-ispace-vars atom.body
                                           dim-renam
                                           shape-renam))))
   (atom :ilambdan
         (b* (((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort atom.params)
                                              dim-renam
                                              shape-renam)))
           (make-atom-ilambdan
            :params atom.params
            :body (expr-rename-ispace-vars atom.body
                                           dim-renam
                                           shape-renam))))
   (bind :ifun
         (b* (((mv & & dim-renam shape-renam)
               (dim/shape-rename-remove-bound (set::mergesort bind.params)
                                              dim-renam
                                              shape-renam)))
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
          :some (b* (((mv & & dim-renam shape-renam)
                      (dim/shape-rename-remove-bound
                       (set::mergesort bind.iparams?.val)
                       dim-renam
                       shape-renam)))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? bind.iparams?
                   :params (var+type?-list-rename-ispace-vars bind.params
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
                 :params (var+type?-list-rename-ispace-vars bind.params
                                                            dim-renam
                                                            shape-renam)
                 :type (type-rename-ispace-vars bind.type
                                                dim-renam
                                                shape-renam)
                 :expr (expr-rename-ispace-vars bind.expr
                                                dim-renam
                                                shape-renam))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-rename-ispace-vars bind dim-renam shape-renam))
         ((mv & & dim-renam shape-renam)
          (dim/shape-rename-remove-bound (bind-bound-ispace-vars bind)
                                         dim-renam
                                         shape-renam)))
      (cons new-bind
            (bind-list-rename-ispace-vars (cdr bind-list)
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
          var+type?
          var+type?-list
          exprs/atoms/binds)
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
         (b* (((mv & & atom-renam array-renam)
               (atom/array-rename-remove-bound (set::mergesort type.params)
                                               atom-renam
                                               array-renam)))
           (make-type-forall
            :params type.params
            :body (type-rename-type-vars type.body
                                         atom-renam
                                         array-renam))))
   (expr :let
         (b* ((binds (bind-list-rename-type-vars expr.binds
                                                 atom-renam
                                                 array-renam))
              ((mv & & atom-renam array-renam)
               (atom/array-rename-remove-bound
                (bind-list-bound-type-vars expr.binds)
                atom-renam
                array-renam)))
           (make-expr-let
            :binds binds
            :body (expr-rename-type-vars expr.body
                                         atom-renam
                                         array-renam))))
   (atom :tlambda
         (b* (((mv & & atom-renam array-renam)
               (atom/array-rename-remove-bound (set::mergesort atom.params)
                                               atom-renam
                                               array-renam)))
           (make-atom-tlambda
            :params atom.params
            :body (expr-rename-type-vars atom.body
                                         atom-renam
                                         array-renam))))
   (bind :tfun
         (b* (((mv & & atom-renam array-renam)
               (atom/array-rename-remove-bound (set::mergesort bind.params)
                                               atom-renam
                                               array-renam)))
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
          :some (b* (((mv & & atom-renam array-renam)
                      (atom/array-rename-remove-bound
                       (set::mergesort bind.tparams?.val)
                       atom-renam
                       array-renam)))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? bind.iparams?
                   :params (var+type?-list-rename-type-vars bind.params
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
                 :params (var+type?-list-rename-type-vars bind.params
                                                          atom-renam
                                                          array-renam)
                 :type (type-rename-type-vars bind.type
                                              atom-renam
                                              array-renam)
                 :expr (expr-rename-type-vars bind.expr
                                              atom-renam
                                              array-renam))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-rename-type-vars bind atom-renam array-renam))
         ((mv & & atom-renam array-renam)
          (atom/array-rename-remove-bound (bind-bound-type-vars bind)
                                          atom-renam
                                          array-renam)))
      (cons new-bind
            (bind-list-rename-type-vars (cdr bind-list)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-expr-vars
  :short "Rename free expression variables in ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be guarded by @(tsee ast-rename-expr-vars-no-capture-p),
     but currently @(tsee fty::deffold-map) does not support such guards.
     One should call the @(tsee ast-rename-expr-vars-no-capture-p) predicates
     prior to applying these renaming operations, for the time being."))
  :types (exprs/atoms/binds)
  :extra-args ((renam string-string-mapp))
  :override
  ((expr :var (b* ((renam (string-string-map-fix renam))
                   (var+name (omap::assoc expr.name renam)))
                (if var+name
                    (expr-var (cdr var+name))
                  (expr-var expr.name))))
   (expr :unbox
         (b* ((target (expr-rename-expr-vars expr.target renam))
              (renam (omap::delete expr.var (string-string-map-fix renam))))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var expr.var
            :target target
            :body (expr-rename-expr-vars expr.body renam)
            ;; the result type has no expression variables, so we carry it
            :type? expr.type?)))
   (expr :let
         (b* ((binds (bind-list-rename-expr-vars expr.binds renam))
              (bound (bind-list-bound-expr-vars expr.binds))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (make-expr-let
            :binds binds
            :body (expr-rename-expr-vars expr.body renam))))
   (atom :lambda
         (b* ((bound (set::mergesort (var+type?-list->var atom.params)))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (make-atom-lambda
            :params atom.params
            :body (expr-rename-expr-vars atom.body renam)
            :type? atom.type?)))
   (bind :fun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (make-bind-fun
            :var bind.var
            :params bind.params
            :type? bind.type?
            :expr (expr-rename-expr-vars bind.expr renam))))
   (bind :cfun
         (b* ((bound (set::mergesort (var+type?-list->var bind.params)))
              (renam (omap::delete* bound (string-string-map-fix renam))))
           (make-bind-cfun
            :var bind.var
            :tparams? bind.tparams?
            :iparams? bind.iparams?
            :params bind.params
            :type bind.type
            :expr (expr-rename-expr-vars bind.expr renam))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-rename-expr-vars bind renam))
         (bound (bind-bound-expr-vars bind))
         (renam (omap::delete* bound (string-string-map-fix renam))))
      (cons new-bind
            (bind-list-rename-expr-vars (cdr bind-list) renam)))))
  :name ast-rename-expr-vars)
