; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "variable-substitution-operations")
(include-book "fresh-variable-operations")

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variable-substitution-alpha-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for substituting variables with other ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The substitutions are represented
     as in @(see variable-substitution-operations).")
   (xdoc::p
    "These are the capture-avoiding counterparts of
     the operations in @(see variable-substitution-operations).
     Instead of requiring a separate no-capture check,
     at each binder these operations alpha-rename the bound variables
     to fresh ones, extending the susbstitution with the renamings,
     and rebuild the binder with the fresh variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-subst-alpha-bound ((bound-vars ispace-var-listp)
                                     (dim-subst string-dim-mapp)
                                     (shape-subst string-shape-mapp)
                                     (body-vars ispace-var-setp))
  :returns (mv (fresh-vars ispace-var-listp)
               (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Alpha-rename a list of bound ispace variables to fresh ones,
          extending a dimension and a shape substitution accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This supports the capture-avoiding substitution of ispace variables.
     When the substitution descends under a construct
     that binds the ispace variables @('bound-vars'),
     instead of merely removing them from the substitution maps
     (which could capture variables),
     we rename them to fresh variables, on the fly,
     by extending the (restricted) substitution maps to send
     each bound variable to a fresh dimension or shape variable.
     The fresh variables avoid
     the free ispace variables of the restricted substitution maps
     and the ispace variables @('body-vars') of the body of the binder,
     so that no capture occurs and binding structure is preserved.
     We return the fresh variables (to rebuild the binder)
     and the extended substitution maps (to recurse into the body)."))
  (b* (((mv dim-subst shape-subst)
        (dim/shape-subst-remove-bound
         (set::mergesort (ispace-var-list-fix bound-vars))
         dim-subst
         shape-subst))
       (avoid (set::union
               (ispace-var-set-fix body-vars)
               (set::union (string-dim-map-free-ispace-vars dim-subst)
                           (string-shape-map-free-ispace-vars shape-subst)))))
    (dim/shape-subst-alpha-bound-loop bound-vars dim-subst shape-subst avoid))

  :prepwork
  ((define dim/shape-subst-alpha-bound-loop ((bound-vars ispace-var-listp)
                                             (dim-subst string-dim-mapp)
                                             (shape-subst string-shape-mapp)
                                             (avoid ispace-var-setp))
     :returns (mv (fresh-vars ispace-var-listp)
                  (new-dim-subst string-dim-mapp)
                  (new-shape-subst string-shape-mapp))
     :parents nil
     (b* (((when (endp bound-vars))
           (mv nil
               (string-dim-map-fix dim-subst)
               (string-shape-map-fix shape-subst)))
          (var (car bound-vars))
          ((mv fresh-var dim-subst shape-subst avoid)
           (ispace-var-case
            var
            :dim (b* ((fresh (fresh-dim-ispace-var var.name avoid))
                      (dim-subst
                       (omap::update var.name
                                     (dim-var (ispace-var->name fresh))
                                     (string-dim-map-fix dim-subst))))
                   (mv fresh
                       dim-subst
                       shape-subst
                       (set::insert fresh (ispace-var-set-fix avoid))))
            :shape (b* ((fresh (fresh-shape-ispace-var var.name avoid))
                        (shape-subst
                         (omap::update var.name
                                       (shape-var (ispace-var->name fresh))
                                       (string-shape-map-fix shape-subst))))
                     (mv fresh
                         dim-subst
                         shape-subst
                         (set::insert fresh (ispace-var-set-fix avoid))))))
          ((mv fresh-vars dim-subst shape-subst)
           (dim/shape-subst-alpha-bound-loop (cdr bound-vars)
                                             dim-subst
                                             shape-subst
                                             avoid)))
       (mv (cons fresh-var fresh-vars) dim-subst shape-subst))
     :verify-guards :after-returns

     ///

     (defret consp-of-fresh-vars-of-dim/shape-subst-alpha-bound-loop
       (equal (consp fresh-vars)
              (consp bound-vars))
       :hints (("Goal" :induct t)))))

  ///

  (defret consp-of-fresh-vars-of-dim/shape-subst-alpha-bound
    (equal (consp fresh-vars)
           (consp bound-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-subst-alpha-bound ((bound-vars type-var-listp)
                                      (atom-subst string-type-mapp)
                                      (array-subst string-type-mapp)
                                      (body-vars type-var-setp))
  :returns (mv (fresh-vars type-var-listp)
               (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Alpha-rename a list of bound type variables to fresh ones,
          extending an atom-kind and an array-kind type substitution
          accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type-variable analogue of
     @(tsee dim/shape-subst-alpha-bound)."))
  (b* (((mv atom-subst array-subst)
        (atom/array-subst-remove-bound
         (set::mergesort (type-var-list-fix bound-vars))
         atom-subst
         array-subst))
       (avoid (set::union
               (type-var-set-fix body-vars)
               (set::union (string-type-map-free-type-vars atom-subst)
                           (string-type-map-free-type-vars array-subst)))))
    (atom/array-subst-alpha-bound-loop bound-vars atom-subst array-subst avoid))

  :prepwork
  ((define atom/array-subst-alpha-bound-loop ((bound-vars type-var-listp)
                                              (atom-subst string-type-mapp)
                                              (array-subst string-type-mapp)
                                              (avoid type-var-setp))
     :returns (mv (fresh-vars type-var-listp)
                  (new-atom-subst string-type-mapp)
                  (new-array-subst string-type-mapp))
     :parents nil
     (b* (((when (endp bound-vars))
           (mv nil
               (string-type-map-fix atom-subst)
               (string-type-map-fix array-subst)))
          (var (car bound-vars))
          ((mv fresh-var atom-subst array-subst avoid)
           (type-var-case
            var
            :atom (b* ((fresh (fresh-atom-type-var var.name avoid))
                       (atom-subst
                        (omap::update var.name
                                      (type-var fresh)
                                      (string-type-map-fix atom-subst))))
                    (mv fresh
                        atom-subst
                        array-subst
                        (set::insert fresh (type-var-set-fix avoid))))
            :array (b* ((fresh (fresh-array-type-var var.name avoid))
                        (array-subst
                         (omap::update var.name
                                       (type-var fresh)
                                       (string-type-map-fix array-subst))))
                     (mv fresh
                         atom-subst
                         array-subst
                         (set::insert fresh (type-var-set-fix avoid))))))
          ((mv fresh-vars atom-subst array-subst)
           (atom/array-subst-alpha-bound-loop (cdr bound-vars)
                                              atom-subst
                                              array-subst
                                              avoid)))
       (mv (cons fresh-var fresh-vars) atom-subst array-subst))
     :verify-guards :after-returns

     ///

     (defret consp-of-fresh-vars-of-atom/array-subst-alpha-bound-loop
       (equal (consp fresh-vars)
              (consp bound-vars))
       :hints (("Goal" :induct t)))))

  ///

  (defret consp-of-fresh-vars-of-atom/array-subst-alpha-bound
    (equal (consp fresh-vars)
           (consp bound-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-subst-alpha-bound ((bound-vars string-listp)
                                (subst string-expr-mapp)
                                (body-vars string-setp))
  :returns (mv (fresh-vars string-listp)
               (new-subst string-expr-mapp))
  :short "Alpha-rename a set of bound expression variables to fresh ones,
          extending an expression substitution accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the expression-variable analogue of
     @(tsee dim/shape-subst-alpha-bound).
     Since expression variables form a single namespace,
     the substitution is a single map."))
  (b* ((subst (omap::delete* (set::mergesort (string-list-fix bound-vars))
                             (string-expr-map-fix subst)))
       (avoid (set::union (string-sfix body-vars)
                          (string-expr-map-free-expr-vars subst))))
    (expr-subst-alpha-bound-loop bound-vars subst avoid))

  :prepwork
  ((define expr-subst-alpha-bound-loop ((bound-vars string-listp)
                                        (subst string-expr-mapp)
                                        (avoid string-setp))
     :returns (mv (fresh-vars string-listp)
                  (new-subst string-expr-mapp))
     :parents nil
     (b* (((when (endp bound-vars)) (mv nil (string-expr-map-fix subst)))
          (var (car bound-vars))
          (fresh-var (fresh-expr-var var avoid))
          (subst (omap::update (str-fix var)
                               (expr-var fresh-var)
                               (string-expr-map-fix subst)))
          ((mv fresh-vars subst)
           (expr-subst-alpha-bound-loop (cdr bound-vars)
                                        subst
                                        (set::insert fresh-var
                                                     (string-sfix avoid)))))
       (mv (cons fresh-var fresh-vars) subst))
     :verify-guards :after-returns

     ///

     (defret consp-of-fresh-vars-of-expr-subst-alpha-bound-loop
       (equal (consp fresh-vars)
              (consp bound-vars))
       :hints (("Goal" :induct t)))))

  ///

  (defret consp-of-fresh-vars-of-expr-subst-alpha-bound
    (equal (consp fresh-vars)
           (consp bound-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-ispace-subst-alpha-extend ((binds bind-listp)
                                             (dim-subst string-dim-mapp)
                                             (shape-subst string-shape-mapp)
                                             (avoid ispace-var-setp))
  :returns (mv (new-dim-subst string-dim-mapp)
               (new-shape-subst string-shape-mapp))
  :short "Extend a dimension and a shape substitution
          with the renamings introduced by alpha-renaming
          the ispace variables bound in a list of @('let') bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since @('let') bindings are sequential,
     @(tsee ast-subst-ispace-vars-alpha-aux) processes a list of bindings
     by threading the substitution through the bindings,
     alpha-renaming the ispace variable bound by each @(':ispace') binding
     (using @(tsee dim/shape-subst-alpha-bound) on the singleton list
     of the bound variable) and extending the substitution accordingly.
     The body of the @('let') must be substituted
     with the substitution extended with all those renamings;
     but the @(tsee fty::deffold-map) traversal of the bindings
     returns only the new bindings, not the extended substitution.
     So this operation recomputes just the extended substitution,
     mirroring the threading performed on the bindings,
     for use in substituting the body of the @('let').
     The @('avoid') argument carries the ispace variables to avoid
     when generating fresh variables; it is the same value passed to
     the bindings traversal, so that the fresh variables generated here
     coincide with the ones used to rename the bindings.")
   (xdoc::p
    "Only @(':ispace') bindings bind ispace variables;
     the other kinds of bindings leave the substitution unchanged here
     (their internal ispace binders are handled when substituting the
     bindings themselves)."))
  (b* (((when (endp binds))
        (mv (string-dim-map-fix dim-subst)
            (string-shape-map-fix shape-subst)))
       (bind (car binds))
       ((mv dim-subst shape-subst)
        (bind-case
         bind
         :ispace (b* (((mv & dim-subst shape-subst)
                       (dim/shape-subst-alpha-bound (list bind.var)
                                                    dim-subst
                                                    shape-subst
                                                    avoid)))
                   (mv dim-subst shape-subst))
         :otherwise (mv (string-dim-map-fix dim-subst)
                        (string-shape-map-fix shape-subst)))))
    (bind-list-ispace-subst-alpha-extend (cdr binds)
                                         dim-subst
                                         shape-subst
                                         avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-type-subst-alpha-extend ((binds bind-listp)
                                           (atom-subst string-type-mapp)
                                           (array-subst string-type-mapp)
                                           (avoid type-var-setp))
  :returns (mv (new-atom-subst string-type-mapp)
               (new-array-subst string-type-mapp))
  :short "Extend an atom-kind and an array-kind type substitution
          with the renamings introduced by alpha-renaming
          the type variables bound in a list of @('let') bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since @('let') bindings are sequential,
     @(tsee ast-subst-type-vars-alpha-aux) processes a list of bindings
     by threading the substitution through the bindings,
     alpha-renaming the type variable bound by each @(':type') binding
     (using @(tsee atom/array-subst-alpha-bound) on the singleton list
     of the bound variable) and extending the substitution accordingly.
     The body of the @('let') must be substituted
     with the substitution extended with all those renamings;
     but the @(tsee fty::deffold-map) traversal of the bindings
     returns only the new bindings, not the extended substitution.
     So this operation recomputes just the extended substitution,
     mirroring the threading performed on the bindings,
     for use in substituting the body of the @('let').
     The @('avoid') argument carries the type variables to avoid
     when generating fresh variables; it is the same value passed to
     the bindings traversal, so that the fresh variables generated here
     coincide with the ones used to rename the bindings.")
   (xdoc::p
    "Only @(':type') bindings bind type variables;
     the other kinds of bindings leave the substitution unchanged here
     (their internal type binders are handled when substituting the
     bindings themselves)."))
  (b* (((when (endp binds))
        (mv (string-type-map-fix atom-subst)
            (string-type-map-fix array-subst)))
       (bind (car binds))
       ((mv atom-subst array-subst)
        (bind-case
         bind
         :type (b* (((mv & atom-subst array-subst)
                     (atom/array-subst-alpha-bound (list bind.var)
                                                   atom-subst
                                                   array-subst
                                                   avoid)))
                 (mv atom-subst array-subst))
         :otherwise (mv (string-type-map-fix atom-subst)
                        (string-type-map-fix array-subst)))))
    (bind-list-type-subst-alpha-extend (cdr binds)
                                       atom-subst
                                       array-subst
                                       avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-expr-subst-alpha-extend ((binds bind-listp)
                                           (subst string-expr-mapp)
                                           (avoid string-setp))
  :returns (new-subst string-expr-mapp)
  :short "Extend an expression substitution
          with the renamings introduced by alpha-renaming
          the expression variables bound in a list of @('let') bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since @('let') bindings are sequential,
     @(tsee ast-subst-expr-vars-alpha-aux) processes a list of bindings
     by threading the substitution through the bindings,
     alpha-renaming the expression variable bound by each binding
     (using @(tsee expr-subst-alpha-bound) on the variable)
     and extending the substitution accordingly.
     The body of the @('let') must be substituted
     with the substitution extended with all those renamings;
     but the @(tsee fty::deffold-map) traversal of the bindings
     returns only the new bindings, not the extended substitution.
     So this operation recomputes just the extended substitution,
     mirroring the threading performed on the bindings,
     for use in substituting the body of the @('let').
     The @('avoid') argument carries the expression variables to avoid
     when generating fresh variables; it is the same value passed to
     the bindings traversal, so that the fresh variables generated here
     coincide with the ones used to rename the bindings.")
   (xdoc::p
    "The value,
     function,
     type-function,
     ispace-function,
     and combined-function
     bindings each bind an expression variable;
     the ispace and type bindings do not,
     and so they leave the substitution unchanged here.
     This is handled uniformly via @(tsee bind-bound-expr-vars),
     which returns the (at most one) expression variable bound by a binding."))
  (b* (((when (endp binds)) (string-expr-map-fix subst))
       (bind (car binds))
       ((mv & subst)
        (expr-subst-alpha-bound (bind-bound-expr-var-list bind) subst avoid)))
    (bind-list-expr-subst-alpha-extend (cdr binds) subst avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-ispace-vars-alpha-aux
  :short "Auxiliary functions to substitute ispace variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are auxiliary functions because they all take
     a set of ispace variables to avoid.
     After these, we provide wrappers for some AST types,
     which are meant to be used to apply substitutions in ASTs
     (whether they are sub-ASTs of others or not).")
   (xdoc::p
    "The substitution consists of two maps,
     one for dimension variables and one for shape variables,
     as in @(tsee ast-subst-ispace-vars).")
   (xdoc::p
    "Unlike @(tsee ast-subst-ispace-vars),
     this does not require a separate no-capture check:
     at each ispace-binding construct,
     instead of merely removing the bound variables from the substitution,
     we alpha-rename them to fresh variables
     (via @(tsee dim/shape-subst-alpha-bound)),
     extending the substitution with the renamings,
     and rebuild the binder with the fresh variables.
     The fresh variables are chosen to avoid
     the free ispace variables of the (restricted) substitution
     and the ispace variables of the body of the binder,
     so that no capture occurs and binding structure is preserved.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     we substitute and alpha-rename the @(tsee car) of the list,
     extend the substitution with the renaming,
     and proceed to the @(tsee cdr) of the list.
     For the body of a @('let'),
     we substitute with the substitution extended with
     all the renamings of the bindings,
     recomputed via @(tsee bind-list-ispace-subst-alpha-extend).
     The @('avoid') extra argument conveys, into the bindings traversal,
     the ispace variables of the @('let') (its bindings and body),
     which the fresh variables generated for the bound variables must avoid;
     it is otherwise threaded unchanged.")
   (xdoc::p
    "The @('avoid') set is threaded through the bindings unchanged:
     it is not augmented with the fresh variables
     generated for the preceding bindings.
     This is correct because those fresh variables are already avoided
     via the substitution, which is threaded through the bindings.
     Each bound variable is mapped, in the substitution,
     to a dimension or shape consisting of its fresh variable,
     so the fresh variable occurs among the free ispace variables
     of the substitution maps,
     which @(tsee dim/shape-subst-alpha-bound) includes
     in the variables to avoid when generating subsequent fresh variables.
     Thus the bound variables are renamed to mutually distinct fresh variables
     without growing @('avoid').
     The @('avoid') set only needs to additionally cover
     the ispace variables that are not in the substitution,
     namely the other ispace variables of the @('let');
     since it conservatively includes all of them
     (an over-approximation of the scope of each binding),
     it needs no per-binding augmentation.")
   (xdoc::p
    "There is a subtle case when a binding shadows an earlier one
     that binds the same ispace variable name:
     extending the substitution replaces the earlier renaming,
     so the earlier fresh variable no longer occurs
     among the free ispace variables of the substitution,
     and could in principle be reused for a later binding.
     This is still correct: once its renaming has been removed
     from the substitution, that fresh variable can no longer be introduced
     into any remaining binding or into the body of the @('let')
     (nothing in the substitution maps to it any more,
     and, being fresh, it does not occur in the original ASTs),
     so reusing it cannot cause capture."))
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-subst string-dim-mapp)
               (shape-subst string-shape-mapp)
               (avoid ispace-var-setp))
  :override
  ((shape :var (b* ((shape-subst (string-shape-map-fix shape-subst))
                    (var+shape (omap::assoc shape.name shape-subst)))
                 (if var+shape
                     (cdr var+shape)
                   (shape-var shape.name))))
   (shape :dims (shape-dims (dim-list-subst-dim-vars shape.dims dim-subst)))
   (ispace :dim (ispace-dim (dim-subst-dim-vars ispace.dim dim-subst)))
   (type :pi
         (b* (((mv fresh-params dim-subst shape-subst)
               (dim/shape-subst-alpha-bound (list type.param)
                                            dim-subst
                                            shape-subst
                                            (type-free-ispace-vars type.body))))
           (make-type-pi
            :param (car fresh-params)
            :body (type-subst-ispace-vars-alpha-aux type.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (type :pin
         (b* (((mv fresh-params dim-subst shape-subst)
               (dim/shape-subst-alpha-bound type.params
                                            dim-subst
                                            shape-subst
                                            (type-free-ispace-vars type.body))))
           (make-type-pin
            :params fresh-params
            :body (type-subst-ispace-vars-alpha-aux type.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (type :sigma
         (b* (((mv fresh-params dim-subst shape-subst)
               (dim/shape-subst-alpha-bound type.params
                                            dim-subst
                                            shape-subst
                                            (type-free-ispace-vars type.body))))
           (make-type-sigma
            :params fresh-params
            :body (type-subst-ispace-vars-alpha-aux type.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (expr :unbox
         (b* ((target (expr-subst-ispace-vars-alpha-aux expr.target
                                                        dim-subst
                                                        shape-subst
                                                        avoid))
              ((mv fresh-ispaces dim-subst shape-subst)
               (dim/shape-subst-alpha-bound expr.ispaces
                                            dim-subst
                                            shape-subst
                                            (expr-free-ispace-vars expr.body))))
           (make-expr-unbox
            :ispaces fresh-ispaces
            :var expr.var
            :target target
            :body (expr-subst-ispace-vars-alpha-aux expr.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (ispace-var-set-fix avoid)
                       (set::union (bind-list-all-ispace-vars expr.binds)
                                   (expr-all-ispace-vars expr.body))))
              (binds (bind-list-subst-ispace-vars-alpha-aux expr.binds
                                                            dim-subst
                                                            shape-subst
                                                            avoid2))
              ((mv dim-subst shape-subst)
               (bind-list-ispace-subst-alpha-extend expr.binds
                                                    dim-subst
                                                    shape-subst
                                                    avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-subst-ispace-vars-alpha-aux expr.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (atom :ilambda
         (b* (((mv fresh-params dim-subst shape-subst)
               (dim/shape-subst-alpha-bound (list atom.param)
                                            dim-subst
                                            shape-subst
                                            (expr-free-ispace-vars atom.body)))
              (fresh-param (if (consp fresh-params)
                               (car fresh-params)
                             atom.param)))
           (make-atom-ilambda
            :param fresh-param
            :body (expr-subst-ispace-vars-alpha-aux atom.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (atom :ilambdan
         (b* (((mv fresh-params dim-subst shape-subst)
               (dim/shape-subst-alpha-bound atom.params
                                            dim-subst
                                            shape-subst
                                            (expr-free-ispace-vars atom.body))))
           (make-atom-ilambdan
            :params fresh-params
            :body (expr-subst-ispace-vars-alpha-aux atom.body
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (bind :ifun
         (b* (((mv fresh-params dim-subst shape-subst)
               (dim/shape-subst-alpha-bound
                bind.params
                dim-subst
                shape-subst
                (set::union (type-option-free-ispace-vars bind.type?)
                            (expr-free-ispace-vars bind.expr)))))
           (make-bind-ifun
            :var bind.var
            :params fresh-params
            :type? (type-option-subst-ispace-vars-alpha-aux bind.type?
                                                            dim-subst
                                                            shape-subst
                                                            avoid)
            :expr (expr-subst-ispace-vars-alpha-aux bind.expr
                                                    dim-subst
                                                    shape-subst
                                                    avoid))))
   (bind :cfun
         (ispace-var-list-option-case
          bind.iparams?
          :some (b* (((mv fresh-iparams dim-subst shape-subst)
                      (dim/shape-subst-alpha-bound
                       bind.iparams?.val
                       dim-subst
                       shape-subst
                       (set::union
                        (var+type?-list-free-ispace-vars bind.params)
                        (set::union (type-free-ispace-vars bind.type)
                                    (expr-free-ispace-vars bind.expr))))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? (ispace-var-list-option-some fresh-iparams)
                   :params (var+type?-list-subst-ispace-vars-alpha-aux
                            bind.params dim-subst shape-subst avoid)
                   :type (type-subst-ispace-vars-alpha-aux bind.type
                                                           dim-subst
                                                           shape-subst
                                                           avoid)
                   :expr (expr-subst-ispace-vars-alpha-aux bind.expr
                                                           dim-subst
                                                           shape-subst
                                                           avoid)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type?-list-subst-ispace-vars-alpha-aux
                          bind.params dim-subst shape-subst avoid)
                 :type (type-subst-ispace-vars-alpha-aux bind.type
                                                         dim-subst
                                                         shape-subst
                                                         avoid)
                 :expr (expr-subst-ispace-vars-alpha-aux bind.expr
                                                         dim-subst
                                                         shape-subst
                                                         avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         ((mv new-bind dim-subst shape-subst)
          (bind-case
           bind
           :ispace (b* ((ispace (ispace-subst-ispace-vars-alpha-aux bind.ispace
                                                                    dim-subst
                                                                    shape-subst
                                                                    avoid))
                        ((mv fresh dim-subst shape-subst)
                         (dim/shape-subst-alpha-bound (list bind.var)
                                                      dim-subst
                                                      shape-subst
                                                      avoid)))
                     (mv (make-bind-ispace :var (car fresh) :ispace ispace)
                         dim-subst
                         shape-subst))
           :otherwise (mv (bind-subst-ispace-vars-alpha-aux bind
                                                            dim-subst
                                                            shape-subst
                                                            avoid)
                          dim-subst
                          shape-subst))))
      (cons new-bind
            (bind-list-subst-ispace-vars-alpha-aux (cdr bind-list)
                                                   dim-subst
                                                   shape-subst
                                                   avoid)))))
  :name ast-subst-ispace-vars-alpha-aux)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-subst-ispace-vars-alpha ((type typep)
                                      (dim-subst string-dim-mapp)
                                      (shape-subst string-shape-mapp))
  :returns (new-type typep)
  :short "Substitute ispace variables in a type,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for types.
     It calls @(tsee type-subst-ispace-vars-alpha-aux)
     with an empty set of additional ispace variables to avoid.")
   (xdoc::p
    "As explained in @(see ast-subst-ispace-vars-alpha-aux),
     the @('avoid') set is needed only to thread,
     into the bindings of a @('let'),
     the ispace variables of the @('let') that the bindings cannot see;
     it is internal plumbing, not a channel for surrounding-scope variables.
     So it is correct to start with an empty @('avoid') set here,
     even when substituting in a subterm of a larger construct:
     the renaming is correct regardless of the surrounding context,
     because at each binder the fresh variables avoid
     the free variables of the binder's body
     (which already include any surrounding variables that occur free in it)
     and the free variables of the substitution's range."))
  (type-subst-ispace-vars-alpha-aux type dim-subst shape-subst nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-subst-ispace-vars-alpha ((expr exprp)
                                      (dim-subst string-dim-mapp)
                                      (shape-subst string-shape-mapp))
  :returns (new-expr exprp)
  :short "Substitute ispace variables in an expression,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for expressions;
     see @(tsee type-subst-ispace-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (expr-subst-ispace-vars-alpha-aux expr dim-subst shape-subst nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-subst-ispace-vars-alpha ((atom atomp)
                                      (dim-subst string-dim-mapp)
                                      (shape-subst string-shape-mapp))
  :returns (new-atom atomp)
  :short "Substitute ispace variables in an atom,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for atoms;
     see @(tsee type-subst-ispace-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (atom-subst-ispace-vars-alpha-aux atom dim-subst shape-subst nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-type-vars-alpha-aux
  :short "Auxiliary functions to substitute type variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are auxiliary functions because they all take
     a set of type variables to avoid.
     After these, we provide wrappers for some AST types,
     which are meant to be used to apply substitutions in ASTs
     (whether they are sub-ASTs of others or not).")
   (xdoc::p
    "The substitution consists of two maps,
     one for atom-kind type variables and one for array-kind type variables,
     as in @(tsee ast-subst-type-vars).")
   (xdoc::p
    "Unlike @(tsee ast-subst-type-vars),
     this does not require a separate no-capture check:
     at each type-binding construct,
     instead of merely removing the bound variables from the substitution,
     we alpha-rename them to fresh variables
     (via @(tsee atom/array-subst-alpha-bound)),
     extending the substitution with the renamings,
     and rebuild the binder with the fresh variables.
     The fresh variables are chosen to avoid
     the free type variables of the (restricted) substitution
     and the type variables of the body of the binder,
     so that no capture occurs and binding structure is preserved.")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     we substitute and alpha-rename the @(tsee car) of the list,
     extend the substitution with the renaming,
     and proceed to the @(tsee cdr) of the list.
     For the body of a @('let'),
     we substitute with the substitution extended with
     all the renamings of the bindings,
     recomputed via @(tsee bind-list-type-subst-alpha-extend).
     The @('avoid') extra argument conveys, into the bindings traversal,
     the type variables of the @('let') (its bindings and body),
     which the fresh variables generated for the bound variables must avoid;
     it is otherwise threaded unchanged.")
   (xdoc::p
    "The @('avoid') set is threaded through a list of bindings unchanged:
     it is not augmented with the fresh variables
     generated for the preceding bindings.
     This is correct because those fresh variables are already avoided
     via the substitution, which is threaded through the bindings.
     Each bound variable is mapped, in the substitution,
     to a type consisting of its fresh variable,
     so the fresh variable occurs among the free type variables
     of the substitution maps,
     which @(tsee atom/array-subst-alpha-bound) includes
     in the variables to avoid when generating subsequent fresh variables.
     Thus the bound variables are renamed to mutually distinct fresh variables
     without growing @('avoid').
     The @('avoid') set only needs to additionally cover
     the type variables that are not in the substitution,
     namely the other type variables of the @('let');
     since it conservatively includes all of them
     (an over-approximation of the scope of each binding),
     it needs no per-binding augmentation.")
   (xdoc::p
    "There is a subtle case when a binding shadows an earlier one
     that binds the same type variable name:
     extending the substitution replaces the earlier renaming,
     so the earlier fresh variable no longer occurs
     among the free type variables of the substitution,
     and could in principle be reused for a later binding.
     This is still correct: once its renaming has been removed
     from the substitution, that fresh variable can no longer be introduced
     into any remaining binding or into the body of the @('let')
     (nothing in the substitution maps to it any more,
     and, being fresh, it does not occur in the original ASTs),
     so reusing it cannot cause capture."))
  :types (types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((atom-subst string-type-mapp)
               (array-subst string-type-mapp)
               (avoid type-var-setp))
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
         (b* (((mv fresh-params atom-subst array-subst)
               (atom/array-subst-alpha-bound (list type.param)
                                             atom-subst
                                             array-subst
                                             (type-free-type-vars type.body))))
           (make-type-forall
            :param (car fresh-params)
            :body (type-subst-type-vars-alpha-aux type.body
                                                  atom-subst
                                                  array-subst
                                                  avoid))))
   (type :foralln
         (b* (((mv fresh-params atom-subst array-subst)
               (atom/array-subst-alpha-bound type.params
                                             atom-subst
                                             array-subst
                                             (type-free-type-vars type.body))))
           (make-type-foralln
            :params fresh-params
            :body (type-subst-type-vars-alpha-aux type.body
                                                  atom-subst
                                                  array-subst
                                                  avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (type-var-set-fix avoid)
                       (set::union (bind-list-all-type-vars expr.binds)
                                   (expr-all-type-vars expr.body))))
              (binds (bind-list-subst-type-vars-alpha-aux expr.binds
                                                          atom-subst
                                                          array-subst
                                                          avoid2))
              ((mv atom-subst array-subst)
               (bind-list-type-subst-alpha-extend expr.binds
                                                  atom-subst
                                                  array-subst
                                                  avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-subst-type-vars-alpha-aux expr.body
                                                  atom-subst
                                                  array-subst
                                                  avoid))))
   (atom :tlambda
         (b* (((mv fresh-params atom-subst array-subst)
               (atom/array-subst-alpha-bound (list atom.param)
                                             atom-subst
                                             array-subst
                                             (expr-free-type-vars atom.body))))
           (make-atom-tlambda
            :param (car fresh-params)
            :body (expr-subst-type-vars-alpha-aux atom.body
                                                  atom-subst
                                                  array-subst
                                                  avoid))))
   (atom :tlambdan
         (b* (((mv fresh-params atom-subst array-subst)
               (atom/array-subst-alpha-bound atom.params
                                             atom-subst
                                             array-subst
                                             (expr-free-type-vars atom.body))))
           (make-atom-tlambdan
            :params fresh-params
            :body (expr-subst-type-vars-alpha-aux atom.body
                                                  atom-subst
                                                  array-subst
                                                  avoid))))
   (bind :tfun
         (b* (((mv fresh-params atom-subst array-subst)
               (atom/array-subst-alpha-bound
                bind.params
                atom-subst
                array-subst
                (set::union (type-option-free-type-vars bind.type?)
                            (expr-free-type-vars bind.expr)))))
           (make-bind-tfun
            :var bind.var
            :params fresh-params
            :type? (type-option-subst-type-vars-alpha-aux bind.type?
                                                          atom-subst
                                                          array-subst
                                                          avoid)
            :expr (expr-subst-type-vars-alpha-aux bind.expr
                                                  atom-subst
                                                  array-subst
                                                  avoid))))
   (bind :cfun
         (type-var-list-option-case
          bind.tparams?
          :some (b* (((mv fresh-tparams atom-subst array-subst)
                      (atom/array-subst-alpha-bound
                       bind.tparams?.val
                       atom-subst
                       array-subst
                       (set::union
                        (var+type?-list-free-type-vars bind.params)
                        (set::union (type-free-type-vars bind.type)
                                    (expr-free-type-vars bind.expr))))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? (type-var-list-option-some fresh-tparams)
                   :iparams? bind.iparams?
                   :params (var+type?-list-subst-type-vars-alpha-aux bind.params
                                                                     atom-subst
                                                                     array-subst
                                                                     avoid)
                   :type (type-subst-type-vars-alpha-aux bind.type
                                                         atom-subst
                                                         array-subst
                                                         avoid)
                   :expr (expr-subst-type-vars-alpha-aux bind.expr
                                                         atom-subst
                                                         array-subst
                                                         avoid)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type?-list-subst-type-vars-alpha-aux bind.params
                                                                   atom-subst
                                                                   array-subst
                                                                   avoid)
                 :type (type-subst-type-vars-alpha-aux bind.type
                                                       atom-subst
                                                       array-subst
                                                       avoid)
                 :expr (expr-subst-type-vars-alpha-aux bind.expr
                                                       atom-subst
                                                       array-subst
                                                       avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         ((mv new-bind atom-subst array-subst)
          (bind-case
           bind
           :type (b* ((type (type-subst-type-vars-alpha-aux bind.type
                                                            atom-subst
                                                            array-subst
                                                            avoid))
                      ((mv fresh atom-subst array-subst)
                       (atom/array-subst-alpha-bound (list bind.var)
                                                     atom-subst
                                                     array-subst
                                                     avoid)))
                   (mv (make-bind-type :var (car fresh) :type type)
                       atom-subst
                       array-subst))
           :otherwise (mv (bind-subst-type-vars-alpha-aux bind
                                                          atom-subst
                                                          array-subst
                                                          avoid)
                          atom-subst
                          array-subst))))
      (cons new-bind
            (bind-list-subst-type-vars-alpha-aux (cdr bind-list)
                                                 atom-subst
                                                 array-subst
                                                 avoid)))))
  :name ast-subst-type-vars-alpha-aux)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-subst-type-vars-alpha ((type typep)
                                    (atom-subst string-type-mapp)
                                    (array-subst string-type-mapp))
  :returns (new-type typep)
  :short "Substitute type variables in a type,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for types.
     It calls @(tsee type-subst-type-vars-alpha-aux)
     with an empty set of additional type variables to avoid.")
   (xdoc::p
    "As explained in @(see ast-subst-type-vars-alpha-aux),
     the @('avoid') set is needed only to thread,
     into the bindings of a @('let'),
     the type variables of the @('let') that the bindings cannot see;
     it is internal plumbing, not a channel for surrounding-scope variables.
     So it is correct to start with an empty @('avoid') set here,
     even when substituting in a subterm of a larger construct:
     the renaming is correct regardless of the surrounding context,
     because at each binder the fresh variables avoid
     the free variables of the binder's body
     (which already include any surrounding variables that occur free in it)
     and the free variables of the substitution's range."))
  (type-subst-type-vars-alpha-aux type atom-subst array-subst nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-subst-type-vars-alpha ((expr exprp)
                                    (atom-subst string-type-mapp)
                                    (array-subst string-type-mapp))
  :returns (new-expr exprp)
  :short "Substitute type variables in an expression,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for expressions;
     see @(tsee type-subst-type-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (expr-subst-type-vars-alpha-aux expr atom-subst array-subst nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-subst-type-vars-alpha ((atom atomp)
                                    (atom-subst string-type-mapp)
                                    (array-subst string-type-mapp))
  :returns (new-atom atomp)
  :short "Substitute type variables in an atom,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for atoms;
     see @(tsee type-subst-type-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (atom-subst-type-vars-alpha-aux atom atom-subst array-subst nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-expr-vars-alpha-aux
  :short "Auxiliary functions to substitute expression variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are auxiliary functions because they all take
     a set of type variables to avoid.
     After these, we provide wrappers for some AST types,
     which are meant to be used to apply substitutions in ASTs
     (whether they are sub-ASTs of others or not).")
   (xdoc::p
    "The substitution consists of one map,
     as in @(tsee ast-subst-expr-vars).")
   (xdoc::p
    "Unlike @(tsee ast-subst-expr-vars),
     this does not require a separate no-capture check:
     at each expression-binding construct,
     instead of merely removing the bound variables from the substitution,
     we alpha-rename them to fresh variables
     (via @(tsee expr-subst-alpha-bound)),
     extending the substitution with the renamings,
     and rebuild the binder with the fresh variables.
     The fresh variables are chosen to avoid
     the free expression variables of the (restricted) substitution
     and the expression variables of the body of the binder,
     so that no capture occurs and binding structure is preserved.")
   (xdoc::p
    "The parameters of a lambda abstraction and of a function binding
     are variables with types;
     since types contain no expression variables,
     we rename only the variables (keeping the types),
     rebuilding the parameter list via @(tsee var+type?-list-set-vars).")
   (xdoc::p
    "Since @('let') bindings are sequential,
     we override the function for @(tsee bind-list)
     so that, for a non-empty list of bindings,
     we substitute and alpha-rename the @(tsee car) of the list,
     extend the substitution with the renaming,
     and proceed to the @(tsee cdr) of the list.
     For the body of a @('let'),
     we substitute with the substitution extended with
     all the renamings of the bindings,
     recomputed via @(tsee bind-list-expr-subst-alpha-extend).
     The @('avoid') extra argument conveys, into the bindings traversal,
     the expression variables of the @('let') (its bindings and body),
     which the fresh variables generated for the bound variables must avoid;
     it is otherwise threaded unchanged.")
   (xdoc::p
    "The @('avoid') set is threaded through a list of bindings unchanged:
     it is not augmented with the fresh variables
     generated for the preceding bindings.
     This is correct because those fresh variables are already avoided
     via the substitution, which is threaded through the bindings.
     Each bound variable is mapped, in the substitution,
     to an expression consisting of its fresh variable,
     so the fresh variable occurs among the free expression variables
     of the substitution,
     which @(tsee expr-subst-alpha-bound) includes
     in the variables to avoid when generating subsequent fresh variables.
     Thus the bound variables are renamed to mutually distinct fresh variables
     without growing @('avoid').
     The @('avoid') set only needs to additionally cover
     the expression variables that are not in the substitution,
     namely the other expression variables of the @('let');
     since it conservatively includes all of them
     (an over-approximation of the scope of each binding),
     it needs no per-binding augmentation.")
   (xdoc::p
    "There is a subtle case when a binding shadows an earlier one
     that binds the same expression variable name:
     extending the substitution replaces the earlier renaming,
     so the earlier fresh variable no longer occurs
     among the free expression variables of the substitution,
     and could in principle be reused for a later binding.
     This is still correct:
     once its renaming has been removed from the substitution,
     that fresh variable can no longer be introduced
     into any remaining binding or into the body of the @('let')
     (nothing in the substitution maps to it any more,
     and, being fresh, it does not occur in the original ASTs),
     so reusing it cannot cause capture."))
  :types (exprs/atoms/binds)
  :extra-args ((subst string-expr-mapp)
               (avoid string-setp))
  :override
  ((expr :var (b* ((subst (string-expr-map-fix subst))
                   (var+expr (omap::assoc expr.name subst)))
                (if var+expr
                    (cdr var+expr)
                  (expr-var expr.name))))
   (expr :unbox
         (b* ((target (expr-subst-expr-vars-alpha-aux expr.target subst avoid))
              ((mv fresh subst)
               (expr-subst-alpha-bound (list expr.var)
                                       subst
                                       (expr-free-expr-vars expr.body))))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var (car fresh)
            :target target
            :body (expr-subst-expr-vars-alpha-aux expr.body subst avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (string-sfix avoid)
                       (set::union (bind-list-all-expr-vars expr.binds)
                                   (expr-all-expr-vars expr.body))))
              (binds (bind-list-subst-expr-vars-alpha-aux expr.binds
                                                          subst
                                                          avoid2))
              (subst (bind-list-expr-subst-alpha-extend expr.binds subst avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-subst-expr-vars-alpha-aux expr.body subst avoid))))
   (atom :lambdan
         (b* (((mv fresh subst)
               (expr-subst-alpha-bound (var+type?-list->var atom.params)
                                       subst
                                       (expr-free-expr-vars atom.body)))
              (params (var+type?-list-set-vars fresh atom.params)))
           (make-atom-lambdan
            :params params
            :body (expr-subst-expr-vars-alpha-aux atom.body subst avoid)
            :type? atom.type?)))
   (bind :fun
         (b* (((mv fresh subst)
               (expr-subst-alpha-bound (var+type?-list->var bind.params)
                                       subst
                                       (expr-free-expr-vars bind.expr)))
              (params (var+type?-list-set-vars fresh bind.params)))
           (make-bind-fun
            :var bind.var
            :params params
            :type? bind.type?
            :expr (expr-subst-expr-vars-alpha-aux bind.expr subst avoid))))
   (bind :cfun
         (b* (((mv fresh subst)
               (expr-subst-alpha-bound (var+type?-list->var bind.params)
                                       subst
                                       (expr-free-expr-vars bind.expr)))
              (params (var+type?-list-set-vars fresh bind.params)))
           (make-bind-cfun
            :var bind.var
            :tparams? bind.tparams?
            :iparams? bind.iparams?
            :params params
            :type bind.type
            :expr (expr-subst-expr-vars-alpha-aux bind.expr subst avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-subst-expr-vars-alpha-aux bind subst avoid))
         ((mv fresh subst)
          (expr-subst-alpha-bound (bind-bound-expr-var-list bind) subst avoid))
         (new-bind
          (bind-case
           new-bind
           :val (if (consp fresh)
                    (change-bind-val new-bind :var (car fresh))
                  new-bind)
           :fun (if (consp fresh)
                    (change-bind-fun new-bind :var (car fresh))
                  new-bind)
           :tfun (if (consp fresh)
                     (change-bind-tfun new-bind :var (car fresh))
                   new-bind)
           :ifun (if (consp fresh)
                     (change-bind-ifun new-bind :var (car fresh))
                   new-bind)
           :cfun (if (consp fresh)
                     (change-bind-cfun new-bind :var (car fresh))
                   new-bind)
           :otherwise new-bind)))
      (cons new-bind
            (bind-list-subst-expr-vars-alpha-aux (cdr bind-list)
                                                 subst
                                                 avoid)))))
  :name ast-subst-expr-vars-alpha-aux)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-subst-expr-vars-alpha ((expr exprp) (subst string-expr-mapp))
  :returns (new-expr exprp)
  :short "Substitute expression variables in an expression,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for expressions.
     It calls @(tsee expr-subst-expr-vars-alpha-aux)
     with an empty set of additional expression variables to avoid.")
   (xdoc::p
    "As explained in @(see ast-subst-expr-vars-alpha-aux),
     the @('avoid') set is needed only to thread,
     into the bindings of a @('let'),
     the expression variables of the @('let') that the bindings cannot see;
     it is internal plumbing, not a channel for surrounding-scope variables.
     So it is correct to start with an empty @('avoid') set here,
     even when substituting in a subterm of a larger construct:
     the renaming is correct regardless of the surrounding context,
     because at each binder the fresh variables avoid
     the free variables of the binder's body
     (which already include any surrounding variables that occur free in it)
     and the free variables of the substitution's range."))
  (expr-subst-expr-vars-alpha-aux expr subst nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-subst-expr-vars-alpha ((atom atomp) (subst string-expr-mapp))
  :returns (new-atom atomp)
  :short "Substitute expression variables in an atom,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for atoms;
     see @(tsee expr-subst-expr-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (atom-subst-expr-vars-alpha-aux atom subst nil))
