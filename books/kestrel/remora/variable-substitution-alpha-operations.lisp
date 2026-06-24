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
    "This is work in progress."))
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
     :verify-guards :after-returns)))

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
    "This supports the capture-avoiding substitution of type variables.
     When the substitution descends under a construct
     that binds the type variables @('bound-vars'),
     instead of merely removing them from the substitution maps
     (which could capture variables),
     we rename them to fresh variables, on the fly,
     by extending the (restricted) substitution maps to send
     each bound variable to the type consisting of a fresh variable.
     The fresh variables avoid
     the free type variables of the restricted substitution maps
     and the type variables @('body-vars') of the body of the binder,
     so that no capture occurs and binding structure is preserved.
     We return the fresh variables (to rebuild the binder)
     and the extended substitution maps (to recurse into the body)."))
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
    "This supports the capture-avoiding substitution of expression variables.
     When the substitution descends under a construct
     that binds the expression variables @('bound-vars'),
     instead of merely removing them from the substitution
     (which could capture variables),
     we rename them to fresh variables, on the fly,
     by extending the (restricted) substitution to send
     each bound variable to the expression consisting of a fresh variable.
     The fresh variables avoid
     the free expression variables of the restricted substitution
     and the expression variables @('body-vars') of the body of the binder,
     so that no capture occurs and binding structure is preserved.
     We return the fresh variables (to rebuild the binder)
     and the extended substitution (to recurse into the body)."))
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
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-type-alpha-extend ((binds bind-listp)
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
     @(tsee ast-subst-type-vars-alpha) processes a list of bindings
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
    (bind-list-type-alpha-extend (cdr binds) atom-subst array-subst avoid))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv bind-list-type-alpha-extend
    :hints (("Goal"
             :induct (bind-list-type-alpha-extend
                      binds atom-subst array-subst avoid)
             :in-theory (enable bind-list-type-alpha-extend)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map subst-type-vars-alpha
  :short "Substitute type variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
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
     recomputed via @(tsee bind-list-type-alpha-extend).
     The @('avoid') extra argument conveys, into the bindings traversal,
     the type variables of the @('let') (its bindings and body),
     which the fresh variables generated for the bound variables must avoid;
     it is otherwise threaded unchanged."))
  :types (types
          type-option
          type-list-option
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
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
               (atom/array-subst-alpha-bound type.params
                                             atom-subst
                                             array-subst
                                             (type-free-type-vars type.body))))
           (make-type-forall
            :params fresh-params
            :body (type-subst-type-vars-alpha type.body
                                              atom-subst
                                              array-subst
                                              avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (type-var-set-fix avoid)
                       (set::union (bind-list-all-type-vars expr.binds)
                                   (expr-all-type-vars expr.body))))
              (binds (bind-list-subst-type-vars-alpha expr.binds
                                                      atom-subst
                                                      array-subst
                                                      avoid2))
              ((mv atom-subst array-subst)
               (bind-list-type-alpha-extend expr.binds
                                            atom-subst
                                            array-subst
                                            avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-subst-type-vars-alpha expr.body
                                              atom-subst
                                              array-subst
                                              avoid))))
   (atom :tlambda
         (b* (((mv fresh-params atom-subst array-subst)
               (atom/array-subst-alpha-bound atom.params
                                             atom-subst
                                             array-subst
                                             (expr-free-type-vars atom.body))))
           (make-atom-tlambda
            :params fresh-params
            :body (expr-subst-type-vars-alpha atom.body
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
            :type? (type-option-subst-type-vars-alpha bind.type?
                                                      atom-subst
                                                      array-subst
                                                      avoid)
            :expr (expr-subst-type-vars-alpha bind.expr
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
                        (var+type-list-free-type-vars bind.params)
                        (set::union (type-free-type-vars bind.type)
                                    (expr-free-type-vars bind.expr))))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? (type-var-list-option-some fresh-tparams)
                   :iparams? bind.iparams?
                   :params (var+type-list-subst-type-vars-alpha bind.params
                                                                atom-subst
                                                                array-subst
                                                                avoid)
                   :type (type-subst-type-vars-alpha bind.type
                                                     atom-subst
                                                     array-subst
                                                     avoid)
                   :expr (expr-subst-type-vars-alpha bind.expr
                                                     atom-subst
                                                     array-subst
                                                     avoid)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type-list-subst-type-vars-alpha bind.params
                                                              atom-subst
                                                              array-subst
                                                              avoid)
                 :type (type-subst-type-vars-alpha bind.type
                                                   atom-subst
                                                   array-subst
                                                   avoid)
                 :expr (expr-subst-type-vars-alpha bind.expr
                                                   atom-subst
                                                   array-subst
                                                   avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         ((mv new-bind atom-subst array-subst)
          (bind-case
           bind
           :type (b* ((type (type-subst-type-vars-alpha bind.type
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
           :otherwise (mv (bind-subst-type-vars-alpha bind
                                                      atom-subst
                                                      array-subst
                                                      avoid)
                          atom-subst
                          array-subst))))
      (cons new-bind
            (bind-list-subst-type-vars-alpha (cdr bind-list)
                                             atom-subst
                                             array-subst
                                             avoid)))))
  :name ast-subst-type-vars-alpha)
