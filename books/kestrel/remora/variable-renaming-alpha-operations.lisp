; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "variable-renaming-operations")
(include-book "fresh-variable-operations")

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variable-renaming-alpha-operations
  :parents (abstract-syntax-variable-operations)
  :short "Operations for renaming variables,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "The renamings are represented
     as in @(see variable-renaming-operations).")
   (xdoc::p
    "These are the capture-avoiding counterparts of
     the operations in @(see variable-renaming-operations),
     in the same way as @(see variable-substitution-alpha-operations)
     is the capture-avoiding counterpart of
     @(see variable-substitution-operations).
     Instead of requiring a separate no-capture check,
     at each binder these operations alpha-rename the bound variables
     to fresh ones, extending the renaming with the renamings,
     and rebuild the binder with the fresh variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim/shape-rename-alpha-bound ((bound-vars ispace-var-listp)
                                      (dim-renam string-string-mapp)
                                      (shape-renam string-string-mapp)
                                      (body-vars ispace-var-setp))
  :returns (mv (fresh-vars ispace-var-listp)
               (new-dim-renam string-string-mapp)
               (new-shape-renam string-string-mapp))
  :short "Alpha-rename a list of bound ispace variables to fresh ones,
          extending a dimension and a shape renaming accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This supports the capture-avoiding renaming of ispace variables.
     When the renaming descends under a construct
     that binds the ispace variables @('bound-vars'),
     instead of merely removing them from the renaming maps
     (which could capture variables),
     we rename them to fresh variables, on the fly,
     by extending the (restricted) renaming maps to send
     each bound variable to a fresh dimension or shape variable name.
     The fresh variables avoid
     the ispace variables that the restricted renaming maps target
     (i.e. the values of the maps)
     and the ispace variables @('body-vars') of the body of the binder,
     so that no capture occurs and binding structure is preserved.
     We return the fresh variables (to rebuild the binder)
     and the extended renaming maps (to recurse into the body)."))
  (b* (((mv & & dim-renam shape-renam)
        (dim/shape-rename-remove-bound
         (set::mergesort (ispace-var-list-fix bound-vars))
         dim-renam
         shape-renam))
       (avoid (set::union
               (ispace-var-set-fix body-vars)
               (set::union
                (ispace-var-dims-from-names (omap::values dim-renam))
                (ispace-var-shapes-from-names (omap::values shape-renam))))))
    (dim/shape-rename-alpha-bound-loop bound-vars dim-renam shape-renam avoid))
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::string-setp-of-values-when-string-string-mapp)))

  :prepwork
  ((define dim/shape-rename-alpha-bound-loop ((bound-vars ispace-var-listp)
                                              (dim-renam string-string-mapp)
                                              (shape-renam string-string-mapp)
                                              (avoid ispace-var-setp))
     :returns (mv (fresh-vars ispace-var-listp)
                  (new-dim-renam string-string-mapp)
                  (new-shape-renam string-string-mapp))
     :parents nil
     (b* (((when (endp bound-vars))
           (mv nil
               (string-string-map-fix dim-renam)
               (string-string-map-fix shape-renam)))
          (var (car bound-vars))
          ((mv fresh-var dim-renam shape-renam avoid)
           (ispace-var-case
            var
            :dim (b* ((fresh (fresh-dim-ispace-var var.name avoid))
                      (dim-renam
                       (omap::update var.name
                                     (ispace-var->name fresh)
                                     (string-string-map-fix dim-renam))))
                   (mv fresh
                       dim-renam
                       shape-renam
                       (set::insert fresh (ispace-var-set-fix avoid))))
            :shape (b* ((fresh (fresh-shape-ispace-var var.name avoid))
                        (shape-renam
                         (omap::update var.name
                                       (ispace-var->name fresh)
                                       (string-string-map-fix shape-renam))))
                     (mv fresh
                         dim-renam
                         shape-renam
                         (set::insert fresh (ispace-var-set-fix avoid))))))
          ((mv fresh-vars dim-renam shape-renam)
           (dim/shape-rename-alpha-bound-loop (cdr bound-vars)
                                              dim-renam
                                              shape-renam
                                              avoid)))
       (mv (cons fresh-var fresh-vars) dim-renam shape-renam))
     :verify-guards :after-returns

     ///

     (defret consp-of-fresh-vars-of-dim/shape-rename-alpha-bound-loop
       (equal (consp fresh-vars)
              (consp bound-vars))
       :hints (("Goal" :induct t)))))

  ///

  (defret consp-of-fresh-vars-of-dim/shape-rename-alpha-bound
    (equal (consp fresh-vars)
           (consp bound-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom/array-rename-alpha-bound ((bound-vars type-var-listp)
                                       (atom-renam string-string-mapp)
                                       (array-renam string-string-mapp)
                                       (body-vars type-var-setp))
  :returns (mv (fresh-vars type-var-listp)
               (new-atom-renam string-string-mapp)
               (new-array-renam string-string-mapp))
  :short "Alpha-rename a list of bound type variables to fresh ones,
          extending an atom-kind and an array-kind type renaming accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type-variable analogue of
     @(tsee dim/shape-rename-alpha-bound)."))
  (b* (((mv & & atom-renam array-renam)
        (atom/array-rename-remove-bound
         (set::mergesort (type-var-list-fix bound-vars))
         atom-renam
         array-renam))
       (avoid (set::union
               (type-var-set-fix body-vars)
               (set::union
                (type-var-atoms-from-names (omap::values atom-renam))
                (type-var-arrays-from-names (omap::values array-renam))))))
    (atom/array-rename-alpha-bound-loop bound-vars atom-renam array-renam avoid))
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::string-setp-of-values-when-string-string-mapp)))

  :prepwork
  ((define atom/array-rename-alpha-bound-loop ((bound-vars type-var-listp)
                                               (atom-renam string-string-mapp)
                                               (array-renam string-string-mapp)
                                               (avoid type-var-setp))
     :returns (mv (fresh-vars type-var-listp)
                  (new-atom-renam string-string-mapp)
                  (new-array-renam string-string-mapp))
     :parents nil
     (b* (((when (endp bound-vars))
           (mv nil
               (string-string-map-fix atom-renam)
               (string-string-map-fix array-renam)))
          (var (car bound-vars))
          ((mv fresh-var atom-renam array-renam avoid)
           (type-var-case
            var
            :atom (b* ((fresh (fresh-atom-type-var var.name avoid))
                       (atom-renam
                        (omap::update var.name
                                      (type-var->name fresh)
                                      (string-string-map-fix atom-renam))))
                    (mv fresh
                        atom-renam
                        array-renam
                        (set::insert fresh (type-var-set-fix avoid))))
            :array (b* ((fresh (fresh-array-type-var var.name avoid))
                        (array-renam
                         (omap::update var.name
                                       (type-var->name fresh)
                                       (string-string-map-fix array-renam))))
                     (mv fresh
                         atom-renam
                         array-renam
                         (set::insert fresh (type-var-set-fix avoid))))))
          ((mv fresh-vars atom-renam array-renam)
           (atom/array-rename-alpha-bound-loop (cdr bound-vars)
                                               atom-renam
                                               array-renam
                                               avoid)))
       (mv (cons fresh-var fresh-vars) atom-renam array-renam))
     :verify-guards :after-returns

     ///

     (defret consp-of-fresh-vars-of-atom/array-rename-alpha-bound-loop
       (equal (consp fresh-vars)
              (consp bound-vars))
       :hints (("Goal" :induct t)))))

  ///

  (defret consp-of-fresh-vars-of-atom/array-rename-alpha-bound
    (equal (consp fresh-vars)
           (consp bound-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-rename-alpha-bound ((bound-vars string-listp)
                                 (renam string-string-mapp)
                                 (body-vars string-setp))
  :returns (mv (fresh-vars string-listp)
               (new-renam string-string-mapp))
  :short "Alpha-rename a set of bound expression variables to fresh ones,
          extending an expression renaming accordingly."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the expression-variable analogue of
     @(tsee dim/shape-rename-alpha-bound).
     Since expression variables form a single namespace,
     the renaming is a single map,
     and the variables to avoid are directly the values of the map
     (no conversion to a set of typed variables is needed)."))
  (b* ((renam (omap::delete* (set::mergesort (string-list-fix bound-vars))
                             (string-string-map-fix renam)))
       (avoid (set::union (string-sfix body-vars)
                          (omap::values renam))))
    (expr-rename-alpha-bound-loop bound-vars renam avoid))
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::string-setp-of-values-when-string-string-mapp)))

  :prepwork
  ((define expr-rename-alpha-bound-loop ((bound-vars string-listp)
                                         (renam string-string-mapp)
                                         (avoid string-setp))
     :returns (mv (fresh-vars string-listp)
                  (new-renam string-string-mapp))
     :parents nil
     (b* (((when (endp bound-vars)) (mv nil (string-string-map-fix renam)))
          (var (car bound-vars))
          (fresh-var (fresh-expr-var var avoid))
          (renam (omap::update (str-fix var)
                               fresh-var
                               (string-string-map-fix renam)))
          ((mv fresh-vars renam)
           (expr-rename-alpha-bound-loop (cdr bound-vars)
                                         renam
                                         (set::insert fresh-var
                                                      (string-sfix avoid)))))
       (mv (cons fresh-var fresh-vars) renam))
     :verify-guards :after-returns

     ///

     (defret consp-of-fresh-vars-of-expr-rename-alpha-bound-loop
       (equal (consp fresh-vars)
              (consp bound-vars))
       :hints (("Goal" :induct t)))))

  ///

  (defret consp-of-fresh-vars-of-expr-rename-alpha-bound
    (equal (consp fresh-vars)
           (consp bound-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-ispace-rename-alpha-extend ((binds bind-listp)
                                              (dim-renam string-string-mapp)
                                              (shape-renam string-string-mapp)
                                              (avoid ispace-var-setp))
  :returns (mv (new-dim-renam string-string-mapp)
               (new-shape-renam string-string-mapp))
  :short "Extend a dimension and a shape renaming
          with the renamings introduced by alpha-renaming
          the ispace variables bound in a list of @('let') bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the renaming analogue of
     @(tsee bind-list-ispace-subst-alpha-extend);
     see that operation for an explanation."))
  (b* (((when (endp binds))
        (mv (string-string-map-fix dim-renam)
            (string-string-map-fix shape-renam)))
       (bind (car binds))
       ((mv dim-renam shape-renam)
        (bind-case
         bind
         :ispace (b* (((mv & dim-renam shape-renam)
                       (dim/shape-rename-alpha-bound (list bind.var)
                                                     dim-renam
                                                     shape-renam
                                                     avoid)))
                   (mv dim-renam shape-renam))
         :otherwise (mv (string-string-map-fix dim-renam)
                        (string-string-map-fix shape-renam)))))
    (bind-list-ispace-rename-alpha-extend (cdr binds)
                                          dim-renam
                                          shape-renam
                                          avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-type-rename-alpha-extend ((binds bind-listp)
                                            (atom-renam string-string-mapp)
                                            (array-renam string-string-mapp)
                                            (avoid type-var-setp))
  :returns (mv (new-atom-renam string-string-mapp)
               (new-array-renam string-string-mapp))
  :short "Extend an atom-kind and an array-kind type renaming
          with the renamings introduced by alpha-renaming
          the type variables bound in a list of @('let') bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the renaming analogue of
     @(tsee bind-list-type-subst-alpha-extend);
     see that operation for an explanation."))
  (b* (((when (endp binds))
        (mv (string-string-map-fix atom-renam)
            (string-string-map-fix array-renam)))
       (bind (car binds))
       ((mv atom-renam array-renam)
        (bind-case
         bind
         :type (b* (((mv & atom-renam array-renam)
                     (atom/array-rename-alpha-bound (list bind.var)
                                                    atom-renam
                                                    array-renam
                                                    avoid)))
                 (mv atom-renam array-renam))
         :otherwise (mv (string-string-map-fix atom-renam)
                        (string-string-map-fix array-renam)))))
    (bind-list-type-rename-alpha-extend (cdr binds)
                                        atom-renam
                                        array-renam
                                        avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-list-expr-rename-alpha-extend ((binds bind-listp)
                                            (renam string-string-mapp)
                                            (avoid string-setp))
  :returns (new-renam string-string-mapp)
  :short "Extend an expression renaming
          with the renamings introduced by alpha-renaming
          the expression variables bound in a list of @('let') bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the renaming analogue of
     @(tsee bind-list-expr-subst-alpha-extend);
     see that operation for an explanation."))
  (b* (((when (endp binds)) (string-string-map-fix renam))
       (bind (car binds))
       ((mv & renam)
        (expr-rename-alpha-bound (bind-bound-expr-var-list bind) renam avoid)))
    (bind-list-expr-rename-alpha-extend (cdr binds) renam avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-ispace-vars-alpha-aux
  :short "Auxiliary functions to rename ispace variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are auxiliary functions because they all take
     a set of ispace variables to avoid.
     After these, we provide wrappers for some AST types,
     which are meant to be used to apply renamings in ASTs
     (whether they are sub-ASTs of others or not).")
   (xdoc::p
    "This is the capture-avoiding analogue of @(tsee ast-rename-ispace-vars).
     At each ispace-binding construct,
     instead of merely removing the bound variables from the renaming,
     we alpha-rename them to fresh variables
     (via @(tsee dim/shape-rename-alpha-bound)),
     extend the renaming with the renamings,
     and rebuild the binder with the fresh variables.
     The @('avoid') extra argument and the handling of @('let')
     are as in @(tsee ast-subst-ispace-vars-alpha-aux)."))
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-renam string-string-mapp)
               (shape-renam string-string-mapp)
               (avoid ispace-var-setp))
  :override
  ((shape :var (b* ((shape-renam (string-string-map-fix shape-renam))
                    (var+name (omap::assoc shape.name shape-renam)))
                 (if var+name
                     (shape-var (cdr var+name))
                   (shape-var shape.name))))
   (shape :dims (shape-dims (dim-list-rename-dim-vars shape.dims dim-renam)))
   (ispace :dim (ispace-dim (dim-rename-dim-vars ispace.dim dim-renam)))
   (type :pi
         (b* (((mv fresh-params dim-renam shape-renam)
               (dim/shape-rename-alpha-bound (list type.param)
                                             dim-renam
                                             shape-renam
                                             (type-free-ispace-vars type.body))))
           (make-type-pi
            :param (car fresh-params)
            :body (type-rename-ispace-vars-alpha-aux type.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (type :pin
         (b* (((mv fresh-params dim-renam shape-renam)
               (dim/shape-rename-alpha-bound type.params
                                             dim-renam
                                             shape-renam
                                             (type-free-ispace-vars type.body))))
           (make-type-pin
            :params fresh-params
            :body (type-rename-ispace-vars-alpha-aux type.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (type :sigma
         (b* (((mv fresh-params dim-renam shape-renam)
               (dim/shape-rename-alpha-bound type.params
                                             dim-renam
                                             shape-renam
                                             (type-free-ispace-vars type.body))))
           (make-type-sigma
            :params fresh-params
            :body (type-rename-ispace-vars-alpha-aux type.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (expr :unbox
         (b* ((target (expr-rename-ispace-vars-alpha-aux expr.target
                                                         dim-renam
                                                         shape-renam
                                                         avoid))
              ((mv fresh-ispaces dim-renam shape-renam)
               (dim/shape-rename-alpha-bound expr.ispaces
                                             dim-renam
                                             shape-renam
                                             (expr-free-ispace-vars expr.body))))
           (make-expr-unbox
            :ispaces fresh-ispaces
            :var expr.var
            :target target
            :body (expr-rename-ispace-vars-alpha-aux expr.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (ispace-var-set-fix avoid)
                       (set::union (bind-list-all-ispace-vars expr.binds)
                                   (expr-all-ispace-vars expr.body))))
              (binds (bind-list-rename-ispace-vars-alpha-aux expr.binds
                                                             dim-renam
                                                             shape-renam
                                                             avoid2))
              ((mv dim-renam shape-renam)
               (bind-list-ispace-rename-alpha-extend expr.binds
                                                     dim-renam
                                                     shape-renam
                                                     avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-rename-ispace-vars-alpha-aux expr.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (atom :ilambda
         (b* (((mv fresh-params dim-renam shape-renam)
               (dim/shape-rename-alpha-bound (list atom.param)
                                             dim-renam
                                             shape-renam
                                             (expr-free-ispace-vars
                                              atom.body)))
              (fresh-param (if (consp fresh-params)
                               (car fresh-params)
                             atom.param)))
           (make-atom-ilambda
            :param fresh-param
            :body (expr-rename-ispace-vars-alpha-aux atom.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (atom :ilambdan
         (b* (((mv fresh-params dim-renam shape-renam)
               (dim/shape-rename-alpha-bound atom.params
                                             dim-renam
                                             shape-renam
                                             (expr-free-ispace-vars
                                              atom.body))))
           (make-atom-ilambdan
            :params fresh-params
            :body (expr-rename-ispace-vars-alpha-aux atom.body
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (bind :ifun
         (b* (((mv fresh-params dim-renam shape-renam)
               (dim/shape-rename-alpha-bound
                bind.params
                dim-renam
                shape-renam
                (set::union (type-option-free-ispace-vars bind.type?)
                            (expr-free-ispace-vars bind.expr)))))
           (make-bind-ifun
            :var bind.var
            :params fresh-params
            :type? (type-option-rename-ispace-vars-alpha-aux bind.type?
                                                             dim-renam
                                                             shape-renam
                                                             avoid)
            :expr (expr-rename-ispace-vars-alpha-aux bind.expr
                                                     dim-renam
                                                     shape-renam
                                                     avoid))))
   (bind :cfun
         (ispace-var-list-option-case
          bind.iparams?
          :some (b* (((mv fresh-iparams dim-renam shape-renam)
                      (dim/shape-rename-alpha-bound
                       bind.iparams?.val
                       dim-renam
                       shape-renam
                       (set::union
                        (var+type?-list-free-ispace-vars bind.params)
                        (set::union (type-free-ispace-vars bind.type)
                                    (expr-free-ispace-vars bind.expr))))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? bind.tparams?
                   :iparams? (ispace-var-list-option-some fresh-iparams)
                   :params (var+type?-list-rename-ispace-vars-alpha-aux
                            bind.params dim-renam shape-renam avoid)
                   :type (type-rename-ispace-vars-alpha-aux bind.type
                                                            dim-renam
                                                            shape-renam
                                                            avoid)
                   :expr (expr-rename-ispace-vars-alpha-aux bind.expr
                                                            dim-renam
                                                            shape-renam
                                                            avoid)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type?-list-rename-ispace-vars-alpha-aux
                          bind.params dim-renam shape-renam avoid)
                 :type (type-rename-ispace-vars-alpha-aux bind.type
                                                          dim-renam
                                                          shape-renam
                                                          avoid)
                 :expr (expr-rename-ispace-vars-alpha-aux bind.expr
                                                          dim-renam
                                                          shape-renam
                                                          avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         ((mv new-bind dim-renam shape-renam)
          (bind-case
           bind
           :ispace (b* ((ispace (ispace-rename-ispace-vars-alpha-aux bind.ispace
                                                                     dim-renam
                                                                     shape-renam
                                                                     avoid))
                        ((mv fresh dim-renam shape-renam)
                         (dim/shape-rename-alpha-bound (list bind.var)
                                                       dim-renam
                                                       shape-renam
                                                       avoid)))
                     (mv (make-bind-ispace :var (car fresh) :ispace ispace)
                         dim-renam
                         shape-renam))
           :otherwise (mv (bind-rename-ispace-vars-alpha-aux bind
                                                             dim-renam
                                                             shape-renam
                                                             avoid)
                          dim-renam
                          shape-renam))))
      (cons new-bind
            (bind-list-rename-ispace-vars-alpha-aux (cdr bind-list)
                                                    dim-renam
                                                    shape-renam
                                                    avoid)))))
  :name ast-rename-ispace-vars-alpha-aux)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-rename-ispace-vars-alpha ((type typep)
                                       (dim-renam string-string-mapp)
                                       (shape-renam string-string-mapp))
  :returns (new-type typep)
  :short "Rename ispace variables in a type,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for types.
     It calls @(tsee type-rename-ispace-vars-alpha-aux)
     with an empty set of additional ispace variables to avoid.
     As explained in @(tsee ast-subst-type-vars-alpha-aux) for substitutions,
     the @('avoid') set is internal plumbing,
     so it is correct to start empty here,
     even when renaming in a subterm of a larger construct."))
  (type-rename-ispace-vars-alpha-aux type dim-renam shape-renam nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-rename-ispace-vars-alpha ((expr exprp)
                                       (dim-renam string-string-mapp)
                                       (shape-renam string-string-mapp))
  :returns (new-expr exprp)
  :short "Rename ispace variables in an expression,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for expressions;
     see @(tsee type-rename-ispace-vars-alpha)."))
  (expr-rename-ispace-vars-alpha-aux expr dim-renam shape-renam nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-rename-ispace-vars-alpha ((atom atomp)
                                       (dim-renam string-string-mapp)
                                       (shape-renam string-string-mapp))
  :returns (new-atom atomp)
  :short "Rename ispace variables in an atom,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for atoms;
     see @(tsee type-rename-ispace-vars-alpha)."))
  (atom-rename-ispace-vars-alpha-aux atom dim-renam shape-renam nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-type-vars-alpha-aux
  :short "Auxiliary functions to rename type variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the capture-avoiding analogue of @(tsee ast-rename-type-vars);
     see @(tsee ast-rename-ispace-vars-alpha-aux) and
     @(tsee ast-subst-type-vars-alpha-aux) for the general scheme."))
  :types (types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((atom-renam string-string-mapp)
               (array-renam string-string-mapp)
               (avoid type-var-setp))
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
         (b* (((mv fresh-params atom-renam array-renam)
               (atom/array-rename-alpha-bound (list type.param)
                                              atom-renam
                                              array-renam
                                              (type-free-type-vars type.body))))
           (make-type-forall
            :param (car fresh-params)
            :body (type-rename-type-vars-alpha-aux type.body
                                                   atom-renam
                                                   array-renam
                                                   avoid))))
   (type :foralln
         (b* (((mv fresh-params atom-renam array-renam)
               (atom/array-rename-alpha-bound type.params
                                              atom-renam
                                              array-renam
                                              (type-free-type-vars type.body))))
           (make-type-foralln
            :params fresh-params
            :body (type-rename-type-vars-alpha-aux type.body
                                                   atom-renam
                                                   array-renam
                                                   avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (type-var-set-fix avoid)
                       (set::union (bind-list-all-type-vars expr.binds)
                                   (expr-all-type-vars expr.body))))
              (binds (bind-list-rename-type-vars-alpha-aux expr.binds
                                                           atom-renam
                                                           array-renam
                                                           avoid2))
              ((mv atom-renam array-renam)
               (bind-list-type-rename-alpha-extend expr.binds
                                                   atom-renam
                                                   array-renam
                                                   avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-rename-type-vars-alpha-aux expr.body
                                                   atom-renam
                                                   array-renam
                                                   avoid))))
   (atom :tlambda
         (b* (((mv fresh-params atom-renam array-renam)
               (atom/array-rename-alpha-bound (list atom.param)
                                              atom-renam
                                              array-renam
                                              (expr-free-type-vars atom.body))))
           (make-atom-tlambda
            :param (car fresh-params)
            :body (expr-rename-type-vars-alpha-aux atom.body
                                                   atom-renam
                                                   array-renam
                                                   avoid))))
   (atom :tlambdan
         (b* (((mv fresh-params atom-renam array-renam)
               (atom/array-rename-alpha-bound atom.params
                                              atom-renam
                                              array-renam
                                              (expr-free-type-vars atom.body))))
           (make-atom-tlambdan
            :params fresh-params
            :body (expr-rename-type-vars-alpha-aux atom.body
                                                   atom-renam
                                                   array-renam
                                                   avoid))))
   (bind :tfun
         (b* (((mv fresh-params atom-renam array-renam)
               (atom/array-rename-alpha-bound
                bind.params
                atom-renam
                array-renam
                (set::union (type-option-free-type-vars bind.type?)
                            (expr-free-type-vars bind.expr)))))
           (make-bind-tfun
            :var bind.var
            :params fresh-params
            :type? (type-option-rename-type-vars-alpha-aux bind.type?
                                                           atom-renam
                                                           array-renam
                                                           avoid)
            :expr (expr-rename-type-vars-alpha-aux bind.expr
                                                   atom-renam
                                                   array-renam
                                                   avoid))))
   (bind :cfun
         (type-var-list-option-case
          bind.tparams?
          :some (b* (((mv fresh-tparams atom-renam array-renam)
                      (atom/array-rename-alpha-bound
                       bind.tparams?.val
                       atom-renam
                       array-renam
                       (set::union
                        (var+type?-list-free-type-vars bind.params)
                        (set::union (type-free-type-vars bind.type)
                                    (expr-free-type-vars bind.expr))))))
                  (make-bind-cfun
                   :var bind.var
                   :tparams? (type-var-list-option-some fresh-tparams)
                   :iparams? bind.iparams?
                   :params (var+type?-list-rename-type-vars-alpha-aux
                            bind.params atom-renam array-renam avoid)
                   :type (type-rename-type-vars-alpha-aux bind.type
                                                          atom-renam
                                                          array-renam
                                                          avoid)
                   :expr (expr-rename-type-vars-alpha-aux bind.expr
                                                          atom-renam
                                                          array-renam
                                                          avoid)))
          :none (make-bind-cfun
                 :var bind.var
                 :tparams? bind.tparams?
                 :iparams? bind.iparams?
                 :params (var+type?-list-rename-type-vars-alpha-aux
                          bind.params atom-renam array-renam avoid)
                 :type (type-rename-type-vars-alpha-aux bind.type
                                                        atom-renam
                                                        array-renam
                                                        avoid)
                 :expr (expr-rename-type-vars-alpha-aux bind.expr
                                                        atom-renam
                                                        array-renam
                                                        avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         ((mv new-bind atom-renam array-renam)
          (bind-case
           bind
           :type (b* ((type (type-rename-type-vars-alpha-aux bind.type
                                                             atom-renam
                                                             array-renam
                                                             avoid))
                      ((mv fresh atom-renam array-renam)
                       (atom/array-rename-alpha-bound (list bind.var)
                                                      atom-renam
                                                      array-renam
                                                      avoid)))
                   (mv (make-bind-type :var (car fresh) :type type)
                       atom-renam
                       array-renam))
           :otherwise (mv (bind-rename-type-vars-alpha-aux bind
                                                           atom-renam
                                                           array-renam
                                                           avoid)
                          atom-renam
                          array-renam))))
      (cons new-bind
            (bind-list-rename-type-vars-alpha-aux (cdr bind-list)
                                                  atom-renam
                                                  array-renam
                                                  avoid)))))
  :name ast-rename-type-vars-alpha-aux)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-rename-type-vars-alpha ((type typep)
                                     (atom-renam string-string-mapp)
                                     (array-renam string-string-mapp))
  :returns (new-type typep)
  :short "Rename type variables in a type,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for types;
     see @(tsee type-rename-ispace-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (type-rename-type-vars-alpha-aux type atom-renam array-renam nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-rename-type-vars-alpha ((expr exprp)
                                     (atom-renam string-string-mapp)
                                     (array-renam string-string-mapp))
  :returns (new-expr exprp)
  :short "Rename type variables in an expression,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for expressions;
     see @(tsee type-rename-type-vars-alpha)."))
  (expr-rename-type-vars-alpha-aux expr atom-renam array-renam nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-rename-type-vars-alpha ((atom atomp)
                                     (atom-renam string-string-mapp)
                                     (array-renam string-string-mapp))
  :returns (new-atom atomp)
  :short "Rename type variables in an atom,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for atoms;
     see @(tsee type-rename-type-vars-alpha)."))
  (atom-rename-type-vars-alpha-aux atom atom-renam array-renam nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map rename-expr-vars-alpha-aux
  :short "Auxiliary functions to rename expression variables in ASTs,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the capture-avoiding analogue of @(tsee ast-rename-expr-vars);
     see @(tsee ast-subst-expr-vars-alpha-aux) for the general scheme,
     including the rebuilding of @('var+type?-list') parameters
     via @(tsee var+type?-list-set-vars)."))
  :types (exprs/atoms/binds)
  :extra-args ((renam string-string-mapp)
               (avoid string-setp))
  :override
  ((expr :var (b* ((renam (string-string-map-fix renam))
                   (var+name (omap::assoc expr.name renam)))
                (if var+name
                    (expr-var (cdr var+name))
                  (expr-var expr.name))))
   (expr :unbox
         (b* ((target (expr-rename-expr-vars-alpha-aux expr.target renam avoid))
              ((mv fresh renam)
               (expr-rename-alpha-bound (list expr.var)
                                        renam
                                        (expr-free-expr-vars expr.body))))
           (make-expr-unbox
            :ispaces expr.ispaces
            :var (car fresh)
            :target target
            :body (expr-rename-expr-vars-alpha-aux expr.body renam avoid))))
   (expr :let
         (b* ((avoid2 (set::union
                       (string-sfix avoid)
                       (set::union (bind-list-all-expr-vars expr.binds)
                                   (expr-all-expr-vars expr.body))))
              (binds (bind-list-rename-expr-vars-alpha-aux expr.binds
                                                           renam
                                                           avoid2))
              (renam (bind-list-expr-rename-alpha-extend expr.binds
                                                         renam
                                                         avoid2)))
           (make-expr-let
            :binds binds
            :body (expr-rename-expr-vars-alpha-aux expr.body renam avoid))))
   (atom :lambdan
         (b* (((mv fresh renam)
               (expr-rename-alpha-bound (var+type?-list->var atom.params)
                                        renam
                                        (expr-free-expr-vars atom.body)))
              (params (var+type?-list-set-vars fresh atom.params)))
           (make-atom-lambdan
            :params params
            :body (expr-rename-expr-vars-alpha-aux atom.body renam avoid)
            :type? atom.type?)))
   (bind :fun
         (b* (((mv fresh renam)
               (expr-rename-alpha-bound (var+type?-list->var bind.params)
                                        renam
                                        (expr-free-expr-vars bind.expr)))
              (params (var+type?-list-set-vars fresh bind.params)))
           (make-bind-fun
            :var bind.var
            :params params
            :type? bind.type?
            :expr (expr-rename-expr-vars-alpha-aux bind.expr renam avoid))))
   (bind :cfun
         (b* (((mv fresh renam)
               (expr-rename-alpha-bound (var+type?-list->var bind.params)
                                        renam
                                        (expr-free-expr-vars bind.expr)))
              (params (var+type?-list-set-vars fresh bind.params)))
           (make-bind-cfun
            :var bind.var
            :tparams? bind.tparams?
            :iparams? bind.iparams?
            :params params
            :type bind.type
            :expr (expr-rename-expr-vars-alpha-aux bind.expr renam avoid))))
   (bind-list
    (b* (((when (endp bind-list)) nil)
         (bind (car bind-list))
         (new-bind (bind-rename-expr-vars-alpha-aux bind renam avoid))
         ((mv fresh renam)
          (expr-rename-alpha-bound (bind-bound-expr-var-list bind) renam avoid))
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
            (bind-list-rename-expr-vars-alpha-aux (cdr bind-list)
                                                  renam
                                                  avoid)))))
  :name ast-rename-expr-vars-alpha-aux)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-rename-expr-vars-alpha ((expr exprp) (renam string-string-mapp))
  :returns (new-expr exprp)
  :short "Rename expression variables in an expression,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for expressions;
     see @(tsee type-rename-ispace-vars-alpha) for why the @('avoid') set
     can be started empty here."))
  (expr-rename-expr-vars-alpha-aux expr renam nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-rename-expr-vars-alpha ((atom atomp) (renam string-string-mapp))
  :returns (new-atom atomp)
  :short "Rename expression variables in an atom,
          with automatic alpha renaming to avoid capture."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level entry point for atoms;
     see @(tsee expr-rename-expr-vars-alpha)."))
  (atom-rename-expr-vars-alpha-aux atom renam nil))
