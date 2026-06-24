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
     :verify-guards :after-returns)))

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
