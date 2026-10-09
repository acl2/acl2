; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "variable-renaming-operations")
(include-book "all-variable-operations")
(include-book "variable-name-sets")
(include-book "omaps")

(local (include-book "osets"))

; The renaming maps are read through their values here, and the variables
; of a type through the two name projections, so the library rules that
; carry a containment through those are wanted throughout.
(local (in-theory (enable subset-of-union
                          subset-values-of-delete
                          subset-values-of-delete*
                          subset-values-of-update)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming-no-capture-when-avoided
  :parents (abstract-syntax-variable-operations)
  :short "Capture-freedom of a renaming whose image avoids
          the variables of what is renamed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Renaming the variables of a type can capture: a variable renamed
     under a binder may collide with that binder's parameter, which is
     why the renaming operations come with the no-capture checks of
     @(see variable-renaming-operations).  Those checks succeed
     unconditionally when the renaming can produce no name that occurs in
     the type at all, which is the situation of a renaming whose values
     are freshly generated names.")
   (xdoc::p
    "This book states that condition as @(tsee map-values-avoid-p) --- the
     values of the map are disjoint from a set of names --- and proves
     that a renaming satisfying it, against the names of all the
     variables of a type, is capture-free in both variable namespaces.
     The condition survives the reduction of the map at a binder, which
     is what makes the induction go through."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Renaming maps whose values avoid a set of names.

(define map-values-avoid-p ((m string-string-mapp) (avoid string-setp))
  :returns (yes/no booleanp)
  :short "The values of a renaming map are disjoint from a set of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The uniquifier only ever records a freshly generated name as a map
     value, and fresh names avoid the constant set @('avoid') of all the
     names occurring in the expression.  So this is invariant along the
     traversal, and it is what makes the deterministic renaming of an
     embedded type capture-free: the binders inside the type are among
     the avoided names."))
  (set::emptyp (set::intersect (omap::values (string-string-map-fix m))
                               (string-sfix avoid)))
  ///
  (fty::deffixequiv map-values-avoid-p))

(in-theory (disable map-values-avoid-p))

(defrule map-values-avoid-p-of-delete*
  (implies (map-values-avoid-p m avoid)
           (map-values-avoid-p (omap::delete* keys (string-string-map-fix m))
                               avoid))
  :enable map-values-avoid-p
  :use ((:instance emptyp-of-intersect-when-subsets
                   (a (omap::values
                       (omap::delete* keys (string-string-map-fix m))))
                   (a2 (omap::values (string-string-map-fix m)))
                   (b (string-sfix avoid))
                   (b2 (string-sfix avoid)))))

(defrule map-values-avoid-p-of-delete
  (implies (map-values-avoid-p m avoid)
           (map-values-avoid-p (omap::delete key (string-string-map-fix m))
                               avoid))
  :enable map-values-avoid-p
  :use ((:instance emptyp-of-intersect-when-subsets
                   (a (omap::values
                       (omap::delete key (string-string-map-fix m))))
                   (a2 (omap::values (string-string-map-fix m)))
                   (b (string-sfix avoid))
                   (b2 (string-sfix avoid)))))

(defrule map-values-avoid-p-of-update-when-not-in-avoid
  (implies (and (map-values-avoid-p m avoid)
                (stringp k)
                (stringp v)
                (not (set::in v (string-sfix avoid))))
           (map-values-avoid-p (omap::update k v (string-string-map-fix m))
                               avoid))
  :enable map-values-avoid-p
  :use ((:instance emptyp-of-intersect-when-subsets
                   (a (omap::values
                       (omap::update k v (string-string-map-fix m))))
                   (a2 (set::insert v (omap::values (string-string-map-fix m))))
                   (b (string-sfix avoid))
                   (b2 (string-sfix avoid)))
        (:instance set::intersect-insert-x
                   (a v)
                   (x (omap::values (string-string-map-fix m)))
                   (y (string-sfix avoid)))))

(defrule renaming-no-capture-p-of-nil
  (renaming-no-capture-p nil renam)
  :enable renaming-no-capture-p)

(defrule renaming-no-capture-p-of-delete*-when-avoided
  :short "Removing bound names from a map whose values avoid a set that
          contains those names cannot capture them."
  (implies (and (map-values-avoid-p m avoid)
                (set::subset (string-sfix names) (string-sfix avoid)))
           (renaming-no-capture-p names
                                  (omap::delete* names2
                                                 (string-string-map-fix m))))
  :enable (renaming-no-capture-p map-values-avoid-p)
  :use ((:instance emptyp-of-intersect-when-subsets
                   (a (omap::values
                       (omap::delete* names2 (string-string-map-fix m))))
                   (a2 (omap::values (string-string-map-fix m)))
                   (b (string-sfix names))
                   (b2 (string-sfix avoid)))
        (:instance set::intersect-symmetric
                   (x (string-sfix names))
                   (y (omap::values
                       (omap::delete* names2 (string-string-map-fix m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Embedded types: the deterministic renaming of a type is capture-free when
; the map values avoid all the names in the type.  The middle theorem is
; what lets the two namespaces be treated in sequence: the first stage of
; the renaming, over ispace variables, leaves the type variables alone.

(defthm-types-rename-ispace-vars-no-capture-p-flag
  (defthm type-rename-ispace-vars-no-capture-p-when-avoided
    (implies (and (map-values-avoid-p dim-renam avoid)
                  (map-values-avoid-p shape-renam avoid)
                  (set::subset (ispace-var-set-names
                                (type-all-ispace-vars type))
                               (string-sfix avoid)))
             (type-rename-ispace-vars-no-capture-p type dim-renam shape-renam))
    :flag type-rename-ispace-vars-no-capture-p)
  (defthm type-list-rename-ispace-vars-no-capture-p-when-avoided
    (implies (and (map-values-avoid-p dim-renam avoid)
                  (map-values-avoid-p shape-renam avoid)
                  (set::subset (ispace-var-set-names
                                (type-list-all-ispace-vars type-list))
                               (string-sfix avoid)))
             (type-list-rename-ispace-vars-no-capture-p type-list
                                                        dim-renam
                                                        shape-renam))
    :flag type-list-rename-ispace-vars-no-capture-p)
  :hints (("Goal"
           :expand ((type-rename-ispace-vars-no-capture-p type
                                                          dim-renam
                                                          shape-renam)
                    (type-list-rename-ispace-vars-no-capture-p type-list
                                                               dim-renam
                                                               shape-renam)
                    (type-all-ispace-vars type)
                    (type-list-all-ispace-vars type-list))
           :in-theory (enable dim/shape-rename-remove-bound ispace-var->name))))

(defthm-types-rename-ispace-vars-flag
  (defthm type-all-type-vars-of-type-rename-ispace-vars
    (equal (type-all-type-vars
            (type-rename-ispace-vars type dim-renam shape-renam))
           (type-all-type-vars type))
    :flag type-rename-ispace-vars)
  (defthm type-list-all-type-vars-of-type-list-rename-ispace-vars
    (equal (type-list-all-type-vars
            (type-list-rename-ispace-vars type-list dim-renam shape-renam))
           (type-list-all-type-vars type-list))
    :flag type-list-rename-ispace-vars)
  :hints (("Goal"
           :expand ((type-rename-ispace-vars type dim-renam shape-renam)
                    (type-list-rename-ispace-vars type-list
                                                  dim-renam
                                                  shape-renam)
                    (type-all-type-vars type)
                    (type-list-all-type-vars type-list))
           :in-theory (enable type-all-type-vars
                              type-list-all-type-vars))))

(defthm-types-rename-type-vars-no-capture-p-flag
  (defthm type-rename-type-vars-no-capture-p-when-avoided
    (implies (and (map-values-avoid-p atom-renam avoid)
                  (map-values-avoid-p array-renam avoid)
                  (set::subset (type-var-set-names
                                (type-all-type-vars type))
                               (string-sfix avoid)))
             (type-rename-type-vars-no-capture-p type atom-renam array-renam))
    :flag type-rename-type-vars-no-capture-p)
  (defthm type-list-rename-type-vars-no-capture-p-when-avoided
    (implies (and (map-values-avoid-p atom-renam avoid)
                  (map-values-avoid-p array-renam avoid)
                  (set::subset (type-var-set-names
                                (type-list-all-type-vars type-list))
                               (string-sfix avoid)))
             (type-list-rename-type-vars-no-capture-p type-list
                                                      atom-renam
                                                      array-renam))
    :flag type-list-rename-type-vars-no-capture-p)
  :hints (("Goal"
           :expand ((type-rename-type-vars-no-capture-p type
                                                        atom-renam
                                                        array-renam)
                    (type-list-rename-type-vars-no-capture-p type-list
                                                             atom-renam
                                                             array-renam)
                    (type-all-type-vars type)
                    (type-list-all-type-vars type-list))
           :in-theory (enable atom/array-rename-remove-bound type-var->name))))
