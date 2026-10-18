; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/omaps/top" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ omaps
  :parents (library-extensions)
  :short "Library extensions for omaps."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The values of a map under the map operations.
;
; Removing keys can only shrink the set of values, and updating a key can
; only add the new value to it; the -WHEN-SUBSET variants carry a known
; containment of the values through a removal, which is the form in which
; these arise when a renaming map is reduced at a binder.

(defruled subset-values-of-delete
  :short "Deleting a key can only shrink the set of values."
  (set::subset (omap::values (omap::delete k m))
               (omap::values m)))

(defruled subset-values-of-delete*
  :short "Deleting keys can only shrink the set of values."
  (set::subset (omap::values (omap::delete* keys m))
               (omap::values m)))

(defruled subset-values-of-delete-when-subset
  (implies (set::subset (omap::values m) u)
           (set::subset (omap::values (omap::delete k m)) u))
  :use (subset-values-of-delete
        (:instance set::subset-transitive
                   (x (omap::values (omap::delete k m)))
                   (y (omap::values m))
                   (z u))))

(defruled subset-values-of-delete*-when-subset
  (implies (set::subset (omap::values m) u)
           (set::subset (omap::values (omap::delete* keys m)) u))
  :use (subset-values-of-delete*
        (:instance set::subset-transitive
                   (x (omap::values (omap::delete* keys m)))
                   (y (omap::values m))
                   (z u))))

;;;;;;;;;;;;;;;;;;;;

(defruled subset-values-of-update
  :short "Updating a key can only add the new value to the set of values."
  (set::subset (omap::values (omap::update k v m))
               (set::insert v (omap::values m)))
  :enable (omap::values-of-update
           subset-values-of-delete-when-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lookup in a tail, and the membership contrapositive of the containment of
; the values of a deletion.

(defruled assoc-when-assoc-of-tail
  (implies (omap::assoc k (omap::tail m))
           (equal (omap::assoc k m)
                  (omap::assoc k (omap::tail m))))
  :enable omap::assoc)

(defruled not-in-values-of-delete-when-subset
  :short "A name outside a superset of the values
          is not a value of a deletion."
  (implies (and (set::subset (omap::values m) s)
                (not (set::in x s)))
           (not (set::in x (omap::values (omap::delete name m)))))
  :use ((:instance subset-values-of-delete-when-subset (k name) (u s))
        (:instance set::subset-in
                   (a x)
                   (x (omap::values (omap::delete name m)))
                   (y s))))
