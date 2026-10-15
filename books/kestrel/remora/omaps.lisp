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

(defrule car-of-assoc
  (implies (omap::assoc key map)
           (equal (car (omap::assoc key map))
                  key))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :induct t
  :enable omap::assoc)

(defruled delete*-of-delete*-commute
  (equal (omap::delete* keys1 (omap::delete* keys2 map))
         (omap::delete* keys2 (omap::delete* keys1 map)))
  :expand ((omap::ext-equal (omap::delete* keys1 (omap::delete* keys2 map))
                            (omap::delete* keys2 (omap::delete* keys1 map)))
           (omap::ext-equal (omap::delete* keys2 (omap::delete* keys1 map))
                            (omap::delete* keys1 (omap::delete* keys2 map))))
  :use ((:instance omap::ext-equal-becomes-equal
                   (omap::x (omap::delete* keys1 (omap::delete* keys2 map)))
                   (omap::y (omap::delete* keys2 (omap::delete* keys1 map))))))

(defruled delete*-of-delete*-fuse
  (equal (omap::delete* keys1 (omap::delete* keys2 map))
         (omap::delete* (set::union keys1 keys2) map))
  :expand ((omap::ext-equal (omap::delete* keys1 (omap::delete* keys2 map))
                            (omap::delete* (set::union keys1 keys2) map))
           (omap::ext-equal (omap::delete* (set::union keys1 keys2) map)
                            (omap::delete* keys1 (omap::delete* keys2 map))))
  :use ((:instance omap::ext-equal-becomes-equal
                   (omap::x (omap::delete* keys1 (omap::delete* keys2 map)))
                   (omap::y (omap::delete* (set::union keys1 keys2) map)))))

(defruled delete*-of-delete-commute
  (equal (omap::delete v (omap::delete* keys map))
         (omap::delete* keys (omap::delete v map)))
  :expand ((omap::ext-equal (omap::delete v (omap::delete* keys map))
                            (omap::delete* keys (omap::delete v map)))
           (omap::ext-equal (omap::delete* keys (omap::delete v map))
                            (omap::delete v (omap::delete* keys map))))
  :use ((:instance omap::ext-equal-becomes-equal
                   (omap::x (omap::delete v (omap::delete* keys map)))
                   (omap::y (omap::delete* keys (omap::delete v map))))))

(defruled delete*-commute-restricted
  (implies (syntaxp (and (symbolp bound)
                         (not (symbolp p))))
           (equal (omap::delete* p (omap::delete* bound map))
                  (omap::delete* bound (omap::delete* p map))))
  :use ((:instance delete*-of-delete*-commute (keys1 p) (keys2 bound))))

(defruled delete-commute-restricted
  (implies (syntaxp (symbolp bound))
           (equal (omap::delete v (omap::delete* bound map))
                  (omap::delete* bound (omap::delete v map))))
  :use ((:instance delete*-of-delete-commute (keys bound))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The values of a map under the map operations.
;
; Removing keys can only shrink the set of values, and updating a key can
; only add the new value to it; the -WHEN-SUBSET variants carry a known
; containment of the values through a removal, which is the form in which
; these arise when a renaming map is reduced at a binder.

(defruled subset-values-when-submap
  :short "The values of a submap are among the values of the map."
  (implies (omap::submap sub sup)
           (set::subset (omap::values sub) (omap::values sup)))
  :induct (omap::submap sub sup)
  :enable (omap::submap omap::values omap::in-values-when-assoc))

(defruled subset-values-of-delete
  :short "Deleting a key can only shrink the set of values."
  (set::subset (omap::values (omap::delete k m))
               (omap::values m))
  :use ((:instance subset-values-when-submap
                   (sub (omap::delete k m))
                   (sup m))))

(defruled subset-values-of-delete*
  :short "Deleting keys can only shrink the set of values."
  (set::subset (omap::values (omap::delete* keys m))
               (omap::values m))
  :use ((:instance subset-values-when-submap
                   (sub (omap::delete* keys m))
                   (sup m))))

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

(defruled in-of-values-of-update
  (implies (set::in y (omap::values (omap::update k v m)))
           (or (equal y v) (set::in y (omap::values m))))
  :induct (omap::values m)
  :expand ((omap::values (omap::update k v m)))
  :enable omap::values)

(defruled in-values-when-in-values-of-update
  (implies (and (set::in y (omap::values (omap::update k v m)))
                (not (equal y v)))
           (set::in y (omap::values m)))
  :use in-of-values-of-update)

(defruled subset-values-of-update
  :short "Updating a key can only add the new value to the set of values."
  (set::subset (omap::values (omap::update k v m))
               (set::insert v (omap::values m)))
  :enable (set::pick-a-point-subset-strategy
           in-values-when-in-values-of-update))

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
