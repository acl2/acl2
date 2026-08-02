; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/generic-typed" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "map-defs")
(include-book "keys-defs")
(include-book "values-defs")
(include-book "in-defs")
(include-book "lookup-defs")
(include-book "rlookup-defs")
(include-book "min-max-defs")
(include-book "update-defs")
(include-book "update-star-defs")
(include-book "delete-defs")
(include-book "restrict-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))

(local (include-book "map"))
(local (include-book "keys"))
(local (include-book "values"))
(local (include-book "in"))
(local (include-book "lookup"))
(local (include-book "rlookup"))
(local (include-book "min-max"))
(local (include-book "update"))
(local (include-book "update-star"))
(local (include-book "delete"))
(local (include-book "restrict"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A typed treemap is one whose key treeset and value treeset each satisfy an
;; all-elements predicate, so the generic machinery is @(see treeset)'s own,
;; applied to @(tsee keys) and @(tsee values). Nothing here introduces a new
;; stub: each law below constrains one projection through the one generic
;; predicate, and a use with distinct key and value predicates instantiates
;; the laws for each projection separately.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The key treeset. Its bridges are exact -- @(tsee keys) commutes with every
;; operation -- so these read straight off the treeset laws.

(defrule genericp-when-set-all-genericp-of-keys-and-in
  (implies (and (treeset::set-all-genericp (keys map))
                (in k map))
           (treeset::genericp k)))

(defrule set-all-genericp-of-keys-of-update
  (equal (treeset::set-all-genericp (keys (update k v map)))
         (and (treeset::genericp k)
              (treeset::set-all-genericp (keys (delete k map)))))
  :cases ((treeset::in k (keys map)))
  :use (:instance treeset::set-all-genericp-of-insert
                  (treeset::x k)
                  (treeset::set (treeset::delete k (keys map))))
  :enable acl2::equal-of-booleans-cheap
  :disable treeset::set-all-genericp-of-insert)

(defrule set-all-genericp-of-keys-of-delete
  (implies (treeset::set-all-genericp (keys map))
           (treeset::set-all-genericp (keys (delete k map)))))

(defrule set-all-genericp-of-keys-of-restrict
  (implies (treeset::set-all-genericp (keys map))
           (treeset::set-all-genericp (keys (restrict s map))))
  :use (:instance treeset::set-all-genericp-when-subset-and-set-all-genericp
                  (treeset::x (treeset::intersect s (keys map)))
                  (treeset::y (keys map)))
  :disable treeset::set-all-genericp-when-subset-and-set-all-genericp)

(defrule set-all-genericp-of-keys-of-update*
  (equal (treeset::set-all-genericp (keys (update* m1 m2)))
         (and (treeset::set-all-genericp (keys m1))
              (treeset::set-all-genericp (keys m2)))))

(defrule genericp-of-min-key-when-set-all-genericp-of-keys
  (implies (and (treeset::set-all-genericp (keys map))
                (not (emptyp map)))
           (treeset::genericp (min-key map))))

(defrule genericp-of-max-key-when-set-all-genericp-of-keys
  (implies (and (treeset::set-all-genericp (keys map))
                (not (emptyp map)))
           (treeset::genericp (max-key map))))

(defrule genericp-of-head-key-when-set-all-genericp-of-keys
  (implies (and (treeset::set-all-genericp (keys map))
                (not (emptyp map)))
           (treeset::genericp (head-key map))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The value treeset. There are no exact bridges here: an operation removes a
;; value from the value treeset only when no surviving key shares it. What
;; does hold is membership -- each proof picks the witness key with @(tsee
;; rlookup) -- and from membership, containment; and containment is all an
;; all-elements predicate needs.

(defrule in-of-values-of-delete
  (implies (treeset::in v (values (delete k map)))
           (treeset::in v (values map)))
  :use ((:instance treeset::in-of-head
                   (treeset::set (rlookup v (delete k map))))
        (:instance in-of-rlookup
                   (key (treeset::head (rlookup v (delete k map))))
                   (val v)
                   (map (delete k map)))
        (:instance in-of-lookup-and-values
                   (key (treeset::head (rlookup v (delete k map))))
                   (default nil)
                   (map map)))
  :disable (treeset::in-of-head
            in-of-rlookup
            in-of-lookup-and-values))

(defrule in-of-values-of-restrict
  (implies (treeset::in v (values (restrict s map)))
           (treeset::in v (values map)))
  :use ((:instance treeset::in-of-head
                   (treeset::set (rlookup v (restrict s map))))
        (:instance in-of-rlookup
                   (key (treeset::head (rlookup v (restrict s map))))
                   (val v)
                   (map (restrict s map)))
        (:instance in-of-lookup-and-values
                   (key (treeset::head (rlookup v (restrict s map))))
                   (default nil)
                   (map map)))
  :disable (treeset::in-of-head
            in-of-rlookup
            in-of-lookup-and-values))

(defrule in-of-values-of-update
  (implies (and (treeset::in v0 (values (update k v map)))
                (not (equal v0 v)))
           (treeset::in v0 (values map)))
  :use ((:instance treeset::in-of-head
                   (treeset::set (rlookup v0 (update k v map))))
        (:instance in-of-rlookup
                   (key (treeset::head (rlookup v0 (update k v map))))
                   (val v0)
                   (map (update k v map)))
        (:instance in-of-lookup-and-values
                   (key (treeset::head (rlookup v0 (update k v map))))
                   (default nil)
                   (map map)))
  :disable (treeset::in-of-head
            in-of-rlookup
            in-of-lookup-and-values))

(defrule in-of-values-of-update*
  (implies (and (treeset::in v (values (update* m1 m2)))
                (not (treeset::in v (values m1))))
           (treeset::in v (values m2)))
  :use ((:instance treeset::in-of-head
                   (treeset::set (rlookup v (update* m1 m2))))
        (:instance in-of-rlookup
                   (key (treeset::head (rlookup v (update* m1 m2))))
                   (val v)
                   (map (update* m1 m2)))
        (:instance in-of-lookup-and-values
                   (key (treeset::head (rlookup v (update* m1 m2))))
                   (default nil)
                   (map m1))
        (:instance in-of-lookup-and-values
                   (key (treeset::head (rlookup v (update* m1 m2))))
                   (default nil)
                   (map m2)))
  :disable (treeset::in-of-head
            in-of-rlookup
            in-of-lookup-and-values))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-values-of-delete
  (treeset::subset (values (delete k map))
                   (values map))
  :hints (("Goal" :in-theory (enable* treeset::pick-a-point))))

(defrule subset-of-values-of-restrict
  (treeset::subset (values (restrict s map))
                   (values map))
  :hints (("Goal" :in-theory (enable* treeset::pick-a-point))))

(defrule subset-of-values-of-update
  (treeset::subset (values (update k v map))
                   (treeset::insert v (values map)))
  :hints (("Goal" :in-theory (enable* treeset::pick-a-point))))

(defrule subset-of-values-of-update*
  (treeset::subset (values (update* m1 m2))
                   (treeset::union (values m1) (values m2)))
  :hints (("Goal" :in-theory (enable* treeset::pick-a-point))))

;;;;;;;;;;;;;;;;;;;;

(defrule genericp-of-lookup-when-set-all-genericp-of-values
  (implies (and (treeset::set-all-genericp (values map))
                (in k map))
           (treeset::genericp (lookup k map))))

(defrule set-all-genericp-of-values-of-delete
  (implies (treeset::set-all-genericp (values map))
           (treeset::set-all-genericp (values (delete k map))))
  :use (:instance treeset::set-all-genericp-when-subset-and-set-all-genericp
                  (treeset::x (values (delete k map)))
                  (treeset::y (values map)))
  :disable treeset::set-all-genericp-when-subset-and-set-all-genericp)

(defrule set-all-genericp-of-values-of-restrict
  (implies (treeset::set-all-genericp (values map))
           (treeset::set-all-genericp (values (restrict s map))))
  :use (:instance treeset::set-all-genericp-when-subset-and-set-all-genericp
                  (treeset::x (values (restrict s map)))
                  (treeset::y (values map)))
  :disable treeset::set-all-genericp-when-subset-and-set-all-genericp)

(defrule set-all-genericp-of-values-of-update
  (implies (and (treeset::genericp v)
                (treeset::set-all-genericp (values map)))
           (treeset::set-all-genericp (values (update k v map))))
  :use (:instance treeset::set-all-genericp-when-subset-and-set-all-genericp
                  (treeset::x (values (update k v map)))
                  (treeset::y (treeset::insert v (values map))))
  :disable treeset::set-all-genericp-when-subset-and-set-all-genericp)

(defrule set-all-genericp-of-values-of-update*
  (implies (and (treeset::set-all-genericp (values m1))
                (treeset::set-all-genericp (values m2)))
           (treeset::set-all-genericp (values (update* m1 m2))))
  :use (:instance treeset::set-all-genericp-when-subset-and-set-all-genericp
                  (treeset::x (values (update* m1 m2)))
                  (treeset::y (treeset::union (values m1) (values m2))))
  :disable treeset::set-all-genericp-when-subset-and-set-all-genericp)

(defrule genericp-of-min-val-when-set-all-genericp-of-values
  (implies (and (treeset::set-all-genericp (values map))
                (not (emptyp map)))
           (treeset::genericp (min-val map))))

(defrule genericp-of-max-val-when-set-all-genericp-of-values
  (implies (and (treeset::set-all-genericp (values map))
                (not (emptyp map)))
           (treeset::genericp (max-val map))))

(defrule genericp-of-head-val-when-set-all-genericp-of-values
  (implies (and (treeset::set-all-genericp (values map))
                (not (emptyp map)))
           (treeset::genericp (head-val map))))
