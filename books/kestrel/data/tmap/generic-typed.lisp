; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/generic-typed" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tset/union-defs" :dir :system)

(include-book "internal/tree-defs")
(include-book "internal/lookup-defs")
(include-book "internal/split-defs")
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
(include-book "submap-defs")
(include-book "iter-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/values"))
(local (include-book "internal/lookup"))
(local (include-book "internal/rotate"))
(local (include-book "internal/split"))
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
(local (include-book "submap"))
(local (include-book "iter"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A typed tmap is one whose key tset and value tset each satisfy an
;; all-elements predicate, so the generic machinery is @(see tset)'s own,
;; applied to @(tsee keys) and @(tsee values). Nothing here introduces a new
;; stub: each law below constrains one projection through the one generic
;; predicate, and a use with distinct key and value predicates instantiates
;; the laws for each projection separately.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The key tset. Its bridges are exact -- @(tsee keys) commutes with every
;; operation -- so these read straight off the tset laws.

(defrule genericp-when-set-all-genericp-of-keys-and-in
  (implies (and (tset::set-all-genericp (keys map))
                (in k map))
           (tset::genericp k)))

;; The peel step of a min/delete recursion over the map, keys side, for an
;; arbitrary bound key.
(defruled set-all-genericp-of-keys-of-delete-when-in
  (implies (tset::in k (keys map))
           (equal (tset::set-all-genericp (keys map))
                  (and (tset::genericp k)
                       (tset::set-all-genericp (keys (delete k map))))))
  :use ((:instance tset::set-all-genericp-of-delete-when-in
                   (tset::x k)
                   (tset::set (keys map)))))

(defrule set-all-genericp-of-keys-of-update
  (equal (tset::set-all-genericp (keys (update k v map)))
         (and (tset::genericp k)
              (tset::set-all-genericp (keys (delete k map)))))
  :use (:instance set-all-genericp-of-keys-of-delete-when-in
                  (map (update k v map)))
  :enable tset::in-of-insert)

(defrule set-all-genericp-of-keys-of-delete
  (implies (tset::set-all-genericp (keys map))
           (tset::set-all-genericp (keys (delete k map)))))

(defrule set-all-genericp-of-keys-of-restrict
  (implies (tset::set-all-genericp (keys map))
           (tset::set-all-genericp (keys (restrict s map))))
  :enable tset::set-all-genericp-when-set-all-genericp-and-subset)

(defrule set-all-genericp-of-keys-of-update*
  (equal (tset::set-all-genericp (keys (update* m1 m2)))
         (and (tset::set-all-genericp (keys m1))
              (tset::set-all-genericp (keys m2)))))

(defrule genericp-of-min-key-when-set-all-genericp-of-keys
  (implies (and (tset::set-all-genericp (keys map))
                (not (emptyp map)))
           (tset::genericp (min-key map))))

(defrule genericp-of-max-key-when-set-all-genericp-of-keys
  (implies (and (tset::set-all-genericp (keys map))
                (not (emptyp map)))
           (tset::genericp (max-key map))))

(defrule genericp-of-head-key-when-set-all-genericp-of-keys
  (implies (and (tset::set-all-genericp (keys map))
                (not (emptyp map)))
           (tset::genericp (head-key map))))

;; The key an @(see iterator) is at, for a walk over a map whose keys are all
;; generic. An iterator carries no key type, so this is what discharges the
;; guard of a typed loop at @(tsee entry-key); @('deftmap') instantiates it.

(defrule genericp-of-entry-key-when-set-all-genericp-of-keys
  (implies (and (tset::set-all-genericp (keys (from-iter iter)))
                (has-valuep iter))
           (tset::genericp (entry-key iter))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The value tset. There are no exact bridges here: an operation removes a
;; value from the value tset only when no surviving key shares it. What
;; does hold is membership, and one lemma carries the whole witness argument:
;; a value of a submap is a value of the map, since some key produces it there
;; and the same key produces it in the map. @(tsee rlookup) names the witness;
;; this is the one place it is needed, and the @(tsee delete) and @(tsee
;; restrict) bridges are its instances through @(tsee submap-of-delete) and
;; @(tsee submap-of-restrict).

(defrule in-of-values-when-submap
  (implies (and (tset::in v (values m1))
                (submap m1 m2))
           (tset::in v (values m2)))
  :use ((:instance tset::in-of-head
                   (tset::set (rlookup v m1)))
        (:instance lookup-when-in-of-keys-and-submap
                   (key (tset::head (rlookup v m1)))
                   (default nil)
                   (x m1)
                   (y m2))
        (:instance in-of-lookup-and-values
                   (key (tset::head (rlookup v m1)))
                   (default nil)
                   (map m2)))
  :disable (tset::in-of-head
            lookup-when-in-of-keys-and-submap
            in-of-lookup-and-values))

;; An update may bind a fresh value, so its bridges carry the one case the
;; submap lemma cannot: the witness argument repeats, relative to the updated
;; map.

(defrule in-of-values-of-update
  (implies (and (tset::in v0 (values (update k v map)))
                (not (equal v0 v)))
           (tset::in v0 (values map)))
  :use ((:instance tset::in-of-head
                   (tset::set (rlookup v0 (update k v map))))
        (:instance in-of-rlookup
                   (key (tset::head (rlookup v0 (update k v map))))
                   (val v0)
                   (map (update k v map)))
        (:instance in-of-lookup-and-values
                   (key (tset::head (rlookup v0 (update k v map))))
                   (default nil)
                   (map map)))
  :disable (tset::in-of-head
            in-of-rlookup
            in-of-lookup-and-values))

(defrule in-of-values-of-update*
  (implies (and (tset::in v (values (update* m1 m2)))
                (not (tset::in v (values m1))))
           (tset::in v (values m2)))
  :use ((:instance tset::in-of-head
                   (tset::set (rlookup v (update* m1 m2))))
        (:instance in-of-rlookup
                   (key (tset::head (rlookup v (update* m1 m2))))
                   (val v)
                   (map (update* m1 m2)))
        (:instance in-of-lookup-and-values
                   (key (tset::head (rlookup v (update* m1 m2))))
                   (default nil)
                   (map m1))
        (:instance in-of-lookup-and-values
                   (key (tset::head (rlookup v (update* m1 m2))))
                   (default nil)
                   (map m2)))
  :disable (tset::in-of-head
            in-of-rlookup
            in-of-lookup-and-values))

;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-values-of-delete
  (tset::subset (values (delete k map))
                (values map))
  :enable tset::pick-a-point)

(defrule subset-of-values-of-restrict
  (tset::subset (values (restrict s map))
                (values map))
  :enable tset::pick-a-point)

(defrule subset-of-values-of-update
  (tset::subset (values (update k v map))
                (tset::insert v (values map)))
  :enable tset::pick-a-point)

(defrule subset-of-values-of-update*
  (tset::subset (values (update* m1 m2))
                (tset::union (values m1) (values m2)))
  :enable tset::pick-a-point)

;;;;;;;;;;;;;;;;;;;;

(defrule genericp-of-lookup-when-set-all-genericp-of-values
  (implies (and (tset::set-all-genericp (values map))
                (in k map))
           (tset::genericp (lookup k map))))

(defrule set-all-genericp-of-values-of-delete
  (implies (tset::set-all-genericp (values map))
           (tset::set-all-genericp (values (delete k map))))
  :enable tset::set-all-genericp-when-set-all-genericp-and-subset)

(defrule set-all-genericp-of-values-of-restrict
  (implies (tset::set-all-genericp (values map))
           (tset::set-all-genericp (values (restrict s map))))
  :enable tset::set-all-genericp-when-set-all-genericp-and-subset)

(defruledl set-all-genericp-of-values-of-update-weak
  (implies (and (tset::genericp v)
                (tset::set-all-genericp (values map)))
           (tset::set-all-genericp (values (update k v map))))
  :use (:instance tset::set-all-genericp-when-subset-and-set-all-genericp
                  (tset::x (values (update k v map)))
                  (tset::y (tset::insert v (values map))))
  :disable tset::set-all-genericp-when-subset-and-set-all-genericp)

;; The peel step of a min/delete recursion over the map, values side: peeling
;; a bound key removes exactly its value from view. The reverse direction is
;; the put-back argument, updating the key with its own value.
(defruled set-all-genericp-of-values-of-delete-when-in
  (implies (tset::in k (keys map))
           (equal (tset::set-all-genericp (values map))
                  (and (tset::genericp (lookup k map))
                       (tset::set-all-genericp (values (delete k map))))))
  :use ((:instance set-all-genericp-of-values-of-update-weak
                   (v (lookup k map))
                   (map (delete k map))))
  :enable (update-of-delete-same
           update-redundant-cheap
           fix-under-equiv))

(defrule set-all-genericp-of-values-of-update
  (equal (tset::set-all-genericp (values (update k v map)))
         (and (tset::genericp v)
              (tset::set-all-genericp (values (delete k map)))))
  :use ((:instance set-all-genericp-of-values-of-delete-when-in
                   (map (update k v map))))
  :enable tset::in-of-insert)

(defrule set-all-genericp-of-values-of-update*
  (implies (and (tset::set-all-genericp (values m1))
                (tset::set-all-genericp (values m2)))
           (tset::set-all-genericp (values (update* m1 m2))))
  :use (:instance tset::set-all-genericp-when-subset-and-set-all-genericp
                  (tset::x (values (update* m1 m2)))
                  (tset::y (tset::union (values m1) (values m2))))
  :disable tset::set-all-genericp-when-subset-and-set-all-genericp)

(defrule genericp-of-min-val-when-set-all-genericp-of-values
  (implies (and (tset::set-all-genericp (values map))
                (not (emptyp map)))
           (tset::genericp (min-val map))))

(defrule genericp-of-max-val-when-set-all-genericp-of-values
  (implies (and (tset::set-all-genericp (values map))
                (not (emptyp map)))
           (tset::genericp (max-val map))))

(defrule genericp-of-head-val-when-set-all-genericp-of-values
  (implies (and (tset::set-all-genericp (values map))
                (not (emptyp map)))
           (tset::genericp (head-val map))))

;; The value an @(see iterator) is at, for a walk over a map whose values are
;; all generic. The mirror of the key rule above, for @(tsee entry-val).

(defrule genericp-of-entry-val-when-set-all-genericp-of-values
  (implies (and (tset::set-all-genericp (values (from-iter iter)))
                (has-valuep iter))
           (tset::genericp (entry-val iter)))
  :use (:instance genericp-of-lookup-when-set-all-genericp-of-values
                  (k (entry-key iter))
                  (map (from-iter iter)))
  :disable genericp-of-lookup-when-set-all-genericp-of-values)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Structural folds over the map's own tree, one per projection. Each is a
;; single walk reading its component at every node; neither builds a tset.
;; The bridges below let an executable recognizer conjoining the two folds
;; meet the projection laws above, one functional instance per fold.

(define tree-all-keys-genericp ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p tree)
      (and (tset::genericp (tree-element->key (tree->head tree)))
           (tree-all-keys-genericp (tree->left tree))
           (tree-all-keys-genericp (tree->right tree)))))

(define tree-all-vals-genericp ((tree treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tree-empty-p tree)
      (and (tset::genericp (tree-element->val (tree->head tree)))
           (tree-all-vals-genericp (tree->left tree))
           (tree-all-vals-genericp (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-keys-genericp-becomes-set-all-genericp-of-tree-key-set
  (equal (tree-all-keys-genericp tree)
         (tset::set-all-genericp (tree-key-set tree)))
  :induct t
  :enable (tree-all-keys-genericp
           tree-key-set))

(defruled tree-all-vals-genericp-becomes-set-all-genericp-of-tree-val-set
  (equal (tree-all-vals-genericp tree)
         (tset::set-all-genericp (tree-val-set tree)))
  :induct t
  :enable (tree-all-vals-genericp
           tree-val-set))

(defruled tree-all-keys-genericp-becomes-set-all-genericp-of-keys
  (implies (mapp map)
           (equal (tree-all-keys-genericp map)
                  (tset::set-all-genericp (keys map))))
  :enable (keys
           tree-all-keys-genericp-becomes-set-all-genericp-of-tree-key-set))

(defruled tree-all-vals-genericp-becomes-set-all-genericp-of-values
  (implies (mapp map)
           (equal (tree-all-vals-genericp map)
                  (tset::set-all-genericp (values map))))
  :enable (values
           tree-all-vals-genericp-becomes-set-all-genericp-of-tree-val-set))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-vals-genericp-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-all-vals-genericp tree0)
                  (tree-all-vals-genericp tree1)))
  :rule-classes :congruence
  :expand ((tree-all-vals-genericp tree0)
           (tree-all-vals-genericp tree1)))

;; A split only rearranges the tree's nodes, and a search returns the value of
;; one of them, so neither escapes the value fold.

(defrule tree-all-vals-genericp-of-tree-split.left-when-tree-all-vals-genericp
  (implies (tree-all-vals-genericp tree)
           (tree-all-vals-genericp (mv-nth 1 (tree-split key tree))))
  :induct t
  :enable (tree-split
           tree-all-vals-genericp))

(defrule tree-all-vals-genericp-of-tree-split.right-when-tree-all-vals-genericp
  (implies (tree-all-vals-genericp tree)
           (tree-all-vals-genericp (mv-nth 2 (tree-split key tree))))
  :induct t
  :enable (tree-split
           tree-all-vals-genericp))

(defrule genericp-of-cdr-of-tree-search-assoc-when-tree-all-vals-genericp
  (implies (and (tree-all-vals-genericp tree)
                (tree-search-assoc key tree))
           (tset::genericp (cdr (tree-search-assoc key tree))))
  :induct t
  :enable (tree-search-assoc
           tree-all-vals-genericp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The fixer of a typed map, with tset::genericp standing for the type of
;; the whole map. @('deftmap') instantiates its laws for each fixer it
;; generates.

(define generic-fix (map)
  (if (tset::genericp map)
      map
    (empty)))

;;;;;;;;;;;;;;;;;;;;

(defrule submap-of-generic-fix
  (implies (submap map y)
           (submap (generic-fix map) y))
  :enable generic-fix)
