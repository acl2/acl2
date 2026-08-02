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

(include-book "internal/tree-defs")
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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/intersect" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/keys"))
(local (include-book "internal/values"))
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
  :enable treeset::set-all-genericp-when-set-all-genericp-and-subset)

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
;; does hold is membership, and one lemma carries the whole witness argument:
;; a value of a submap is a value of the map, since some key produces it there
;; and the same key produces it in the map. @(tsee rlookup) names the witness;
;; this is the one place it is needed, and the @(tsee delete) and @(tsee
;; restrict) bridges are its instances through @(tsee submap-of-delete) and
;; @(tsee submap-of-restrict).

(defrule in-of-values-when-submap
  (implies (and (treeset::in v (values m1))
                (submap m1 m2))
           (treeset::in v (values m2)))
  :use ((:instance treeset::in-of-head
                   (treeset::set (rlookup v m1)))
        (:instance lookup-when-in-of-keys-and-submap
                   (key (treeset::head (rlookup v m1)))
                   (default nil)
                   (x m1)
                   (y m2))
        (:instance in-of-lookup-and-values
                   (key (treeset::head (rlookup v m1)))
                   (default nil)
                   (map m2)))
  :disable (treeset::in-of-head
            lookup-when-in-of-keys-and-submap
            in-of-lookup-and-values))

;; An update may bind a fresh value, so its bridges carry the one case the
;; submap lemma cannot: the witness argument repeats, relative to the updated
;; map.

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
  :enable treeset::set-all-genericp-when-set-all-genericp-and-subset)

(defrule set-all-genericp-of-values-of-restrict
  (implies (treeset::set-all-genericp (values map))
           (treeset::set-all-genericp (values (restrict s map))))
  :enable treeset::set-all-genericp-when-set-all-genericp-and-subset)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Structural folds over the map's own tree, one per projection. Each is a
;; single walk reading its component at every node; neither builds a treeset.
;; The bridges below let an executable recognizer conjoining the two folds
;; meet the projection laws above, one functional instance per fold.

(define tree-all-keys-genericp ((tree treep))
  (or (tree-empty-p tree)
      (and (treeset::genericp (tree-element->key (tree->head tree)))
           (tree-all-keys-genericp (tree->left tree))
           (tree-all-keys-genericp (tree->right tree)))))

(define tree-all-vals-genericp ((tree treep))
  (or (tree-empty-p tree)
      (and (treeset::genericp (tree-element->val (tree->head tree)))
           (tree-all-vals-genericp (tree->left tree))
           (tree-all-vals-genericp (tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-keys-genericp-becomes-set-all-genericp-of-tree-key-set
  (equal (tree-all-keys-genericp tree)
         (treeset::set-all-genericp (tree-key-set tree)))
  :induct t
  :enable (tree-all-keys-genericp
           tree-key-set))

(defruled tree-all-vals-genericp-becomes-set-all-genericp-of-tree-val-set
  (equal (tree-all-vals-genericp tree)
         (treeset::set-all-genericp (tree-val-set tree)))
  :induct t
  :enable (tree-all-vals-genericp
           tree-val-set))

(defruled tree-all-keys-genericp-becomes-set-all-genericp-of-keys
  (implies (mapp map)
           (equal (tree-all-keys-genericp map)
                  (treeset::set-all-genericp (keys map))))
  :enable (keys
           tree-all-keys-genericp-becomes-set-all-genericp-of-tree-key-set))

(defruled tree-all-vals-genericp-becomes-set-all-genericp-of-values
  (implies (mapp map)
           (equal (tree-all-vals-genericp map)
                  (treeset::set-all-genericp (values map))))
  :enable (values
           tree-all-vals-genericp-becomes-set-all-genericp-of-tree-val-set))
