; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/min-max-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)

(include-book "kestrel/data/tmap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/join-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/split-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/values-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/min-max-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/update-star-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/restrict-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))

(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/internal/keys" :dir :system))
(local (include-book "kestrel/data/tmap/internal/join" :dir :system))
(local (include-book "kestrel/data/tmap/internal/values" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/values" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/min-max" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/update-star" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/restrict" :dir :system))
(local (include-book "kestrel/data/tmap/generic-typed" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A @(see tbag) is a @(see tmap::tmap) from element to multiplicity,
;; and an element absent from the bag is one absent from the map rather than
;; one bound to zero. The representation invariant is therefore that every
;; value in the map is a positive integer, which is what this book defines.
;;
;; Nothing here is proved from scratch: the check is an instance of @(see
;; tset::generic-typed)'s all-elements predicate at @(tsee posp), and each
;; law below is the corresponding generic law functionally instantiated. The
;; two projections of that generic theory used here are the tset one, which
;; states the check over a value set, and the tmap one, which carries it
;; through the map operations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The check over a value @(see acl2::tset), by repeatedly taking the
;; minimum. This is the shape @(tsee tset::set-all-genericp) recurses in, so
;; it is the function the generic laws are instantiated at.

(define set-all-posp ((set tset::setp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tset::emptyp set)
      (and (posp (tset::min set))
           (set-all-posp (tset::delete (tset::min set) set))))
  :measure (tset::cardinality set)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min))))

;;;;;;;;;;;;;;;;;;;;

(defrule set-all-posp-when-tset-equiv-congruence
  (implies (tset::equiv set0 set1)
           (equal (set-all-posp set0)
                  (set-all-posp set1)))
  :rule-classes :congruence
  :use (:instance
         (:functional-instance tset::set-all-genericp-when-equiv-congruence
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::set0 set0)
         (tset::set1 set1))
  :enable set-all-posp)

(defruled set-all-posp-when-emptyp
  (implies (tset::emptyp set)
           (set-all-posp set))
  :enable set-all-posp)

(defrule set-all-posp-when-emptyp-cheap
  (implies (tset::emptyp set)
           (set-all-posp set))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-all-posp-when-emptyp)

(defrule set-all-posp-of-empty
  (set-all-posp (tset::empty))
  :enable set-all-posp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-when-set-all-posp-and-in
  (implies (and (set-all-posp set)
                (tset::in x set))
           (posp x))
  :use (:instance
         (:functional-instance tset::genericp-when-set-all-genericp-and-in
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::x x)
         (tset::set set))
  :enable set-all-posp)

(defrule set-all-posp-of-insert
  (equal (set-all-posp (tset::insert x set))
         (and (posp x)
              (set-all-posp set)))
  :use (:instance
         (:functional-instance tset::set-all-genericp-of-insert
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::x x)
         (tset::set set))
  :enable set-all-posp)

(defrule set-all-posp-of-delete
  (implies (set-all-posp set)
           (set-all-posp (tset::delete x set)))
  :use (:instance
         (:functional-instance tset::set-all-genericp-of-delete
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::x x)
         (tset::set set))
  :enable set-all-posp)

;; The peel step of the min/delete recursion, for an arbitrary member.

(defruled set-all-posp-of-delete-when-in
  (implies (tset::in x set)
           (equal (set-all-posp set)
                  (and (posp x)
                       (set-all-posp (tset::delete x set)))))
  :use (:instance
         (:functional-instance tset::set-all-genericp-of-delete-when-in
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::x x)
         (tset::set set))
  :enable set-all-posp)

(defrule set-all-posp-when-subset-and-set-all-posp
  (implies (and (tset::subset x y)
                (set-all-posp y))
           (set-all-posp x))
  :use (:instance
         (:functional-instance
           tset::set-all-genericp-when-subset-and-set-all-genericp
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::x x)
         (tset::y y))
  :enable set-all-posp)

;; The same fact with the hypotheses exchanged, left disabled for the reason
;; given at @(tsee tset::set-all-genericp-when-set-all-genericp-and-subset).

(defruled set-all-posp-when-set-all-posp-and-subset
  (implies (and (set-all-posp y)
                (tset::subset x y))
           (set-all-posp x))
  :by set-all-posp-when-subset-and-set-all-posp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-of-min-when-set-all-posp
  (implies (and (set-all-posp set)
                (not (tset::emptyp set)))
           (posp (tset::min set)))
  :use (:instance
         (:functional-instance
           tset::genericp-of-min-under-iff-when-set-all-genericp
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::set set))
  :enable set-all-posp)

(defrule posp-of-max-when-set-all-posp
  (implies (and (set-all-posp set)
                (not (tset::emptyp set)))
           (posp (tset::max set)))
  :use (:instance
         (:functional-instance
           tset::genericp-of-max-under-iff-when-set-all-genericp
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::set set))
  :enable set-all-posp)

(defrule posp-of-head-when-set-all-posp
  (implies (and (set-all-posp set)
                (not (tset::emptyp set)))
           (posp (tset::head set)))
  :use (:instance
         (:functional-instance
           tset::genericp-of-head-under-iff-when-set-all-genericp
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tset::set set))
  :enable set-all-posp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same check run as a single walk over the map's own tree, reading the
;; value at every node. This builds no value tset, so it is what the
;; recognizer executes.

(define tree-all-vals-posp ((tree tmap::treep))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (or (tmap::tree-empty-p tree)
      (and (posp (tmap::tree-element->val (tmap::tree->head tree)))
           (tree-all-vals-posp (tmap::tree->left tree))
           (tree-all-vals-posp (tmap::tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-vals-posp-becomes-set-all-posp-of-values
  (implies (tmap::mapp map)
           (equal (tree-all-vals-posp map)
                  (set-all-posp (tmap::values (double-rewrite map)))))
  :use (:instance
         (:functional-instance
           tmap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp)
           (tmap::tree-all-vals-genericp tree-all-vals-posp))
         (tmap::map map))
  :enable (set-all-posp
           tree-all-vals-posp))

(defrule tree-all-vals-posp-of-tree-split.left-when-tree-all-vals-posp
  (implies (tree-all-vals-posp tree)
           (tree-all-vals-posp (mv-nth 1 (tmap::tree-split key tree))))
  :use (:instance
         (:functional-instance
           tmap::tree-all-vals-genericp-of-tree-split.left-when-tree-all-vals-genericp
           (tset::genericp posp)
           (tmap::tree-all-vals-genericp tree-all-vals-posp))
         (tmap::tree tree)
         (tmap::key key))
  :enable tree-all-vals-posp)

(defrule tree-all-vals-posp-of-tree-split.right-when-tree-all-vals-posp
  (implies (tree-all-vals-posp tree)
           (tree-all-vals-posp (mv-nth 2 (tmap::tree-split key tree))))
  :use (:instance
         (:functional-instance
           tmap::tree-all-vals-genericp-of-tree-split.right-when-tree-all-vals-genericp
           (tset::genericp posp)
           (tmap::tree-all-vals-genericp tree-all-vals-posp))
         (tmap::tree tree)
         (tmap::key key))
  :enable tree-all-vals-posp)

(defrule posp-of-cdr-of-tree-search-assoc-when-tree-all-vals-posp
  (implies (and (tree-all-vals-posp tree)
                (tmap::tree-search-assoc key tree))
           (posp (cdr (tmap::tree-search-assoc key tree))))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-cdr-of-tree-search-assoc-when-tree-all-vals-genericp
           (tset::genericp posp)
           (tmap::tree-all-vals-genericp tree-all-vals-posp))
         (tmap::tree tree)
         (tmap::key key))
  :enable tree-all-vals-posp)

(defrule posp-of-tree-lookup-when-tree-all-vals-posp
  (implies (and (tree-all-vals-posp tree)
                (tset::in key (tmap::tree-key-set (double-rewrite tree))))
           (posp (tmap::tree-lookup key tree)))
  :rule-classes
  (:rewrite
   (:linear :corollary
            (implies (and (tree-all-vals-posp tree)
                          (tset::in key (tmap::tree-key-set
                                          (double-rewrite tree))))
                     (< 0 (tmap::tree-lookup key tree)))))
  :induct t
  :enable (tmap::tree-lookup
           tmap::in-of-tree-key-set-when-not-tree-empty-p
           tree-all-vals-posp))

(defrule tree-all-vals-posp-when-tree-equiv-congruence
  (implies (tmap::tree-equiv tree0 tree1)
           (equal (tree-all-vals-posp tree0)
                  (tree-all-vals-posp tree1)))
  :rule-classes :congruence
  :use (:instance
         (:functional-instance
           tmap::tree-all-vals-genericp-when-tree-equiv-congruence
           (tset::genericp posp)
           (tmap::tree-all-vals-genericp tree-all-vals-posp))
         (tmap::tree0 tree0)
         (tmap::tree1 tree1))
  :enable tree-all-vals-posp)

(defrule tree-all-vals-posp-of-tree-join
  (implies (and (tree-all-vals-posp left)
                (tree-all-vals-posp right))
           (tree-all-vals-posp (tmap::tree-join left right)))
  :induct (tmap::tree-join left right)
  :enable (tmap::tree-join
           tree-all-vals-posp))

(defrule tree-all-vals-posp-of-tree-join-at
  (implies (and (tree-all-vals-posp left)
                (tree-all-vals-posp right))
           (tree-all-vals-posp (tmap::tree-join-at split left right)))
  :enable tmap::tree-join-at)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The recognizer itself: every value of the map is a positive integer. The
;; logical form is the tset check over @(tsee tmap::values), which is
;; where the generic laws land; the walk above is the execution.
;;
;; Time complexity: @($O(n)$).

(define map-values-all-posp ((map tmap::mapp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  (mbe :logic (set-all-posp (tmap::values map))
       :exec (tree-all-vals-posp map))
  :guard-hints
  (("Goal" :in-theory (enable tree-all-vals-posp-becomes-set-all-posp-of-values
                              tmap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-posp-when-tmap-equiv-congruence
  (implies (tmap::equiv map0 map1)
           (equal (map-values-all-posp map0)
                  (map-values-all-posp map1)))
  :rule-classes :congruence
  :enable map-values-all-posp)

(defrule tree-all-vals-posp-when-map-values-all-posp
  (implies (and (tmap::mapp map)
                (map-values-all-posp (double-rewrite map)))
           (tree-all-vals-posp map))
  :enable (map-values-all-posp
           tree-all-vals-posp-becomes-set-all-posp-of-values))

(defruled map-values-all-posp-when-tree-all-vals-posp
  (implies (and (tmap::mapp map)
                (tree-all-vals-posp map))
           (map-values-all-posp map))
  :enable (map-values-all-posp
           tree-all-vals-posp-becomes-set-all-posp-of-values))

(defruled map-values-all-posp-when-emptyp
  (implies (tmap::emptyp map)
           (map-values-all-posp map))
  :enable (map-values-all-posp
           set-all-posp-when-emptyp))

(defrule map-values-all-posp-when-emptyp-cheap
  (implies (tmap::emptyp map)
           (map-values-all-posp map))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-posp-when-emptyp)

(defrule map-values-all-posp-of-empty
  (map-values-all-posp (tmap::empty))
  :enable map-values-all-posp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-of-lookup-when-map-values-all-posp
  (implies (and (map-values-all-posp map)
                (tmap::in k map))
           (posp (tmap::lookup k map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-lookup-when-set-all-genericp-of-values
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-posp
           set-all-posp))

;; The weaker consequence, for a caller reading 0 at an absent key: since no
;; key holds 0, that reading is a natural whether or not the key is present,
;; and the membership hypothesis drops away.

(defrule natp-of-lookup-with-default-0-when-map-values-all-posp
  (implies (map-values-all-posp map)
           (natp (tmap::lookup k map :default 0)))
  :use posp-of-lookup-when-map-values-all-posp
  :disable posp-of-lookup-when-map-values-all-posp
  :enable tmap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-posp-of-update
  (equal (map-values-all-posp (tmap::update k v map))
         (and (posp v)
              (map-values-all-posp (tmap::delete k map))))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-update
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map)
         (tmap::k k)
         (tmap::v v))
  :enable (map-values-all-posp
           set-all-posp))

(defrule map-values-all-posp-of-delete
  (implies (map-values-all-posp map)
           (map-values-all-posp (tmap::delete k map)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-delete
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-posp
           set-all-posp))

(defrule map-values-all-posp-of-update*
  (implies (and (map-values-all-posp m1)
                (map-values-all-posp m2))
           (map-values-all-posp (tmap::update* m1 m2)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-update*
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::m1 m1)
         (tmap::m2 m2))
  :enable (map-values-all-posp
           set-all-posp))

(defrule map-values-all-posp-of-restrict
  (implies (map-values-all-posp map)
           (map-values-all-posp (tmap::restrict s map)))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-restrict
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map)
         (tmap::s s))
  :enable (map-values-all-posp
           set-all-posp))

;; The peel step of a min/delete recursion over the map: peeling a bound key
;; removes exactly its multiplicity from view.

(defruled map-values-all-posp-of-delete-when-in
  (implies (tset::in k (tmap::keys map))
           (equal (map-values-all-posp map)
                  (and (posp (tmap::lookup k map))
                       (map-values-all-posp (tmap::delete k map)))))
  :use (:instance
         (:functional-instance
           tmap::set-all-genericp-of-values-of-delete-when-in
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map)
         (tmap::k k))
  :enable (map-values-all-posp
           set-all-posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-of-min-val-when-map-values-all-posp
  (implies (and (map-values-all-posp (double-rewrite map))
                (not (tmap::emptyp (double-rewrite map))))
           (posp (tmap::min-val map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-min-val-when-set-all-genericp-of-values
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map))
  :enable (map-values-all-posp
           set-all-posp))

(defrule posp-of-max-val-when-map-values-all-posp
  (implies (and (map-values-all-posp (double-rewrite map))
                (not (tmap::emptyp (double-rewrite map))))
           (posp (tmap::max-val map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-max-val-when-set-all-genericp-of-values
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map))
  :enable (map-values-all-posp
           set-all-posp))

(defrule posp-of-head-val-when-map-values-all-posp
  (implies (and (map-values-all-posp (double-rewrite map))
                (not (tmap::emptyp (double-rewrite map))))
           (posp (tmap::head-val map)))
  :use (:instance
         (:functional-instance
           tmap::genericp-of-head-val-when-set-all-genericp-of-values
           (tset::genericp posp)
           (tset::set-all-genericp set-all-posp))
         (tmap::map map))
  :enable (map-values-all-posp
           set-all-posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy map-values-all-posp-extra-rules
  '(set-all-posp-when-emptyp
    set-all-posp-of-delete-when-in
    set-all-posp-when-set-all-posp-and-subset
    tree-all-vals-posp-becomes-set-all-posp-of-values
    map-values-all-posp-when-emptyp
    map-values-all-posp-of-delete-when-in))
