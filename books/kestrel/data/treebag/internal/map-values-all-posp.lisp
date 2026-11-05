; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)

(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/split-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/values-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/min-max-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/update-star-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)
(include-book "kestrel/data/treemap/restrict-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))

(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/values" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/values" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/update-star" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/restrict" :dir :system))
(local (include-book "kestrel/data/treemap/generic-typed" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A @(see treebag) is a @(see treemap::treemap) from element to multiplicity,
;; and an element absent from the bag is one absent from the map rather than
;; one bound to zero. The representation invariant is therefore that every
;; value in the map is a positive integer, which is what this book defines.
;;
;; Nothing here is proved from scratch: the check is an instance of @(see
;; treeset::generic-typed)'s all-elements predicate at @(tsee posp), and each
;; law below is the corresponding generic law functionally instantiated. The
;; two projections of that generic theory used here are the treeset one, which
;; states the check over a value set, and the treemap one, which carries it
;; through the map operations.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The check over a value @(see acl2::treeset), by repeatedly taking the
;; minimum. This is the shape @(tsee treeset::set-all-genericp) recurses in, so
;; it is the function the generic laws are instantiated at.

(define set-all-posp ((set treeset::setp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (or (treeset::emptyp set)
      (and (posp (treeset::min set))
           (set-all-posp (treeset::delete (treeset::min set) set))))
  :measure (treeset::cardinality set)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min))))

;;;;;;;;;;;;;;;;;;;;

(defrule set-all-posp-type-prescription
  (booleanp (set-all-posp set))
  :rule-classes ((:type-prescription :typed-term (set-all-posp set))))

(defrule set-all-posp-when-treeset-equiv-congruence
  (implies (treeset::equiv set0 set1)
           (equal (set-all-posp set0)
                  (set-all-posp set1)))
  :rule-classes :congruence
  :use (:instance
         (:functional-instance treeset::set-all-genericp-when-equiv-congruence
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::set0 set0)
         (treeset::set1 set1))
  :enable set-all-posp)

(defruled set-all-posp-when-emptyp
  (implies (treeset::emptyp set)
           (set-all-posp set))
  :enable set-all-posp)

(defrule set-all-posp-when-emptyp-cheap
  (implies (treeset::emptyp set)
           (set-all-posp set))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by set-all-posp-when-emptyp)

(defrule set-all-posp-of-empty
  (set-all-posp (treeset::empty))
  :enable set-all-posp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-when-set-all-posp-and-in
  (implies (and (set-all-posp set)
                (treeset::in x set))
           (posp x))
  :use (:instance
         (:functional-instance treeset::genericp-when-set-all-genericp-and-in
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::x x)
         (treeset::set set))
  :enable set-all-posp)

(defrule set-all-posp-of-insert
  (equal (set-all-posp (treeset::insert x set))
         (and (posp x)
              (set-all-posp set)))
  :use (:instance
         (:functional-instance treeset::set-all-genericp-of-insert
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::x x)
         (treeset::set set))
  :enable set-all-posp)

(defrule set-all-posp-of-delete
  (implies (set-all-posp set)
           (set-all-posp (treeset::delete x set)))
  :use (:instance
         (:functional-instance treeset::set-all-genericp-of-delete
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::x x)
         (treeset::set set))
  :enable set-all-posp)

;; The peel step of the min/delete recursion, for an arbitrary member.

(defruled set-all-posp-of-delete-when-in
  (implies (treeset::in x set)
           (equal (set-all-posp set)
                  (and (posp x)
                       (set-all-posp (treeset::delete x set)))))
  :use (:instance
         (:functional-instance treeset::set-all-genericp-of-delete-when-in
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::x x)
         (treeset::set set))
  :enable set-all-posp)

(defrule set-all-posp-when-subset-and-set-all-posp
  (implies (and (treeset::subset x y)
                (set-all-posp y))
           (set-all-posp x))
  :use (:instance
         (:functional-instance
           treeset::set-all-genericp-when-subset-and-set-all-genericp
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::x x)
         (treeset::y y))
  :enable set-all-posp)

;; The same fact with the hypotheses exchanged, left disabled for the reason
;; given at @(tsee treeset::set-all-genericp-when-set-all-genericp-and-subset).

(defruled set-all-posp-when-set-all-posp-and-subset
  (implies (and (set-all-posp y)
                (treeset::subset x y))
           (set-all-posp x))
  :by set-all-posp-when-subset-and-set-all-posp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-of-min-when-set-all-posp
  (implies (and (set-all-posp set)
                (not (treeset::emptyp set)))
           (posp (treeset::min set)))
  :use (:instance
         (:functional-instance
           treeset::genericp-of-min-under-iff-when-set-all-genericp
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::set set))
  :enable set-all-posp)

(defrule posp-of-max-when-set-all-posp
  (implies (and (set-all-posp set)
                (not (treeset::emptyp set)))
           (posp (treeset::max set)))
  :use (:instance
         (:functional-instance
           treeset::genericp-of-max-under-iff-when-set-all-genericp
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::set set))
  :enable set-all-posp)

(defrule posp-of-head-when-set-all-posp
  (implies (and (set-all-posp set)
                (not (treeset::emptyp set)))
           (posp (treeset::head set)))
  :use (:instance
         (:functional-instance
           treeset::genericp-of-head-under-iff-when-set-all-genericp
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treeset::set set))
  :enable set-all-posp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same check run as a single walk over the map's own tree, reading the
;; value at every node. This builds no value treeset, so it is what the
;; recognizer executes.

(define tree-all-vals-posp ((tree treemap::treep))
  (or (treemap::tree-empty-p tree)
      (and (posp (treemap::tree-element->val (treemap::tree->head tree)))
           (tree-all-vals-posp (treemap::tree->left tree))
           (tree-all-vals-posp (treemap::tree->right tree)))))

;;;;;;;;;;;;;;;;;;;;

(defruled tree-all-vals-posp-becomes-set-all-posp-of-values
  (implies (treemap::mapp map)
           (equal (tree-all-vals-posp map)
                  (set-all-posp (treemap::values (double-rewrite map)))))
  :use (:instance
         (:functional-instance
           treemap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp)
           (treemap::tree-all-vals-genericp tree-all-vals-posp))
         (treemap::map map))
  :enable (set-all-posp
           tree-all-vals-posp))

(defrule tree-all-vals-posp-of-tree-split.left-when-tree-all-vals-posp
  (implies (tree-all-vals-posp tree)
           (tree-all-vals-posp (mv-nth 1 (treemap::tree-split key tree))))
  :use (:instance
         (:functional-instance
           treemap::tree-all-vals-genericp-of-tree-split.left-when-tree-all-vals-genericp
           (treeset::genericp posp)
           (treemap::tree-all-vals-genericp tree-all-vals-posp))
         (treemap::tree tree)
         (treemap::key key))
  :enable tree-all-vals-posp)

(defrule tree-all-vals-posp-of-tree-split.right-when-tree-all-vals-posp
  (implies (tree-all-vals-posp tree)
           (tree-all-vals-posp (mv-nth 2 (treemap::tree-split key tree))))
  :use (:instance
         (:functional-instance
           treemap::tree-all-vals-genericp-of-tree-split.right-when-tree-all-vals-genericp
           (treeset::genericp posp)
           (treemap::tree-all-vals-genericp tree-all-vals-posp))
         (treemap::tree tree)
         (treemap::key key))
  :enable tree-all-vals-posp)

(defrule posp-of-cdr-of-tree-search-assoc-when-tree-all-vals-posp
  (implies (and (tree-all-vals-posp tree)
                (treemap::tree-search-assoc key tree))
           (posp (cdr (treemap::tree-search-assoc key tree))))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-cdr-of-tree-search-assoc-when-tree-all-vals-genericp
           (treeset::genericp posp)
           (treemap::tree-all-vals-genericp tree-all-vals-posp))
         (treemap::tree tree)
         (treemap::key key))
  :enable tree-all-vals-posp)

(defrule posp-of-tree-lookup-when-tree-all-vals-posp
  (implies (and (tree-all-vals-posp tree)
                (treeset::in key (treemap::tree-key-set (double-rewrite tree))))
           (posp (treemap::tree-lookup key tree)))
  :rule-classes
  (:rewrite
   (:linear :corollary
            (implies (and (tree-all-vals-posp tree)
                          (treeset::in key (treemap::tree-key-set
                                             (double-rewrite tree))))
                     (< 0 (treemap::tree-lookup key tree)))))
  :induct t
  :enable (treemap::tree-lookup
           tree-all-vals-posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The recognizer itself: every value of the map is a positive integer. The
;; logical form is the treeset check over @(tsee treemap::values), which is
;; where the generic laws land; the walk above is the execution.
;;
;; Time complexity: @($O(n)$).

(define map-values-all-posp ((map treemap::mapp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (mbe :logic (set-all-posp (treemap::values map))
       :exec (tree-all-vals-posp map))
  :guard-hints
  (("Goal" :in-theory (enable tree-all-vals-posp-becomes-set-all-posp-of-values
                              treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-posp-type-prescription
  (booleanp (map-values-all-posp map))
  :rule-classes ((:type-prescription :typed-term (map-values-all-posp map))))

(defrule map-values-all-posp-when-treemap-equiv-congruence
  (implies (treemap::equiv map0 map1)
           (equal (map-values-all-posp map0)
                  (map-values-all-posp map1)))
  :rule-classes :congruence
  :enable map-values-all-posp)

(defrule tree-all-vals-posp-when-map-values-all-posp
  (implies (and (treemap::mapp map)
                (map-values-all-posp (double-rewrite map)))
           (tree-all-vals-posp map))
  :enable (map-values-all-posp
           tree-all-vals-posp-becomes-set-all-posp-of-values))

(defruled map-values-all-posp-when-emptyp
  (implies (treemap::emptyp map)
           (map-values-all-posp map))
  :enable (map-values-all-posp
           set-all-posp-when-emptyp))

(defrule map-values-all-posp-when-emptyp-cheap
  (implies (treemap::emptyp map)
           (map-values-all-posp map))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-posp-when-emptyp)

(defrule map-values-all-posp-of-empty
  (map-values-all-posp (treemap::empty))
  :enable map-values-all-posp-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-of-lookup-when-map-values-all-posp
  (implies (and (map-values-all-posp map)
                (treemap::in k map))
           (posp (treemap::lookup k map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-lookup-when-set-all-genericp-of-values
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-posp
           set-all-posp))

;; The weaker consequence, for a caller reading 0 at an absent key: since no
;; key holds 0, that reading is a natural whether or not the key is present,
;; and the membership hypothesis drops away.

(defrule natp-of-lookup-with-default-0-when-map-values-all-posp
  (implies (map-values-all-posp map)
           (natp (treemap::lookup k map :default 0)))
  :use posp-of-lookup-when-map-values-all-posp
  :disable posp-of-lookup-when-map-values-all-posp
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-posp-of-update
  (equal (map-values-all-posp (treemap::update k v map))
         (and (posp v)
              (map-values-all-posp (treemap::delete k map))))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-update
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map)
         (treemap::k k)
         (treemap::v v))
  :enable (map-values-all-posp
           set-all-posp))

(defrule map-values-all-posp-of-delete
  (implies (map-values-all-posp map)
           (map-values-all-posp (treemap::delete k map)))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-delete
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-posp
           set-all-posp))

(defrule map-values-all-posp-of-update*
  (implies (and (map-values-all-posp m1)
                (map-values-all-posp m2))
           (map-values-all-posp (treemap::update* m1 m2)))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-update*
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::m1 m1)
         (treemap::m2 m2))
  :enable (map-values-all-posp
           set-all-posp))

(defrule map-values-all-posp-of-restrict
  (implies (map-values-all-posp map)
           (map-values-all-posp (treemap::restrict s map)))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-restrict
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map)
         (treemap::s s))
  :enable (map-values-all-posp
           set-all-posp))

;; The peel step of a min/delete recursion over the map: peeling a bound key
;; removes exactly its multiplicity from view.

(defruled map-values-all-posp-of-delete-when-in
  (implies (treeset::in k (treemap::keys map))
           (equal (map-values-all-posp map)
                  (and (posp (treemap::lookup k map))
                       (map-values-all-posp (treemap::delete k map)))))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-delete-when-in
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-posp
           set-all-posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule posp-of-min-val-when-map-values-all-posp
  (implies (and (map-values-all-posp (double-rewrite map))
                (not (treemap::emptyp (double-rewrite map))))
           (posp (treemap::min-val map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-min-val-when-set-all-genericp-of-values
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map))
  :enable (map-values-all-posp
           set-all-posp))

(defrule posp-of-max-val-when-map-values-all-posp
  (implies (and (map-values-all-posp (double-rewrite map))
                (not (treemap::emptyp (double-rewrite map))))
           (posp (treemap::max-val map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-max-val-when-set-all-genericp-of-values
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map))
  :enable (map-values-all-posp
           set-all-posp))

(defrule posp-of-head-val-when-map-values-all-posp
  (implies (and (map-values-all-posp (double-rewrite map))
                (not (treemap::emptyp (double-rewrite map))))
           (posp (treemap::head-val map)))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-head-val-when-set-all-genericp-of-values
           (treeset::genericp posp)
           (treeset::set-all-genericp set-all-posp))
         (treemap::map map))
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
