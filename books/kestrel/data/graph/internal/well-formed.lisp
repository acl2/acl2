; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/values-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "adj-list-defs")

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
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/values" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/generic-typed" :dir :system))

(local (include-book "adj-list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An adjacency list is well-formed when every target is also a source: the
;; keys of each adjacency are among the keys of the list. This is what lets the
;; keys of the list serve as the node set of the graph, so that a node with no
;; outgoing edges is a key bound to the empty adjacency and never just a
;; target. Unlike the structural predicate, this relates the keys of one map to
;; those of another, so it is a separate invariant.
;;
;; The invariant is first stated against an arbitrary node set, which is where
;; the generic laws apply, and well-formedness is the case where that set is
;; the list's own keys.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The check over a value set: every adjacency in the set leads only into
;; nodes. The node set is a parameter, so it occurs free in the lambdas of the
;; functional instantiations below.
;;
;; This form is for reasoning only, and its guards are not verified: keys
;; requires a map, and nothing at this level says the elements are maps.

(define set-all-keys-subsetp ((set treeset::setp)
                              (nodes treeset::setp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (or (treeset::emptyp set)
      (and (treeset::subset (treemap::keys (treeset::min set)) nodes)
           (set-all-keys-subsetp (treeset::delete (treeset::min set) set)
                                 nodes)))
  :measure (treeset::cardinality set)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule set-all-keys-subsetp-type-prescription
  (booleanp (set-all-keys-subsetp set nodes))
  :rule-classes ((:type-prescription
                   :typed-term (set-all-keys-subsetp set nodes))))

(defrule set-all-keys-subsetp-when-treeset-equiv-of-arg2-congruence
  (implies (treeset::equiv nodes0 nodes1)
           (equal (set-all-keys-subsetp set nodes0)
                  (set-all-keys-subsetp set nodes1)))
  :rule-classes :congruence
  :induct (set-all-keys-subsetp set nodes0)
  :enable set-all-keys-subsetp)

(defruled set-all-keys-subsetp-when-set-all-keys-subsetp-and-subset
  (implies (and (set-all-keys-subsetp set nodes0)
                (treeset::subset nodes0 nodes1))
           (set-all-keys-subsetp set nodes1))
  :induct (set-all-keys-subsetp set nodes0)
  :enable set-all-keys-subsetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same check run as a single walk over the map's own tree. Each
;; adjacency's targets are checked against the node set directly, without
;; collecting the targets of all the adjacencies first.

(define tree-all-vals-keys-subsetp ((tree treemap::treep)
                                    (nodes treeset::setp))
  :guard (tree-all-vals-adjacencyp tree)
  (or (treemap::tree-empty-p tree)
      (and (treeset::subset
             (treemap::keys
               (treemap::tree-element->val (treemap::tree->head tree)))
             nodes)
           (tree-all-vals-keys-subsetp (treemap::tree->left tree) nodes)
           (tree-all-vals-keys-subsetp (treemap::tree->right tree) nodes)))
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-adjacencyp))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-all-vals-keys-subsetp-when-treeset-equiv-of-arg2-congruence
  (implies (treeset::equiv nodes0 nodes1)
           (equal (tree-all-vals-keys-subsetp tree nodes0)
                  (tree-all-vals-keys-subsetp tree nodes1)))
  :rule-classes :congruence
  :induct (tree-all-vals-keys-subsetp tree nodes0)
  :enable tree-all-vals-keys-subsetp)

(defruled tree-all-vals-keys-subsetp-becomes-set-all-keys-subsetp-of-values
  (implies (treemap::mapp map)
           (equal (tree-all-vals-keys-subsetp map nodes)
                  (set-all-keys-subsetp (treemap::values (double-rewrite map))
                                        nodes)))
  :use (:instance
         (:functional-instance
           treemap::tree-all-vals-genericp-becomes-set-all-genericp-of-values
           (treeset::genericp
             (lambda (x) (treeset::subset (treemap::keys x) nodes)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-keys-subsetp set nodes)))
           (treemap::tree-all-vals-genericp
             (lambda (tree) (tree-all-vals-keys-subsetp tree nodes))))
         (treemap::map map))
  :enable (set-all-keys-subsetp
           tree-all-vals-keys-subsetp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The invariant on a map: every value's keys are among nodes.
;;
;; Time complexity: @($O(s + m \\log(n))$), where @($s$) is the number of keys
;; of the map, @($n$) the size of nodes, and @($m$) the total number of targets
;; over all adjacencies.

(define map-values-all-keys-subsetp ((map treemap::mapp)
                                     (nodes treeset::setp))
  :type-prescription :none
  :guard (map-values-all-adjacencyp map)
  :returns (yes/no booleanp)
  (mbe :logic (set-all-keys-subsetp (treemap::values map) nodes)
       :exec (tree-all-vals-keys-subsetp map nodes))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable tree-all-vals-keys-subsetp-becomes-set-all-keys-subsetp-of-values
            treemap::treep-when-mapp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-keys-subsetp-type-prescription
  (booleanp (map-values-all-keys-subsetp map nodes))
  :rule-classes ((:type-prescription
                   :typed-term (map-values-all-keys-subsetp map nodes))))

(defrule map-values-all-keys-subsetp-when-treemap-equiv-of-arg1-congruence
  (implies (treemap::equiv map0 map1)
           (equal (map-values-all-keys-subsetp map0 nodes)
                  (map-values-all-keys-subsetp map1 nodes)))
  :rule-classes :congruence
  :enable map-values-all-keys-subsetp)

(defrule map-values-all-keys-subsetp-when-treeset-equiv-of-arg2-congruence
  (implies (treeset::equiv nodes0 nodes1)
           (equal (map-values-all-keys-subsetp map nodes0)
                  (map-values-all-keys-subsetp map nodes1)))
  :rule-classes :congruence
  :enable map-values-all-keys-subsetp)

(defrule tree-all-vals-keys-subsetp-when-map-values-all-keys-subsetp
  (implies (and (treemap::mapp map)
                (map-values-all-keys-subsetp (double-rewrite map) nodes))
           (tree-all-vals-keys-subsetp map nodes))
  :enable (map-values-all-keys-subsetp
           tree-all-vals-keys-subsetp-becomes-set-all-keys-subsetp-of-values))

(defruled map-values-all-keys-subsetp-when-tree-all-vals-keys-subsetp
  (implies (and (treemap::mapp map)
                (tree-all-vals-keys-subsetp map nodes))
           (map-values-all-keys-subsetp map nodes))
  :enable (map-values-all-keys-subsetp
           tree-all-vals-keys-subsetp-becomes-set-all-keys-subsetp-of-values))

(defruled map-values-all-keys-subsetp-when-emptyp
  (implies (treemap::emptyp map)
           (map-values-all-keys-subsetp map nodes))
  :enable (map-values-all-keys-subsetp
           set-all-keys-subsetp))

(defrule map-values-all-keys-subsetp-when-emptyp-cheap
  (implies (treemap::emptyp map)
           (map-values-all-keys-subsetp map nodes))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by map-values-all-keys-subsetp-when-emptyp)

(defrule map-values-all-keys-subsetp-of-empty
  (map-values-all-keys-subsetp (treemap::empty) nodes)
  :enable map-values-all-keys-subsetp-when-emptyp)

;; Growing the node set preserves the invariant. The bound being grown from is
;; free, so this is left for explicit instantiation.

(defruled map-values-all-keys-subsetp-when-map-values-all-keys-subsetp-and-subset
  (implies (and (map-values-all-keys-subsetp map nodes0)
                (treeset::subset nodes0 nodes1))
           (map-values-all-keys-subsetp map nodes1))
  :enable (map-values-all-keys-subsetp
           set-all-keys-subsetp-when-set-all-keys-subsetp-and-subset))

;; The usual way the node set grows, with no free variable.

(defrule map-values-all-keys-subsetp-of-arg1-and-insert
  (implies (map-values-all-keys-subsetp map nodes)
           (map-values-all-keys-subsetp map (treeset::insert node nodes)))
  :enable map-values-all-keys-subsetp-when-map-values-all-keys-subsetp-and-subset)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule subset-of-keys-of-lookup-when-map-values-all-keys-subsetp
  (implies (and (map-values-all-keys-subsetp map nodes)
                (treemap::in k map))
           (treeset::subset (treemap::keys (treemap::lookup k map)) nodes))
  :use (:instance
         (:functional-instance
           treemap::genericp-of-lookup-when-set-all-genericp-of-values
           (treeset::genericp
             (lambda (x) (treeset::subset (treemap::keys x) nodes)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-keys-subsetp set nodes))))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-keys-subsetp
           set-all-keys-subsetp))

(defrule subset-of-keys-of-lookup-with-default-empty-when-map-values-all-keys-subsetp
  (implies (map-values-all-keys-subsetp map nodes)
           (treeset::subset (treemap::keys (treemap::lookup
                                             k
                                             map
                                             :default (treemap::empty)))
                            nodes))
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule map-values-all-keys-subsetp-of-update
  (equal (map-values-all-keys-subsetp (treemap::update k v map) nodes)
         (and (treeset::subset (treemap::keys (double-rewrite v)) nodes)
              (map-values-all-keys-subsetp (treemap::delete k map) nodes)))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-update
           (treeset::genericp
             (lambda (x) (treeset::subset (treemap::keys x) nodes)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-keys-subsetp set nodes))))
         (treemap::map map)
         (treemap::k k)
         (treemap::v v))
  :enable (map-values-all-keys-subsetp
           set-all-keys-subsetp))

(defrule map-values-all-keys-subsetp-of-delete
  (implies (map-values-all-keys-subsetp map nodes)
           (map-values-all-keys-subsetp (treemap::delete k map) nodes))
  :use (:instance
         (:functional-instance
           treemap::set-all-genericp-of-values-of-delete
           (treeset::genericp
             (lambda (x) (treeset::subset (treemap::keys x) nodes)))
           (treeset::set-all-genericp
             (lambda (set) (set-all-keys-subsetp set nodes))))
         (treemap::map map)
         (treemap::k k))
  :enable (map-values-all-keys-subsetp
           set-all-keys-subsetp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Well-formedness: the invariant against the list's own keys.
;;
;; Time complexity: @($O(n + m \\log(n))$), where @($n$) is the number of
;; nodes and @($m$) the number of (source, target) pairs with an edge.

(define well-formedp ((adjl adj-listp))
  :type-prescription :none
  :returns (yes/no booleanp)
  (map-values-all-keys-subsetp adjl (treemap::keys adjl))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule well-formedp-type-prescription
  (booleanp (well-formedp adjl))
  :rule-classes ((:type-prescription :typed-term (well-formedp adjl))))

(defrule well-formedp-when-treemap-equiv-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (well-formedp adjl0)
                  (well-formedp adjl1)))
  :rule-classes :congruence
  :enable well-formedp)

(defrule well-formedp-of-empty
  (well-formedp (treemap::empty))
  :enable well-formedp)

;; The point of well-formedness: a target is a node.

(defrule subset-of-keys-of-lookup-when-well-formedp
  (implies (well-formedp adjl)
           (treeset::subset (treemap::keys (treemap::lookup
                                             node
                                             adjl
                                             :default (treemap::empty)))
                            (treemap::keys adjl)))
  :enable well-formedp)
