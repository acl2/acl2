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
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/subset-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/size-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/min-max-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))
(local (include-book "add-node"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reverse the edges out of one source into an accumulating adjacency list:
;; each target gains the source, with the same labels. The label sets are
;; shared, not copied.
;;
;; Time complexity: @($O(d\\log(n))$), where @($d$) is the number of targets
;; and @($n$) the number of keys of the accumulator.

(define adjacency-transpose (from (adj treemap::mapp) (acc treemap::mapp))
  :guard (and (map-values-all-nonempty-setp adj)
              (map-values-all-adjacencyp acc))
  :returns (new-acc treemap::mapp)
  (if (treemap::emptyp adj)
      (treemap::fix acc)
    (b* ((to (treemap::min-key adj)))
      (adjacency-transpose
        from
        (treemap::delete to adj)
        (treemap::update to
                         (treemap::update from
                                          (treemap::lookup to adj)
                                          (treemap::lookup
                                            to
                                            acc
                                            :default (treemap::empty)))
                         acc))))
  :measure (treemap::size adj)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule adjacency-transpose-when-treemap-equiv-of-arg2-congruence
  (implies (treemap::equiv adj0 adj1)
           (equal (adjacency-transpose from adj0 acc)
                  (adjacency-transpose from adj1 acc)))
  :rule-classes :congruence
  :expand ((adjacency-transpose from adj0 acc)
           (adjacency-transpose from adj1 acc)))

(defrule adjacency-transpose-when-treemap-equiv-of-arg3-congruence
  (implies (treemap::equiv acc0 acc1)
           (equal (adjacency-transpose from adj acc0)
                  (adjacency-transpose from adj acc1)))
  :rule-classes :congruence
  :induct t
  :enable adjacency-transpose)

(defrule map-values-all-adjacencyp-of-adjacency-transpose
  (implies (and (map-values-all-nonempty-setp adj)
                (map-values-all-adjacencyp acc))
           (map-values-all-adjacencyp (adjacency-transpose from adj acc)))
  :induct t
  :enable adjacency-transpose)

(verify-guards adjacency-transpose)

;; Each target of the source is now bound to its old adjacency with the source
;; added; every other key is unchanged.

(defrule in-of-keys-of-adjacency-transpose
  (equal (treeset::in key (treemap::keys (adjacency-transpose from adj acc)))
         (or (treeset::in key (treemap::keys adj))
             (treeset::in key (treemap::keys acc))))
  :induct t
  :enable adjacency-transpose)

(defrule lookup-of-adjacency-transpose
  (equal (treemap::lookup key
                          (adjacency-transpose from adj acc)
                          :default default)
         (if (treeset::in key (treemap::keys adj))
             (treemap::update from
                              (treemap::lookup key adj)
                              (treemap::lookup key
                                               acc
                                               :default (treemap::empty)))
           (treemap::lookup key acc :default default)))
  :induct t
  :enable adjacency-transpose)

;; The source becomes a target of each target, so if the source is among a
;; node set into which every adjacency leads, that still holds.

(defrule map-values-all-keys-subsetp-of-adjacency-transpose
  (implies (and (map-values-all-keys-subsetp acc nodes)
                (treeset::in from nodes))
           (map-values-all-keys-subsetp (adjacency-transpose from adj acc)
                                        nodes))
  :induct t
  :enable adjacency-transpose)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reverse every edge. Each source is added as a node, and its edges are then
;; reversed into the transpose of the rest of the list.
;;
;; Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
;; nodes and @($m$) the number of (source, target) pairs with an edge.

(define adj-list-transpose ((adjl adj-listp))
  :returns (new-adjl treemap::mapp)
  (if (treemap::emptyp adjl)
      (treemap::empty)
    (b* ((from (treemap::min-key adjl)))
      (adjacency-transpose
        from
        (treemap::lookup from adjl)
        (adj-list-add-node from
                           (adj-list-transpose
                             (treemap::delete from adjl))))))
  :measure (treemap::size adjl)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-transpose-when-treemap-equiv-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-transpose adjl0)
                  (adj-list-transpose adjl1)))
  :rule-classes :congruence
  :expand ((adj-list-transpose adjl0)
           (adj-list-transpose adjl1)))

(defrule map-values-all-adjacencyp-of-adj-list-transpose
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (adj-list-transpose adjl)))
  :induct t
  :enable adj-list-transpose)

(verify-guards adj-list-transpose)

;; The labels from one node to another in the transpose are the labels from
;; the second to the first.

(defrule lookup-of-lookup-of-adj-list-transpose
  (equal (treemap::lookup from
                          (treemap::lookup to
                                           (adj-list-transpose adjl)
                                           :default (treemap::empty))
                          :default (treeset::empty))
         (treemap::lookup to
                          (treemap::lookup from
                                           adjl
                                           :default (treemap::empty))
                          :default (treeset::empty)))
  :induct t
  :enable adj-list-transpose)

;; Every source is a node of the transpose, and so is every target, which in
;; a well-formed list is also a source.

(defrulel in-of-keys-of-adj-list-transpose-when-in-of-keys
  (implies (treeset::in key (treemap::keys adjl))
           (treeset::in key (treemap::keys (adj-list-transpose adjl))))
  :induct t
  :enable adj-list-transpose)

(defrulel in-when-in-of-keys-of-adj-list-transpose
  (implies (and (map-values-all-keys-subsetp adjl nodes)
                (treeset::subset (treemap::keys adjl) nodes)
                (treeset::in key (treemap::keys (adj-list-transpose adjl))))
           (treeset::in key nodes))
  :induct t
  :enable adj-list-transpose)

(defrule keys-of-adj-list-transpose
  (implies (well-formedp adjl)
           (equal (treemap::keys (adj-list-transpose adjl))
                  (treemap::keys adjl)))
  :enable (treeset::extensionality-polar
           well-formedp
           acl2::equal-of-booleans-cheap))

;; Every target of the transpose is a source of the list.

(defrulel map-values-all-keys-subsetp-of-adj-list-transpose
  (implies (treeset::subset (treemap::keys adjl) nodes)
           (map-values-all-keys-subsetp (adj-list-transpose adjl) nodes))
  :induct t
  :enable (adj-list-transpose
           adj-list-add-node))

(defrule well-formedp-of-adj-list-transpose
  (implies (well-formedp adjl)
           (well-formedp (adj-list-transpose adjl)))
  :enable well-formedp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The edges of the transpose are the edges of the list reversed.

(defruled in-of-adj-list-edges-of-adj-list-transpose
  (implies (edge-equiv edge$ (double-rewrite edge))
           (equal (treeset::in edge (adj-list-edges (adj-list-transpose adjl)))
                  (and (edgep edge)
                       (treeset::in (edge (edge->to edge$)
                                          (edge->from edge$)
                                          (edge->label edge$))
                                    (adj-list-edges adjl)))))
  :enable in-of-adj-list-edges)
