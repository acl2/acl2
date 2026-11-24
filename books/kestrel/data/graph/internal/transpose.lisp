; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/omaps/defs" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/subset-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/size-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/min-max-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/to-omap-defs" :dir :system)
(include-book "kestrel/data/tmap/cursor/defs" :dir :system)

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "std/omaps/core" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/min-max" :dir :system))
(local (include-book "kestrel/data/tmap/to-omap" :dir :system))
(local (include-book "kestrel/data/tmap/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/cursor/top" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))
(local (include-book "add-node"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Executable form of adjacency-transpose: the same loop, over the omap of the
;; adjacency.

(define adjacency-transpose-omap (from (omap omap::mapp) (acc tmap::mapp))
  :guard (and (omap-values-all-nonempty-setp omap)
              (map-values-all-adjacencyp acc))
  :returns (new-acc tmap::mapp)
  (if (omap::emptyp omap)
      (tmap::fix acc)
    (b* (((mv to labels) (omap::head omap)))
      (adjacency-transpose-omap
        from
        (omap::tail omap)
        (mbe :logic (tmap::update to
                                  (tmap::update from
                                                labels
                                                (tmap::lookup
                                                  to
                                                  acc
                                                  :default (tmap::empty)))
                                  acc)
             ;; One search of the accumulator, editing at the cursor it
             ;; reaches.
             :exec (b* ((cursor (tmap::seek to acc)))
                     (tmap::from-cursor
                       (if (tmap::entryp cursor)
                           (tmap::update-entry
                             (tmap::update from
                                           labels
                                           (tmap::entry-val cursor))
                             cursor)
                         (tmap::update-hole
                           to
                           (tmap::update from labels (tmap::empty))
                           cursor))))))))
  :guard-hints (("Goal" :in-theory (enable omap-values-all-nonempty-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reverse the edges out of one source into an accumulating adjacency list:
;; each target gains the source, with the same labels. The label sets are
;; shared, not copied.
;;
;; Time complexity: @($O(d\\log(n))$), where @($d$) is the number of targets
;; and @($n$) the number of keys of the accumulator.

(define adjacency-transpose (from (adj tmap::mapp) (acc tmap::mapp))
  :guard (and (map-values-all-nonempty-setp adj)
              (map-values-all-adjacencyp acc))
  :returns (new-acc tmap::mapp)
  (mbe :logic (if (tmap::emptyp adj)
                  (tmap::fix acc)
                (b* ((to (tmap::min-key adj)))
                  (adjacency-transpose
                    from
                    (tmap::delete to adj)
                    (tmap::update to
                                  (tmap::update from
                                                (tmap::lookup to adj)
                                                (tmap::lookup
                                                  to
                                                  acc
                                                  :default (tmap::empty)))
                                  acc))))
       :exec (adjacency-transpose-omap from (tmap::to-omap adj) acc))
  :measure (tmap::size adj)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule adjacency-transpose-when-tmap-equiv-of-arg2-congruence
  (implies (tmap::equiv adj0 adj1)
           (equal (adjacency-transpose from adj0 acc)
                  (adjacency-transpose from adj1 acc)))
  :rule-classes :congruence
  :expand ((adjacency-transpose from adj0 acc)
           (adjacency-transpose from adj1 acc)))

(defrule adjacency-transpose-when-tmap-equiv-of-arg3-congruence
  (implies (tmap::equiv acc0 acc1)
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

(defruledl adjacency-transpose-omap-of-to-omap
  (equal (adjacency-transpose-omap from (tmap::to-omap adj) acc)
         (adjacency-transpose from adj acc))
  :induct (adjacency-transpose from adj acc)
  :enable (adjacency-transpose
           adjacency-transpose-omap))

(verify-guards adjacency-transpose
  :hints (("Goal" :in-theory (enable adjacency-transpose
                                     adjacency-transpose-omap-of-to-omap))))

;; Each target of the source is now bound to its old adjacency with the source
;; added; every other key is unchanged.

(defrule in-of-keys-of-adjacency-transpose
  (equal (tset::in key (tmap::keys (adjacency-transpose from adj acc)))
         (or (tset::in key (tmap::keys adj))
             (tset::in key (tmap::keys acc))))
  :induct t
  :enable adjacency-transpose)

(defrule lookup-of-adjacency-transpose
  (equal (tmap::lookup key
                       (adjacency-transpose from adj acc)
                       :default default)
         (if (tset::in key (tmap::keys adj))
             (tmap::update from
                           (tmap::lookup key adj)
                           (tmap::lookup key
                                         acc
                                         :default (tmap::empty)))
           (tmap::lookup key acc :default default)))
  :induct t
  :enable adjacency-transpose)

;; The source becomes a target of each target, so if the source is among a
;; node set into which every adjacency leads, that still holds.

(defrule map-values-all-keys-subsetp-of-adjacency-transpose
  (implies (and (map-values-all-keys-subsetp acc nodes)
                (tset::in from nodes))
           (map-values-all-keys-subsetp (adjacency-transpose from adj acc)
                                        nodes))
  :induct t
  :enable adjacency-transpose)

;; Reversing the edges of one source commutes with adding a node, and with
;; reversing the edges of another source.

(defruledl adjacency-transpose-of-adj-list-add-node
  (equal (adjacency-transpose from adj (adj-list-add-node node acc))
         (adj-list-add-node node (adjacency-transpose from adj acc)))
  :enable (tmap::extensionality
           adj-list-add-node))

(defruledl adjacency-transpose-of-adjacency-transpose-commutative
  (implies (not (equal from0 from1))
           (equal (adjacency-transpose from0
                                       adj0
                                       (adjacency-transpose from1 adj1 acc))
                  (adjacency-transpose from1
                                       adj1
                                       (adjacency-transpose from0 adj0 acc))))
  :enable tmap::extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Executable form of adj-list-transpose: the same steps, over the omap of the
;; list, from the least source to the greatest. The logical definition takes
;; them in the opposite order, with the same result, since the steps for
;; distinct sources commute.

(define adj-list-transpose-omap ((omap omap::mapp) (acc tmap::mapp))
  :guard (and (omap-values-all-adjacencyp omap)
              (map-values-all-adjacencyp acc))
  :returns (new-adjl tmap::mapp)
  (if (omap::emptyp omap)
      (tmap::fix acc)
    (b* (((mv from adj) (omap::head omap)))
      (adj-list-transpose-omap
        (omap::tail omap)
        (adjacency-transpose from adj (adj-list-add-node from acc)))))
  :guard-hints (("Goal" :in-theory (enable omap-values-all-adjacencyp))))

;;;;;;;;;;;;;;;;;;;;

;; Adding a node commutes with the walk, and so does reversing the edges of a
;; source not in the omap.

(defruledl adj-list-transpose-omap-of-adj-list-add-node
  (equal (adj-list-transpose-omap omap (adj-list-add-node node acc))
         (adj-list-add-node node (adj-list-transpose-omap omap acc)))
  :induct (adj-list-transpose-omap omap acc)
  :enable (adj-list-transpose-omap
           adjacency-transpose-of-adj-list-add-node))

(defruledl adj-list-transpose-omap-of-adjacency-transpose
  (implies (not (omap::assoc from omap))
           (equal (adj-list-transpose-omap omap
                                           (adjacency-transpose from adj acc))
                  (adjacency-transpose from
                                       adj
                                       (adj-list-transpose-omap omap acc))))
  :induct (adj-list-transpose-omap omap acc)
  :expand (adj-list-transpose-omap omap (adjacency-transpose from adj acc))
  :enable (adj-list-transpose-omap
           adjacency-transpose-of-adj-list-add-node
           adjacency-transpose-of-adjacency-transpose-commutative))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reverse every edge. Each source is added as a node, and its edges are then
;; reversed into the transpose of the rest of the list.
;;
;; Time complexity: @($O((n + m)\\log(n))$), where @($n$) is the number of
;; nodes and @($m$) the number of (source, target) pairs with an edge.

(define adj-list-transpose ((adjl adj-listp))
  :returns (new-adjl tmap::mapp)
  (mbe :logic (if (tmap::emptyp adjl)
                  (tmap::empty)
                (b* ((from (tmap::min-key adjl)))
                  (adjacency-transpose
                    from
                    (tmap::lookup from adjl)
                    (adj-list-add-node from
                                       (adj-list-transpose
                                         (tmap::delete from adjl))))))
       :exec (adj-list-transpose-omap (tmap::to-omap adjl) (tmap::empty)))
  :measure (tmap::size adjl)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-transpose-when-tmap-equiv-congruence
  (implies (tmap::equiv adjl0 adjl1)
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

(defruledl adj-list-transpose-omap-of-to-omap
  (equal (adj-list-transpose-omap (tmap::to-omap adjl) (tmap::empty))
         (adj-list-transpose adjl))
  :induct (adj-list-transpose adjl)
  :expand (adj-list-transpose-omap (tmap::to-omap adjl) (tmap::empty))
  :enable (adj-list-transpose
           adj-list-transpose-omap
           adj-list-transpose-omap-of-adj-list-add-node
           adj-list-transpose-omap-of-adjacency-transpose)
  :disable tmap::to-omap-of-delete)

(verify-guards adj-list-transpose
  :hints (("Goal" :in-theory (enable adj-list-transpose
                                     adj-list-transpose-omap-of-to-omap))))

;; The labels from one node to another in the transpose are the labels from
;; the second to the first.

(defrule lookup-of-lookup-of-adj-list-transpose
  (equal (tmap::lookup from
                       (tmap::lookup to
                                     (adj-list-transpose adjl)
                                     :default (tmap::empty))
                       :default (tset::empty))
         (tmap::lookup to
                       (tmap::lookup from
                                     adjl
                                     :default (tmap::empty))
                       :default (tset::empty)))
  :induct t
  :enable adj-list-transpose)

;; Every source is a node of the transpose, and so is every target, which in
;; a well-formed list is also a source.

(defrulel in-of-keys-of-adj-list-transpose-when-in-of-keys
  (implies (tset::in key (tmap::keys adjl))
           (tset::in key (tmap::keys (adj-list-transpose adjl))))
  :induct t
  :enable adj-list-transpose)

(defrulel in-when-in-of-keys-of-adj-list-transpose
  (implies (and (map-values-all-keys-subsetp adjl nodes)
                (tset::subset (tmap::keys adjl) nodes)
                (tset::in key (tmap::keys (adj-list-transpose adjl))))
           (tset::in key nodes))
  :induct t
  :enable adj-list-transpose)

(defrule keys-of-adj-list-transpose
  (implies (well-formedp adjl)
           (equal (tmap::keys (adj-list-transpose adjl))
                  (tmap::keys adjl)))
  :enable (tset::extensionality-polar
           well-formedp
           acl2::equal-of-booleans-cheap))

;; Every target of the transpose is a source of the list.

(defrulel map-values-all-keys-subsetp-of-adj-list-transpose
  (implies (tset::subset (tmap::keys adjl) nodes)
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
           (equal (tset::in edge (adj-list-edges (adj-list-transpose adjl)))
                  (and (edgep edge)
                       (tset::in (edge (edge->to edge$)
                                       (edge->from edge$)
                                       (edge->label edge$))
                                 (adj-list-edges adjl)))))
  :enable in-of-adj-list-edges)
