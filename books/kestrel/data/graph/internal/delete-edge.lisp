; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")
(include-book "add-edge-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/extensionality" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))
(local (include-book "add-node"))
(local (include-book "add-edge"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove one label from an adjacency. Removing the last label to a target
;; removes the target entirely, rather than leaving an empty label set behind,
;; which the structural predicate forbids.
;;
;; Its laws describe a lookup in the result without branching on intermediate
;; emptiness, which is what lets compositions of deletions be compared by
;; rewriting.

(define adjacency-delete-label (to label (adj tmap::mapp))
  :guard (map-values-all-nonempty-setp adj)
  :returns (new-adj tmap::mapp)
  (b* ((labels (tset::delete
                 label
                 (tmap::lookup to adj :default (tset::empty)))))
    (if (tset::emptyp labels)
        (tmap::delete to adj)
      (tmap::update to labels adj)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule adjacency-delete-label-when-tmap-equiv-of-arg3-congruence
  (implies (tmap::equiv adj0 adj1)
           (equal (adjacency-delete-label to label adj0)
                  (adjacency-delete-label to label adj1)))
  :rule-classes :congruence
  :enable adjacency-delete-label)

(defrule map-values-all-nonempty-setp-of-adjacency-delete-label
  (implies (map-values-all-nonempty-setp adj)
           (map-values-all-nonempty-setp
             (adjacency-delete-label to label adj)))
  :enable adjacency-delete-label)

(defrule keys-of-adjacency-delete-label
  (equal (tmap::keys (adjacency-delete-label to label adj))
         (if (tset::emptyp
               (tset::delete
                 label
                 (tmap::lookup to adj :default (tset::empty))))
             (tset::delete to (tmap::keys adj))
           (tset::insert to (tmap::keys adj))))
  :enable adjacency-delete-label)

(defrule lookup-of-adjacency-delete-label
  (equal (tmap::lookup key
                       (adjacency-delete-label to label adj)
                       :default default)
         (if (equal key to)
             (if (tset::emptyp
                   (tset::delete
                     label
                     (tmap::lookup to adj :default (tset::empty))))
                 default
               (tset::delete
                 label
                 (tmap::lookup to adj :default (tset::empty))))
           (tmap::lookup key adj :default default)))
  :enable adjacency-delete-label)

;; Read with the empty set as the default, the target's labels are simply the
;; remaining ones, whether or not any remain.

(defrule lookup-with-default-empty-of-adjacency-delete-label
  (equal (tmap::lookup key
                       (adjacency-delete-label to label adj)
                       :default (tset::empty))
         (if (equal key to)
             (tset::delete
               label
               (tmap::lookup to adj :default (tset::empty)))
           (tmap::lookup key adj :default (tset::empty))))
  :use (:instance tset::fix-when-emptyp
                  (tset::set
                    (tset::delete
                      label
                      (tmap::lookup to adj :default (tset::empty))))))

(defrule adjacency-delete-label-of-adjacency-delete-label-same
  (equal (adjacency-delete-label to label
                                 (adjacency-delete-label to label adj))
         (adjacency-delete-label to label adj))
  :enable tmap::extensionality-polar)

(defrule adjacency-delete-label-of-adjacency-delete-label-commutative
  (equal (adjacency-delete-label to0 label0
                                 (adjacency-delete-label to1 label1 adj))
         (adjacency-delete-label to1 label1
                                 (adjacency-delete-label to0 label0 adj)))
  :enable tmap::extensionality-polar
  :disable tset::emptyp-of-delete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove one edge, by removing its label from the source's adjacency.
;;
;; Deleting an edge never creates a node: if the source is not a key there is
;; nothing to remove, and updating it would add it.
;;
;; Time complexity: @($O(\\log(n) + \\log(d) + \\log(l))$), where @($d$) is the
;; number of targets of the source and @($l$) the number of labels from the
;; source to the target.

(define adj-list-delete-edge (from to label (adjl adj-listp))
  :returns (new-adjl tmap::mapp)
  (if (tmap::in from adjl)
      (tmap::update from
                    (adjacency-delete-label to
                                            label
                                            (tmap::lookup from adjl))
                    adjl)
    (tmap::fix adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-edge-when-tmap-equiv-of-arg4-congruence
  (implies (tmap::equiv adjl0 adjl1)
           (equal (adj-list-delete-edge from to label adjl0)
                  (adj-list-delete-edge from to label adjl1)))
  :rule-classes :congruence
  :enable adj-list-delete-edge)

(defrule map-values-all-adjacencyp-of-adj-list-delete-edge
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp
             (adj-list-delete-edge from to label adjl)))
  :enable adj-list-delete-edge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the node and edge sets: the nodes are unchanged, and exactly
;; the one edge is removed.

(defrule keys-of-adj-list-delete-edge
  (equal (tmap::keys (adj-list-delete-edge from to label adjl))
         (tmap::keys adjl))
  :enable adj-list-delete-edge)

(defrule adj-list-edges-of-adj-list-delete-edge
  (equal (adj-list-edges (adj-list-delete-edge from to label adjl))
         (tset::delete (edge from to label) (adj-list-edges adjl)))
  :enable (adj-list-delete-edge
           tset::extensionality-no-backchain-limit-polar
           in-of-adj-list-edges)
  :disable adj-list-edges-of-update)

;; Deleting an edge preserves well-formedness unconditionally: the node set is
;; unchanged, and the source's adjacency only loses targets.

(defrule well-formedp-of-adj-list-delete-edge
  (implies (well-formedp adjl)
           (well-formedp (adj-list-delete-edge from to label adjl)))
  :enable (adj-list-delete-edge
           well-formedp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-edge-of-adj-list-delete-edge-same
  (equal (adj-list-delete-edge from to label
                               (adj-list-delete-edge from to label adjl))
         (adj-list-delete-edge from to label adjl))
  :enable adj-list-delete-edge)

(defrule adj-list-delete-edge-of-adj-list-delete-edge-commutative
  (equal (adj-list-delete-edge from0 to0 label0
                               (adj-list-delete-edge from1 to1 label1 adjl))
         (adj-list-delete-edge from1 to1 label1
                               (adj-list-delete-edge from0 to0 label0 adjl)))
  :enable adj-list-delete-edge)

;; As with adding an edge, adding a node moves inward past deleting one.

(defrule adj-list-add-node-of-adj-list-delete-edge
  (equal (adj-list-add-node node (adj-list-delete-edge from to label adjl))
         (adj-list-delete-edge from to label (adj-list-add-node node adjl)))
  :enable (adj-list-delete-edge
           adj-list-add-node
           tmap::extensionality-polar))

;; Adding an edge and then deleting it leaves the source behind as a node.

(defrule adj-list-delete-edge-of-adj-list-add-edge-same
  (equal (adj-list-delete-edge from to label
                               (adj-list-add-edge from to label adjl))
         (adj-list-delete-edge from to label (adj-list-add-node from adjl)))
  :enable (adj-list-delete-edge
           adj-list-add-edge
           adj-list-add-node
           tmap::extensionality-polar))

(defrule adj-list-add-edge-of-adj-list-delete-edge-same
  (equal (adj-list-add-edge from to label
                            (adj-list-delete-edge from to label adjl))
         (adj-list-add-edge from to label adjl))
  :enable (adj-list-delete-edge
           adj-list-add-edge
           tmap::extensionality-polar))
