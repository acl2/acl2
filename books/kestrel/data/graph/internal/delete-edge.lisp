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
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")
(include-book "add-edge-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/extensionality" :dir :system))

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

(define adjacency-delete-label (to label (adj treemap::mapp))
  :guard (map-values-all-nonempty-setp adj)
  :returns (new-adj treemap::mapp)
  (b* ((labels (treeset::delete
                 label
                 (treemap::lookup to adj :default (treeset::empty)))))
    (if (treeset::emptyp labels)
        (treemap::delete to adj)
      (treemap::update to labels adj)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule adjacency-delete-label-when-treemap-equiv-of-arg3-congruence
  (implies (treemap::equiv adj0 adj1)
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
  (equal (treemap::keys (adjacency-delete-label to label adj))
         (if (treeset::emptyp
               (treeset::delete
                 label
                 (treemap::lookup to adj :default (treeset::empty))))
             (treeset::delete to (treemap::keys adj))
           (treeset::insert to (treemap::keys adj))))
  :enable adjacency-delete-label)

(defrule lookup-of-adjacency-delete-label
  (equal (treemap::lookup key
                          (adjacency-delete-label to label adj)
                          :default default)
         (if (equal key to)
             (if (treeset::emptyp
                   (treeset::delete
                     label
                     (treemap::lookup to adj :default (treeset::empty))))
                 default
               (treeset::delete
                 label
                 (treemap::lookup to adj :default (treeset::empty))))
           (treemap::lookup key adj :default default)))
  :enable adjacency-delete-label)

;; Read with the empty set as the default, the target's labels are simply the
;; remaining ones, whether or not any remain.

(defrule lookup-with-default-empty-of-adjacency-delete-label
  (equal (treemap::lookup key
                          (adjacency-delete-label to label adj)
                          :default (treeset::empty))
         (if (equal key to)
             (treeset::delete
               label
               (treemap::lookup to adj :default (treeset::empty)))
           (treemap::lookup key adj :default (treeset::empty))))
  :use (:instance treeset::fix-when-emptyp
                  (treeset::set
                    (treeset::delete
                      label
                      (treemap::lookup to adj :default (treeset::empty))))))

(defrule adjacency-delete-label-of-adjacency-delete-label-same
  (equal (adjacency-delete-label to label
                                 (adjacency-delete-label to label adj))
         (adjacency-delete-label to label adj))
  :enable treemap::extensionality-polar)

(defrule adjacency-delete-label-of-adjacency-delete-label-commutative
  (equal (adjacency-delete-label to0 label0
                                 (adjacency-delete-label to1 label1 adj))
         (adjacency-delete-label to1 label1
                                 (adjacency-delete-label to0 label0 adj)))
  :enable treemap::extensionality-polar
  :disable treeset::emptyp-of-delete)

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
  :returns (new-adjl treemap::mapp)
  (if (treemap::in from adjl)
      (treemap::update from
                       (adjacency-delete-label to
                                               label
                                               (treemap::lookup from adjl))
                       adjl)
    (treemap::fix adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-edge-when-treemap-equiv-of-arg4-congruence
  (implies (treemap::equiv adjl0 adjl1)
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
  (equal (treemap::keys (adj-list-delete-edge from to label adjl))
         (treemap::keys adjl))
  :enable adj-list-delete-edge)

(defrule adj-list-edges-of-adj-list-delete-edge
  (equal (adj-list-edges (adj-list-delete-edge from to label adjl))
         (treeset::delete (edge from to label) (adj-list-edges adjl)))
  :enable (adj-list-delete-edge
           treeset::extensionality-no-backchain-limit-polar
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
           treemap::extensionality-polar))

;; Adding an edge and then deleting it leaves the source behind as a node.

(defrule adj-list-delete-edge-of-adj-list-add-edge-same
  (equal (adj-list-delete-edge from to label
                               (adj-list-add-edge from to label adjl))
         (adj-list-delete-edge from to label (adj-list-add-node from adjl)))
  :enable (adj-list-delete-edge
           adj-list-add-edge
           adj-list-add-node
           treemap::extensionality-polar))

(defrule adj-list-add-edge-of-adj-list-delete-edge-same
  (equal (adj-list-add-edge from to label
                            (adj-list-delete-edge from to label adjl))
         (adj-list-add-edge from to label adjl))
  :enable (adj-list-delete-edge
           adj-list-add-edge
           treemap::extensionality-polar))
