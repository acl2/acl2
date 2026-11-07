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
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
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

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/size" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/extensionality" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))
(local (include-book "add-node"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove a node as a target from every adjacency, which removes its incoming
;; edges. There is no index of a node's sources, so every adjacency is
;; visited.
;;
;; This is the logical definition, a walk which takes the minimum source and
;; deletes it, rebuilding the list with update. Faster executions can be put
;; under an mbe without disturbing the laws below.
;;
;; Time complexity: @($O(n (\\log(n) + \\log(d)))$), where @($d$) is the
;; largest number of targets of a source.

(define adj-list-delete-target (node (adjl adj-listp))
  :returns (new-adjl treemap::mapp)
  (if (treemap::emptyp adjl)
      (treemap::empty)
    (b* ((from (treemap::min-key adjl)))
      (treemap::update from
                       (treemap::delete node (treemap::lookup from adjl))
                       (adj-list-delete-target node
                                               (treemap::delete from adjl)))))
  :measure (treemap::size adjl)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-target-when-treemap-equiv-of-arg2-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-delete-target node adjl0)
                  (adj-list-delete-target node adjl1)))
  :rule-classes :congruence
  :expand ((adj-list-delete-target node adjl0)
           (adj-list-delete-target node adjl1)))

(defrule keys-of-adj-list-delete-target
  (equal (treemap::keys (adj-list-delete-target node adjl))
         (treemap::keys adjl))
  :induct t
  :enable (adj-list-delete-target
           treeset::in-of-min))

(defrule lookup-of-adj-list-delete-target
  (equal (treemap::lookup key
                          (adj-list-delete-target node adjl)
                          :default default)
         (if (treeset::in key (treemap::keys adjl))
             (treemap::delete node (treemap::lookup key adjl))
           default))
  :induct t
  :enable (adj-list-delete-target
           treeset::in-of-min))

(defrule map-values-all-adjacencyp-of-adj-list-delete-target
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (adj-list-delete-target node adjl)))
  :induct t
  :enable (adj-list-delete-target
           treeset::in-of-min))

;; If every adjacency leads into some node set, then once the node is removed
;; as a target, every adjacency leads into that set less the node.

(defrule map-values-all-keys-subsetp-of-adj-list-delete-target
  (implies (map-values-all-keys-subsetp adjl nodes)
           (map-values-all-keys-subsetp (adj-list-delete-target node adjl)
                                        (treeset::delete node nodes)))
  :induct t
  :enable (adj-list-delete-target
           treeset::in-of-min))

;; The incoming edges are exactly the ones lost.

(defruled in-of-adj-list-edges-of-adj-list-delete-target
  (equal (treeset::in edge (adj-list-edges (adj-list-delete-target node adjl)))
         (and (treeset::in edge (adj-list-edges adjl))
              (not (equal (edge->to (double-rewrite edge)) node))))
  :enable (in-of-adj-list-edges
           treemap::lookup-with-default-becomes-lookup-syntaxp))

(defrule adj-list-edges-of-adj-list-delete-target
  (equal (adj-list-edges (adj-list-delete-target node adjl))
         (treeset::diff (adj-list-edges adjl)
                        (adj-list-edges-to node adjl)))
  :enable (treeset::extensionality-no-backchain-limit-polar
           in-of-adj-list-edges-of-adj-list-delete-target
           in-of-adj-list-edges-to))

;; So with no edges into the node there is nothing to remove.

(defrule adj-list-delete-target-when-emptyp-of-adj-list-edges-to
  (implies (and (adj-listp adjl)
                (treeset::emptyp (adj-list-edges-to node adjl)))
           (equal (adj-list-delete-target node adjl)
                  adjl))
  :enable adj-list-extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove a node along with every edge into or out of it. Removing it as a
;; target drops its incoming edges; deleting its key drops its outgoing ones.
;;
;; Time complexity: @($O(n (\\log(n) + \\log(d)))$), as for @(tsee
;; adj-list-delete-target).

(define adj-list-delete-node (node (adjl adj-listp))
  :returns (new-adjl treemap::mapp)
  (treemap::delete node (adj-list-delete-target node adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-node-when-treemap-equiv-of-arg2-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-delete-node node adjl0)
                  (adj-list-delete-node node adjl1)))
  :rule-classes :congruence
  :enable adj-list-delete-node)

(defrule map-values-all-adjacencyp-of-adj-list-delete-node
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (adj-list-delete-node node adjl)))
  :enable adj-list-delete-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the node and edge sets: the node is removed, and so is every
;; edge touching it.

(defrule keys-of-adj-list-delete-node
  (equal (treemap::keys (adj-list-delete-node node adjl))
         (treeset::delete node (treemap::keys adjl)))
  :enable adj-list-delete-node)

(defruled in-of-adj-list-edges-of-adj-list-delete-node
  (implies (edge-equiv edge$ (double-rewrite edge))
           (equal (treeset::in edge
                               (adj-list-edges
                                 (adj-list-delete-node node adjl)))
                  (and (treeset::in edge (adj-list-edges adjl))
                       (not (equal (edge->from edge$) node))
                       (not (equal (edge->to edge$) node)))))
  :enable (adj-list-delete-node
           in-of-adj-list-edges-of-adj-list-delete-target
           in-of-adj-list-edges
           treemap::lookup-with-default-becomes-lookup-syntaxp))

(defrule well-formedp-of-adj-list-delete-node
  (implies (well-formedp adjl)
           (well-formedp (adj-list-delete-node node adjl)))
  :enable (adj-list-delete-node
           well-formedp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-node-of-adj-list-delete-node-same
  (equal (adj-list-delete-node node (adj-list-delete-node node adjl))
         (adj-list-delete-node node adjl))
  :enable (adj-list-delete-node
           treemap::extensionality-polar))

(defrule adj-list-delete-node-of-adj-list-delete-node-commutative
  (equal (adj-list-delete-node node0 (adj-list-delete-node node1 adjl))
         (adj-list-delete-node node1 (adj-list-delete-node node0 adjl)))
  :enable (adj-list-delete-node
           treemap::extensionality-polar))

(defrule adj-list-delete-node-of-adj-list-add-node-same
  (equal (adj-list-delete-node node (adj-list-add-node node adjl))
         (adj-list-delete-node node adjl))
  :enable (adj-list-delete-node
           adj-list-add-node
           treemap::extensionality-polar))
