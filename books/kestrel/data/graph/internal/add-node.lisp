; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)

(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))
(local (include-book "kestrel/data/treemap/update" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))
(local (include-book "kestrel/data/treemap/extensionality" :dir :system))

(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add an isolated node. A node already in the list is left alone, so that
;; adding a node never disturbs its existing edges.
;;
;; Time complexity: @($O(\\log(n))$).

(define adj-list-add-node (node (adjl adj-listp))
  :returns (new-adjl treemap::mapp)
  (if (treemap::in node adjl)
      (treemap::fix adjl)
    (treemap::update node (treemap::empty) adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-add-node-when-treemap-equiv-of-arg2-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-add-node node adjl0)
                  (adj-list-add-node node adjl1)))
  :rule-classes :congruence
  :enable adj-list-add-node)

(defrule map-values-all-adjacencyp-of-adj-list-add-node
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (adj-list-add-node node adjl)))
  :enable adj-list-add-node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the node and edge sets: the node is added, and no edges are.

(defrule keys-of-adj-list-add-node
  (equal (treemap::keys (adj-list-add-node node adjl))
         (treeset::insert node (treemap::keys adjl)))
  :enable adj-list-add-node)

(defrule adj-list-edges-of-adj-list-add-node
  (equal (adj-list-edges (adj-list-add-node node adjl))
         (adj-list-edges adjl))
  :enable adj-list-add-node)

;; The added node has the empty adjacency, which is how an absent node reads.

(defrule lookup-of-adj-list-add-node
  (equal (treemap::lookup key
                          (adj-list-add-node node adjl)
                          :default (treemap::empty))
         (treemap::lookup key adjl :default (treemap::empty)))
  :enable adj-list-add-node)

;; Adding a node only enlarges the node set and adds no targets, so it
;; preserves well-formedness.

(defrule well-formedp-of-adj-list-add-node
  (implies (well-formedp adjl)
           (well-formedp (adj-list-add-node node adjl)))
  :enable (adj-list-add-node
           well-formedp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-add-node-of-adj-list-add-node-same
  (equal (adj-list-add-node node (adj-list-add-node node adjl))
         (adj-list-add-node node adjl))
  :enable adj-list-add-node)

(defrule adj-list-add-node-of-adj-list-add-node-commutative
  (equal (adj-list-add-node node0 (adj-list-add-node node1 adjl))
         (adj-list-add-node node1 (adj-list-add-node node0 adjl)))
  :enable adj-list-add-node)
