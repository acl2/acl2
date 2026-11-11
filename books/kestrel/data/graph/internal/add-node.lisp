; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)

(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/extensionality" :dir :system))

(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add an isolated node. A node already in the list is left alone, so that
;; adding a node never disturbs its existing edges.
;;
;; Time complexity: @($O(\\log(n))$).

(define adj-list-add-node (node (adjl adj-listp))
  :returns (new-adjl tmap::mapp)
  (if (tmap::in node adjl)
      (tmap::fix adjl)
    (tmap::update node (tmap::empty) adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-add-node-when-tmap-equiv-of-arg2-congruence
  (implies (tmap::equiv adjl0 adjl1)
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
  (equal (tmap::keys (adj-list-add-node node adjl))
         (tset::insert node (tmap::keys adjl)))
  :enable adj-list-add-node)

(defrule adj-list-edges-of-adj-list-add-node
  (equal (adj-list-edges (adj-list-add-node node adjl))
         (adj-list-edges adjl))
  :enable adj-list-add-node)

;; The added node has the empty adjacency, which is how an absent node reads.

(defrule lookup-of-adj-list-add-node
  (equal (tmap::lookup key
                       (adj-list-add-node node adjl)
                       :default (tmap::empty))
         (tmap::lookup key adjl :default (tmap::empty)))
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
