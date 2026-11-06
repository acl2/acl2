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

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add an edge from one node to another under a label. The source becomes a key
;; if it was not one already, since its adjacency has to be recorded. The
;; target is not added, so this may leave the adjacency list ill-formed. That
;; is deliberate: at this layer an adjacency list need not be well-formed, and
;; the caller decides whether to add the target first.
;;
;; Time complexity: @($O(\\log(n) + \\log(d) + \\log(l))$), where @($d$) is the
;; number of targets of the source and @($l$) the number of labels from the
;; source to the target.

(define adj-list-add-edge (from to label (adjl adj-listp))
  :returns (new-adjl treemap::mapp)
  (b* ((adj (treemap::lookup from adjl :default (treemap::empty)))
       (labels (treemap::lookup to adj :default (treeset::empty))))
    (treemap::update from
                     (treemap::update to
                                      (treeset::insert label labels)
                                      adj)
                     adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-add-edge-when-treemap-equiv-of-arg4-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (adj-list-add-edge from to label adjl0)
                  (adj-list-add-edge from to label adjl1)))
  :rule-classes :congruence
  :enable adj-list-add-edge)

(defrule map-values-all-adjacencyp-of-adj-list-add-edge
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (adj-list-add-edge from to label adjl)))
  :enable adj-list-add-edge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the node and edge sets: the source is added, and exactly the
;; one edge is. Neither needs a hypothesis: when the source or the target is
;; absent, the corresponding lookup reads as empty.

(defrule keys-of-adj-list-add-edge
  (equal (treemap::keys (adj-list-add-edge from to label adjl))
         (treeset::insert from (treemap::keys adjl)))
  :enable adj-list-add-edge)

(defrule adj-list-edges-of-adj-list-add-edge
  (equal (adj-list-edges (adj-list-add-edge from to label adjl))
         (treeset::insert (edge from to label) (adj-list-edges adjl)))
  :enable (adj-list-add-edge
           treeset::extensionality-no-backchain-limit-polar
           in-of-adj-list-edges)
  :disable adj-list-edges-of-update)

;; Adding an edge preserves well-formedness provided the target is already a
;; node. The source needs no such hypothesis: it is made a key by the operation
;; itself.

(defrule well-formedp-of-adj-list-add-edge
  (implies (and (well-formedp adjl)
                (treeset::in to (treemap::keys adjl)))
           (well-formedp (adj-list-add-edge from to label adjl)))
  :enable (adj-list-add-edge
           well-formedp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-add-edge-of-adj-list-add-edge-same
  (equal (adj-list-add-edge from to label
                            (adj-list-add-edge from to label adjl))
         (adj-list-add-edge from to label adjl))
  :enable adj-list-add-edge)

(defrule adj-list-add-edge-of-adj-list-add-edge-commutative
  (equal (adj-list-add-edge from0 to0 label0
                            (adj-list-add-edge from1 to1 label1 adjl))
         (adj-list-add-edge from1 to1 label1
                            (adj-list-add-edge from0 to0 label0 adjl)))
  :enable (adj-list-add-edge
           treemap::extensionality-polar))

;; Adding an edge already adds its source as a node, and adding a node commutes
;; with adding an edge.

(defrule adj-list-add-node-of-adj-list-add-edge-same
  (equal (adj-list-add-node from (adj-list-add-edge from to label adjl))
         (adj-list-add-edge from to label adjl))
  :enable adj-list-add-node)

(defrule adj-list-add-edge-of-adj-list-add-node
  (equal (adj-list-add-edge from to label (adj-list-add-node node adjl))
         (adj-list-add-node node (adj-list-add-edge from to label adjl)))
  :enable (adj-list-add-edge
           adj-list-add-node
           treemap::extensionality-polar))
