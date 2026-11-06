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

(define add-edge (from to label (adjl adj-listp))
  :returns (new-adjl treemap::mapp)
  (b* ((adj (treemap::lookup from adjl :default (treemap::empty)))
       (labels (treemap::lookup to adj :default (treeset::empty))))
    (treemap::update from
                     (treemap::update to
                                      (treeset::insert label labels)
                                      adj)
                     adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule add-edge-when-treemap-equiv-of-arg4-congruence
  (implies (treemap::equiv adjl0 adjl1)
           (equal (add-edge from to label adjl0)
                  (add-edge from to label adjl1)))
  :rule-classes :congruence
  :enable add-edge)

(defrule map-values-all-adjacencyp-of-add-edge
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (add-edge from to label adjl)))
  :enable add-edge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The effect on the node and edge sets: the source is added, and exactly the
;; one edge is. Neither needs a hypothesis: when the source or the target is
;; absent, the corresponding lookup reads as empty.

(defrule keys-of-add-edge
  (equal (treemap::keys (add-edge from to label adjl))
         (treeset::insert from (treemap::keys adjl)))
  :enable add-edge)

(defrule adj-list-edges-of-add-edge
  (equal (adj-list-edges (add-edge from to label adjl))
         (treeset::insert (edge from to label) (adj-list-edges adjl)))
  :enable (add-edge
           treeset::extensionality-no-backchain-limit-polar
           in-of-adj-list-edges)
  :disable adj-list-edges-of-update)

;; Adding an edge preserves well-formedness provided the target is already a
;; node. The source needs no such hypothesis: it is made a key by the operation
;; itself.

(defrule well-formedp-of-add-edge
  (implies (and (well-formedp adjl)
                (treeset::in to (treemap::keys adjl)))
           (well-formedp (add-edge from to label adjl)))
  :enable (add-edge
           well-formedp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule add-edge-of-add-edge-same
  (equal (add-edge from to label (add-edge from to label adjl))
         (add-edge from to label adjl))
  :enable add-edge)

(defrule add-edge-of-add-edge-commutative
  (equal (add-edge from0 to0 label0 (add-edge from1 to1 label1 adjl))
         (add-edge from1 to1 label1 (add-edge from0 to0 label0 adjl)))
  :enable (add-edge
           treemap::extensionality-polar))

;; Adding an edge already adds its source as a node, and adding a node commutes
;; with adding an edge.

(defrule add-node-of-add-edge-same
  (equal (add-node from (add-edge from to label adjl))
         (add-edge from to label adjl))
  :enable add-node)

(defrule add-edge-of-add-node
  (equal (add-edge from to label (add-node node adjl))
         (add-node node (add-edge from to label adjl)))
  :enable (add-edge
           add-node
           treemap::extensionality-polar))
