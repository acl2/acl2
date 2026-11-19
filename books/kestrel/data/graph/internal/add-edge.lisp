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
(include-book "kestrel/data/tmap/cursor/defs" :dir :system)

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/cursor/top" :dir :system))

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
  :returns (new-adjl tmap::mapp)
  (mbe :logic
       (b* ((adj (tmap::lookup from adjl :default (tmap::empty)))
            (labels (tmap::lookup to adj :default (tset::empty))))
         (tmap::update from
                       (tmap::update to
                                     (tset::insert label labels)
                                     adj)
                       adjl))
       ;; One descent in each map: the cursor reached by the search is edited
       ;; in place.
       :exec
       (b* ((outer (tmap::seek from adjl))
            ((unless (tmap::entryp outer))
             (tmap::from-cursor
               (tmap::update-hole
                 from
                 (tmap::update to
                               (tset::insert label (tset::empty))
                               (tmap::empty))
                 outer)))
            (inner (tmap::seek to (tmap::entry-val outer)))
            (adj (tmap::from-cursor
                   (if (tmap::entryp inner)
                       (tmap::update-entry
                         (tset::insert label (tmap::entry-val inner))
                         inner)
                     (tmap::update-hole to
                                        (tset::insert label (tset::empty))
                                        inner)))))
         (tmap::from-cursor (tmap::update-entry adj outer)))))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-add-edge-when-tmap-equiv-of-arg4-congruence
  (implies (tmap::equiv adjl0 adjl1)
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
  (equal (tmap::keys (adj-list-add-edge from to label adjl))
         (tset::insert from (tmap::keys adjl)))
  :enable adj-list-add-edge)

(defrule adj-list-edges-of-adj-list-add-edge
  (equal (adj-list-edges (adj-list-add-edge from to label adjl))
         (tset::insert (edge from to label) (adj-list-edges adjl)))
  :enable (adj-list-add-edge
           tset::extensionality-no-backchain-limit-polar
           in-of-adj-list-edges)
  :disable adj-list-edges-of-update)

;; Adding an edge preserves well-formedness provided the target is already a
;; node. The source needs no such hypothesis: it is made a key by the operation
;; itself.

(defrule well-formedp-of-adj-list-add-edge
  (implies (and (well-formedp adjl)
                (tset::in to (tmap::keys adjl)))
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
  :enable adj-list-add-edge)

;; Adding an edge already adds its source as a node, and adding a node moves
;; inward past adding an edge, so that a list is built by adding its nodes
;; first. That is the order in which well-formedness is preserved step by step.

(defrule adj-list-add-edge-of-adj-list-add-node-same
  (equal (adj-list-add-edge from to label (adj-list-add-node from adjl))
         (adj-list-add-edge from to label adjl))
  :enable (adj-list-add-edge
           adj-list-add-node))

(defrule adj-list-add-node-of-adj-list-add-edge
  (equal (adj-list-add-node node (adj-list-add-edge from to label adjl))
         (adj-list-add-edge from to label (adj-list-add-node node adjl)))
  :enable (adj-list-add-edge
           adj-list-add-node))
