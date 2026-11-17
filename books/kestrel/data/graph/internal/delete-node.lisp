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
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/min-max-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/diff-defs" :dir :system)
(include-book "kestrel/data/tmap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/size-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/min-max-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)

(include-book "../edge-defs")
(include-book "adj-list-defs")
(include-book "well-formed-defs")
(include-book "edges-defs")
(include-book "add-node-defs")
(include-book "predecessors-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/hash" :dir :system))
(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/union" :dir :system))
(local (include-book "kestrel/data/tset/diff" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))
(local (include-book "kestrel/data/tmap/internal/tree" :dir :system))
(local (include-book "kestrel/data/tmap/internal/bst" :dir :system))
(local (include-book "kestrel/data/tmap/internal/heap" :dir :system))
(local (include-book "kestrel/data/tmap/internal/keys" :dir :system))
(local (include-book "kestrel/data/tmap/internal/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/size" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))
(local (include-book "kestrel/data/tmap/min-max" :dir :system))
(local (include-book "kestrel/data/tmap/lookup" :dir :system))
(local (include-book "kestrel/data/tmap/update" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))
(local (include-book "kestrel/data/tmap/extensionality" :dir :system))

(local (include-book "../edge"))
(local (include-book "adj-list"))
(local (include-book "well-formed"))
(local (include-book "edges"))
(local (include-book "add-node"))
(local (include-book "predecessors"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel mapp-of-tree-element->val-of-tree->head-when-tree-all-vals-adjacencyp
  (implies (and (tree-all-vals-adjacencyp tree)
                (not (tmap::tree-empty-p tree)))
           (tmap::mapp
             (tmap::tree-element->val (tmap::tree->head tree))))
  :enable tree-all-vals-adjacencyp)

;; The walk that executes removing a node as a target. It visits every node of
;; the tree and keeps each node's key and hash, so the shape is untouched and
;; both search-tree invariants carry over term for term. Only an adjacency
;; which actually has the target is rebuilt, and a node is reused whenever
;; nothing beneath it changed, so the allocation is only along the paths to
;; the adjacencies that point at the node.
;;
;; Time complexity: @($O(n \\log(d))$), where @($d$) is the largest number of
;; targets of a source.

(define tree-delete-target (node (tree tmap::treep))
  :guard (tree-all-vals-adjacencyp tree)
  :returns (new-tree tmap::treep)
  (if (tmap::tree-empty-p tree)
      nil
    (b* ((head (tmap::tree->head tree))
         (adj (tmap::tree-element->val head)))
      (tmap::tree-node-with-hint
        (mbe :logic (tmap::tree-element
                      (tmap::tree-element->hash head)
                      (tmap::tree-element->key head)
                      (tmap::delete node adj))
             :exec (if (tmap::in node adj)
                       (tmap::tree-element
                         (tmap::tree-element->hash head)
                         (tmap::tree-element->key head)
                         (tmap::delete node adj))
                     head))
        (tree-delete-target node (tmap::tree->left tree))
        (tree-delete-target node (tmap::tree->right tree))
        tree)))
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-adjacencyp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-delete-target-when-tree-equiv-of-arg2-congruence
  (implies (tmap::tree-equiv tree0 tree1)
           (equal (tree-delete-target node tree0)
                  (tree-delete-target node tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-delete-target)

(defrulel tree-key-set-of-tree-delete-target
  (equal (tmap::tree-key-set (tree-delete-target node tree))
         (tmap::tree-key-set tree))
  :induct t
  :enable tree-delete-target)

(defrulel <<-all-l-of-tree-delete-target
  (equal (tmap::<<-all-l (tree-delete-target node tree) key)
         (tmap::<<-all-l tree key))
  :induct t
  :enable tree-delete-target)

(defrulel <<-all-r-of-tree-delete-target
  (equal (tmap::<<-all-r key (tree-delete-target node tree))
         (tmap::<<-all-r key tree))
  :induct t
  :enable tree-delete-target)

(defrulel heap<-all-l-of-tree-delete-target
  (equal (tmap::heap<-all-l (tree-delete-target node tree) key)
         (tmap::heap<-all-l tree key))
  :induct t
  :enable tree-delete-target)

(defrulel bstp-of-tree-delete-target
  (implies (tmap::bstp tree)
           (tmap::bstp (tree-delete-target node tree)))
  :induct t
  :enable tree-delete-target)

(defrulel heapp-of-tree-delete-target
  (implies (tmap::heapp tree)
           (tmap::heapp (tree-delete-target node tree)))
  :induct t
  :enable tree-delete-target)

(defrulel mapp-of-tree-delete-target
  (implies (tmap::mapp tree)
           (tmap::mapp (tree-delete-target node tree)))
  :enable tmap::mapp)

(defrulel tree-lookup-of-tree-delete-target
  (equal (tmap::tree-lookup key (tree-delete-target node tree))
         (if (tset::in key (tmap::tree-key-set tree))
             (tmap::delete node (tmap::tree-lookup key tree))
           (tmap::tree-lookup key tree)))
  :induct t
  :enable tree-delete-target)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove a node as a target from every adjacency, which removes its incoming
;; edges. There is no index of a node's sources, so every adjacency is
;; visited.
;;
;; The logical definition is a walk which takes the minimum source and deletes
;; it, rebuilding the list with update. It executes as the tree walk above.
;;
;; Time complexity: @($O(n \\log(d))$), as for @(tsee tree-delete-target).

(define adj-list-delete-target (node (adjl adj-listp))
  :returns (new-adjl tmap::mapp)
  (mbe :logic (if (tmap::emptyp adjl)
                  (tmap::empty)
                (b* ((from (tmap::min-key adjl)))
                  (tmap::update
                    from
                    (tmap::delete node (tmap::lookup from adjl))
                    (adj-list-delete-target node
                                            (tmap::delete from adjl)))))
       :exec (tree-delete-target node adjl))
  :measure (tmap::size adjl)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min)))
  ;; Verified below
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-target-when-tmap-equiv-of-arg2-congruence
  (implies (tmap::equiv adjl0 adjl1)
           (equal (adj-list-delete-target node adjl0)
                  (adj-list-delete-target node adjl1)))
  :rule-classes :congruence
  :expand ((adj-list-delete-target node adjl0)
           (adj-list-delete-target node adjl1)))

(defrule keys-of-adj-list-delete-target
  (equal (tmap::keys (adj-list-delete-target node adjl))
         (tmap::keys adjl))
  :induct t
  :enable adj-list-delete-target)

(defrule lookup-of-adj-list-delete-target
  (equal (tmap::lookup key
                       (adj-list-delete-target node adjl)
                       :default default)
         (if (tset::in key (tmap::keys adjl))
             (tmap::delete node (tmap::lookup key adjl))
           default))
  :induct t
  :enable adj-list-delete-target)

(defrule map-values-all-adjacencyp-of-adj-list-delete-target
  (implies (map-values-all-adjacencyp adjl)
           (map-values-all-adjacencyp (adj-list-delete-target node adjl)))
  :induct t
  :enable adj-list-delete-target)

;; The logical walk and the tree walk agree, which is what lets the tree walk
;; execute.

(defruledl adj-list-delete-target-becomes-tree-delete-target
  (implies (tmap::mapp adjl)
           (equal (adj-list-delete-target node adjl)
                  (tree-delete-target node adjl)))
  :enable (tmap::extensionality-polar
           tmap::lookup
           tmap::keys))

(verify-guards adj-list-delete-target
  :hints (("Goal"
           :in-theory (enable tmap::treep-when-mapp-forward-chaining)
           :use adj-list-delete-target-becomes-tree-delete-target
           :expand ((adj-list-delete-target node adjl)))))

;; If every adjacency leads into some node set, then once the node is removed
;; as a target, every adjacency leads into that set less the node.

(defrule map-values-all-keys-subsetp-of-adj-list-delete-target
  (implies (map-values-all-keys-subsetp adjl nodes)
           (map-values-all-keys-subsetp (adj-list-delete-target node adjl)
                                        (tset::delete node nodes)))
  :induct t
  :enable adj-list-delete-target)

;; The incoming edges are exactly the ones lost.

(defruled in-of-adj-list-edges-of-adj-list-delete-target
  (equal (tset::in edge (adj-list-edges (adj-list-delete-target node adjl)))
         (and (tset::in edge (adj-list-edges adjl))
              (not (equal (edge->to (double-rewrite edge)) node))))
  :enable in-of-adj-list-edges)

(defrule adj-list-edges-of-adj-list-delete-target
  (equal (adj-list-edges (adj-list-delete-target node adjl))
         (tset::diff (adj-list-edges adjl)
                     (adj-list-edges-to node adjl)))
  :enable (tset::extensionality-no-backchain-limit-polar
           in-of-adj-list-edges-of-adj-list-delete-target
           in-of-adj-list-edges-to))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove a node along with every edge into or out of it. Removing it as a
;; target drops its incoming edges; deleting its key drops its outgoing ones.
;;
;; Time complexity: @($O(n \\log(d))$), as for @(tsee adj-list-delete-target).

(define adj-list-delete-node (node (adjl adj-listp))
  :returns (new-adjl tmap::mapp)
  (tmap::delete node (adj-list-delete-target node adjl)))

;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-node-when-tmap-equiv-of-arg2-congruence
  (implies (tmap::equiv adjl0 adjl1)
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
  (equal (tmap::keys (adj-list-delete-node node adjl))
         (tset::delete node (tmap::keys adjl)))
  :enable adj-list-delete-node)

(defruled in-of-adj-list-edges-of-adj-list-delete-node
  (implies (edge-equiv edge$ (double-rewrite edge))
           (equal (tset::in edge
                            (adj-list-edges
                              (adj-list-delete-node node adjl)))
                  (and (tset::in edge (adj-list-edges adjl))
                       (not (equal (edge->from edge$) node))
                       (not (equal (edge->to edge$) node)))))
  :enable (adj-list-delete-node
           in-of-adj-list-edges))

(defrule well-formedp-of-adj-list-delete-node
  (implies (well-formedp adjl)
           (well-formedp (adj-list-delete-node node adjl)))
  :enable (adj-list-delete-node
           well-formedp))

;; If no node other than the node itself has an edge into it, removing it as a
;; target changes only its own adjacency, which deleting its key discards
;; anyway.

(defrulel in-of-keys-of-lookup-when-subset-of-adj-list-predecessors
  (implies (and (tset::subset (adj-list-predecessors node adjl)
                              (tset::insert node (tset::empty)))
                (not (equal key node)))
           (not (tset::in node (tmap::keys (tmap::lookup key adjl)))))
  :use (:instance tset::in-when-in-and-subset
                  (tset::a key)
                  (tset::x (adj-list-predecessors node adjl))
                  (tset::y (tset::insert node (tset::empty))))
  :enable (in-of-adj-list-predecessors
           tmap::lookup-with-default-becomes-lookup-syntaxp)
  :disable tset::in-when-in-and-subset)

(defruled adj-list-delete-node-when-subset-of-adj-list-predecessors
  (implies (and (map-values-all-adjacencyp adjl)
                (tset::subset (adj-list-predecessors node adjl)
                              (tset::insert node (tset::empty))))
           (equal (adj-list-delete-node node adjl)
                  (tmap::delete node adjl)))
  :enable (adj-list-delete-node
           tmap::extensionality-polar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule adj-list-delete-node-of-adj-list-delete-node-same
  (equal (adj-list-delete-node node (adj-list-delete-node node adjl))
         (adj-list-delete-node node adjl))
  :enable (adj-list-delete-node
           tmap::extensionality-polar))

(defrule adj-list-delete-node-of-adj-list-delete-node-commutative
  (equal (adj-list-delete-node node0 (adj-list-delete-node node1 adjl))
         (adj-list-delete-node node1 (adj-list-delete-node node0 adjl)))
  :enable (adj-list-delete-node
           tmap::extensionality-polar))

(defrule adj-list-delete-node-of-adj-list-add-node-same
  (equal (adj-list-delete-node node (adj-list-add-node node adjl))
         (adj-list-delete-node node adjl))
  :enable (adj-list-delete-node
           adj-list-add-node
           tmap::extensionality-polar))
