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
(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
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

(local (include-book "kestrel/data/treeset/hash" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/data/treemap/internal/tree" :dir :system))
(local (include-book "kestrel/data/treemap/internal/bst" :dir :system))
(local (include-book "kestrel/data/treemap/internal/heap" :dir :system))
(local (include-book "kestrel/data/treemap/internal/keys" :dir :system))
(local (include-book "kestrel/data/treemap/internal/lookup" :dir :system))
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

;; A tree element rebuilt from its own key and value is that element. TREEMAP
;; states this only as an elimination rule; the hash argument is normalized to
;; nil, which is the form it takes here.

(defrulel tree-element-of-nil-and-tree-element->key-and-tree-element->val
  (implies (treemap::tree-element-p elem)
           (equal (treemap::tree-element nil
                                         (treemap::tree-element->key elem)
                                         (treemap::tree-element->val elem))
                  elem))
  :use treemap::tree-element-elim)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel mapp-of-tree-element->val-of-tree->head-when-tree-all-vals-adjacencyp
  (implies (and (tree-all-vals-adjacencyp tree)
                (not (treemap::tree-empty-p tree)))
           (treemap::mapp
             (treemap::tree-element->val (treemap::tree->head tree))))
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

(define tree-delete-target (node (tree treemap::treep))
  :guard (tree-all-vals-adjacencyp tree)
  :returns (new-tree treemap::treep)
  (if (treemap::tree-empty-p tree)
      nil
    (b* ((head (treemap::tree->head tree))
         (adj (treemap::tree-element->val head)))
      (treemap::tree-node-with-hint
        (mbe :logic (treemap::tree-element
                      (treemap::tree-element->hash head)
                      (treemap::tree-element->key head)
                      (treemap::delete node adj))
             :exec (if (treemap::in node adj)
                       (treemap::tree-element
                         (treemap::tree-element->hash head)
                         (treemap::tree-element->key head)
                         (treemap::delete node adj))
                     head))
        (tree-delete-target node (treemap::tree->left tree))
        (tree-delete-target node (treemap::tree->right tree))
        tree)))
  :guard-hints (("Goal" :in-theory (enable tree-all-vals-adjacencyp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-delete-target-when-tree-equiv-of-arg2-congruence
  (implies (treemap::tree-equiv tree0 tree1)
           (equal (tree-delete-target node tree0)
                  (tree-delete-target node tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-delete-target)

(defrulel tree-key-set-of-tree-delete-target
  (equal (treemap::tree-key-set (tree-delete-target node tree))
         (treemap::tree-key-set tree))
  :induct t
  :enable tree-delete-target)

(defrulel <<-all-l-of-tree-delete-target
  (equal (treemap::<<-all-l (tree-delete-target node tree) key)
         (treemap::<<-all-l tree key))
  :induct t
  :enable tree-delete-target)

(defrulel <<-all-r-of-tree-delete-target
  (equal (treemap::<<-all-r key (tree-delete-target node tree))
         (treemap::<<-all-r key tree))
  :induct t
  :enable tree-delete-target)

(defrulel heap<-all-l-of-tree-delete-target
  (equal (treemap::heap<-all-l (tree-delete-target node tree) key)
         (treemap::heap<-all-l tree key))
  :induct t
  :enable tree-delete-target)

(defrulel bstp-of-tree-delete-target
  (implies (treemap::bstp tree)
           (treemap::bstp (tree-delete-target node tree)))
  :induct t
  :enable tree-delete-target)

(defrulel heapp-of-tree-delete-target
  (implies (treemap::heapp tree)
           (treemap::heapp (tree-delete-target node tree)))
  :induct t
  :enable tree-delete-target)

(defrulel mapp-of-tree-delete-target
  (implies (treemap::mapp tree)
           (treemap::mapp (tree-delete-target node tree)))
  :enable treemap::mapp)

(defrulel tree-lookup-of-tree-delete-target
  (equal (treemap::tree-lookup key (tree-delete-target node tree))
         (if (treeset::in key (treemap::tree-key-set tree))
             (treemap::delete node (treemap::tree-lookup key tree))
           (treemap::tree-lookup key tree)))
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
  :returns (new-adjl treemap::mapp)
  (mbe :logic (if (treemap::emptyp adjl)
                  (treemap::empty)
                (b* ((from (treemap::min-key adjl)))
                  (treemap::update
                    from
                    (treemap::delete node (treemap::lookup from adjl))
                    (adj-list-delete-target node
                                            (treemap::delete from adjl)))))
       :exec (tree-delete-target node adjl))
  :measure (treemap::size adjl)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min)))
  :verify-guards nil)

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
  :enable adj-list-delete-target)

(defrule lookup-of-adj-list-delete-target
  (equal (treemap::lookup key
                          (adj-list-delete-target node adjl)
                          :default default)
         (if (treeset::in key (treemap::keys adjl))
             (treemap::delete node (treemap::lookup key adjl))
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
  (implies (treemap::mapp adjl)
           (equal (adj-list-delete-target node adjl)
                  (tree-delete-target node adjl)))
  :enable (treemap::extensionality-polar
           treemap::lookup
           treemap::keys))

(verify-guards adj-list-delete-target
  :hints (("Goal"
           :in-theory (enable treemap::treep-when-mapp-forward-chaining)
           :use adj-list-delete-target-becomes-tree-delete-target
           :expand ((adj-list-delete-target node adjl)))))

;; If every adjacency leads into some node set, then once the node is removed
;; as a target, every adjacency leads into that set less the node.

(defrule map-values-all-keys-subsetp-of-adj-list-delete-target
  (implies (map-values-all-keys-subsetp adjl nodes)
           (map-values-all-keys-subsetp (adj-list-delete-target node adjl)
                                        (treeset::delete node nodes)))
  :induct t
  :enable adj-list-delete-target)

;; The incoming edges are exactly the ones lost.

(defruled in-of-adj-list-edges-of-adj-list-delete-target
  (equal (treeset::in edge (adj-list-edges (adj-list-delete-target node adjl)))
         (and (treeset::in edge (adj-list-edges adjl))
              (not (equal (edge->to (double-rewrite edge)) node))))
  :enable in-of-adj-list-edges)

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
;; Time complexity: @($O(n \\log(d))$), as for @(tsee adj-list-delete-target).

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
           in-of-adj-list-edges))

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
