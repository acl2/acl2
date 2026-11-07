; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "edge-defs")
(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "internal/edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/lookup" :dir :system))

(local (include-book "edge"))
(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "internal/adj-list"))
(local (include-book "internal/well-formed"))
(local (include-book "internal/edges"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edges ((graph graphp))
  :type-prescription :none
  :returns (edges treeset::setp)
  :parents (graph)
  :short "The set of edges of a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the logical view of a graph's edges, used to state and prove
       properties of the graph operations. It is not meant to be computed on
       large graphs.")
    (xdoc::p
      "Time complexity: @($O((n + m)\\log(n + m))$), where @($n$) is the
       number of nodes and @($m$) the number of edges."))
  (adj-list-edges (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule edges-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (edges graph0)
                  (edges graph1)))
  :rule-classes :congruence
  :enable edges)

(defrule edgep-when-in-of-edges
  (implies (treeset::in edge (edges graph))
           (edgep edge))
  :enable edges)

(defruled edges-when-emptyp
  (implies (emptyp graph)
           (equal (edges graph)
                  (treeset::empty)))
  :enable (edges
           fix-when-emptyp
           empty))

(defrule edges-when-emptyp-cheap
  (implies (emptyp graph)
           (equal (edges graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by edges-when-emptyp)

(defrule edges-of-empty
  (equal (edges (empty))
         (treeset::empty))
  :enable edges-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Both ends of an edge are nodes. This is the representation's well-formedness
;; invariant, seen from the logical view.

(defrule in-of-edge->from-and-nodes-when-in-of-edges
  (implies (treeset::in edge (edges graph))
           (treeset::in (edge->from edge) (nodes graph)))
  :enable (edges
           nodes
           in-of-adj-list-edges
           treemap::lookup-with-default-becomes-lookup-syntaxp))

;; A key with a nonempty label set is present, since an absent key reads as
;; the empty set.

(defrulel in-of-keys-when-in-of-lookup-with-default-empty-forward-chaining
  (implies (treeset::in label
                        (treemap::lookup to map :default (treeset::empty)))
           (treeset::in to (treemap::keys map)))
  :rule-classes :forward-chaining
  :enable treemap::lookup-with-default-becomes-lookup-syntaxp)

(defrule in-of-edge->to-and-nodes-when-in-of-edges
  (implies (treeset::in edge (edges graph))
           (treeset::in (edge->to edge) (nodes graph)))
  :enable (edges
           nodes
           in-of-adj-list-edges
           break-abstraction))
