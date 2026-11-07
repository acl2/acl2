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
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)

(include-book "graph-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/in" :dir :system))

(local (include-book "graph"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nodes ((graph graphp))
  :type-prescription :none
  :returns (nodes treeset::setp)
  :parents (graph)
  :short "The set of nodes of a @(see graph)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(n)$), where @($n$) is the number of nodes.")
  (treemap::keys (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule nodes-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (nodes graph0)
                  (nodes graph1)))
  :rule-classes :congruence
  :enable nodes)

(defrule emptyp-of-nodes
  (equal (treeset::emptyp (nodes graph))
         (emptyp graph))
  :enable (nodes
           emptyp))

(defruled nodes-when-emptyp
  (implies (emptyp graph)
           (equal (nodes graph)
                  (treeset::empty)))
  :enable (nodes
           emptyp))

(defrule nodes-when-emptyp-cheap
  (implies (emptyp graph)
           (equal (nodes graph)
                  (treeset::empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by nodes-when-emptyp)

(defrule nodes-of-empty
  (equal (nodes (empty))
         (treeset::empty))
  :enable nodes-when-emptyp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define node-in (node (graph graphp))
  :parents (graph)
  :short "Check if a value is a node of a @(see graph)."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(\\log(n))$), where @($n$) is the number of
       nodes.")
    (xdoc::p
      "This is a convenient abbreviation, not the logical normal form used by
       this library. It is enabled, so @('(node-in node graph)') becomes
       @('(treeset::in node (nodes graph))'). Unlike that form, it does not
       construct the node set when executed, so it is the form to use in
       guards."))
  (mbe :logic (treeset::in node (nodes graph))
       :exec (treemap::in node graph))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* nodes
                                            break-abstraction))))
