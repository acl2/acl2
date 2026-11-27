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

(include-book "kestrel/data/tset/set-defs" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)

(include-book "graph-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/in" :dir :system))

(local (include-book "graph"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nodes ((graph graphp))
  :returns (nodes tset::setp)
  :parents (graph)
  :short "The set of nodes of a @(see graph)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(n)$), where @($n$) is the number of nodes.")
  (tmap::keys (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule nodes-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (nodes graph0)
                  (nodes graph1)))
  :rule-classes :congruence
  :enable nodes)

(defrule nodes-of-empty
  (equal (nodes (empty))
         (tset::empty))
  :enable (nodes
           fix
           empty))

;; A graph with no nodes is the empty graph.

(defruled fix-when-emptyp-of-nodes
  (implies (tset::emptyp (nodes graph))
           (equal (fix graph)
                  (empty)))
  :enable (nodes
           empty
           mapp-of-fix
           tmap::emptyp-alt-definition))

(defrule fix-when-emptyp-of-nodes-cheap
  (implies (tset::emptyp (nodes graph))
           (equal (fix graph)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-emptyp-of-nodes)

(defrule graphp-when-not-emptyp-of-nodes-forward-chaining
  (implies (not (tset::emptyp (nodes graph)))
           (graphp graph))
  :rule-classes :forward-chaining
  :enable (nodes
           empty))

(defrule emptyp-of-nodes-when-not-graphp-forward-chaining
  (implies (not (graphp graph))
           (tset::emptyp (nodes graph)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((graph graphp))
  :parents (graph)
  :short "Check if a @(see graph) has no nodes."
  :long
  (xdoc::topstring
    (xdoc::p
      "Time complexity: @($O(1)$).")
    (xdoc::p
      "This is a convenient abbreviation, not the logical normal form used by
       this library. It is enabled, so @('(emptyp graph)') becomes
       @('(tset::emptyp (nodes graph))'). Unlike that form, it does not
       construct the node set when executed."))
  (mbe :logic (tset::emptyp (nodes graph))
       :exec (tmap::emptyp graph))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* nodes
                                            break-abstraction))))

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
       @('(tset::in node (nodes graph))'). Unlike that form, it does not
       construct the node set when executed, so it is the form to use in
       guards."))
  (mbe :logic (tset::in node (nodes graph))
       :exec (tmap::in node graph))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable* nodes
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy nodes-extra-rules
  '(fix-when-emptyp-of-nodes))
