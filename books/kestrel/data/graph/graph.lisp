; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treemap/map-defs" :dir :system)

(include-book "internal/adj-list-defs")
(include-book "internal/well-formed-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treemap/map" :dir :system))

(local (include-book "internal/adj-list"))
(local (include-book "internal/well-formed"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules which expose the representation of a graph as a well-formed adjacency
;; list. These are disabled; enable this ruleset to reason about the
;; representation directly. The ruleset is shared with the edge type.

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define graphp (x)
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (graph)
  :short "Recognizer for @(see graph)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n + m\\log(n))$), where @($n$) is the number of
      nodes and @($m$) the number of pairs of nodes joined by an edge."))
  (and (treemap::mapp x)
       (map-values-all-adjacencyp x)
       (well-formedp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ()
  :type-prescription :none
  :returns (graph graphp)
  :parents (graph)
  :short "The empty @(see graph)."
  (treemap::empty)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e empty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fix ((graph graphp))
  :type-prescription :none
  :returns (graph$ graphp)
  :parents (graph)
  :short "Fixer for @(see graph)s."
  (mbe :logic (if (graphp graph)
                  graph
                (empty))
       :exec (the list graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* graphp
                                            treemap::break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule fix-when-graphp
  (implies (graphp graph)
           (equal (fix graph)
                  graph))
  :enable fix)

(defruled fix-when-not-graphp
  (implies (not (graphp graph))
           (equal (fix graph)
                  (empty)))
  :enable fix)

(defrule fix-when-not-graphp-cheap
  (implies (not (graphp graph))
           (equal (fix graph)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by fix-when-not-graphp)

(defruled mapp-of-fix
  (treemap::mapp (fix graph))
  :enable (fix
           graphp
           empty))

(add-to-ruleset break-abstraction '(mapp-of-fix))

(defruled map-values-all-adjacencyp-of-fix
  (map-values-all-adjacencyp (fix graph))
  :enable (fix
           graphp
           empty))

(add-to-ruleset break-abstraction '(map-values-all-adjacencyp-of-fix))

(defruled well-formedp-of-fix
  (well-formedp (fix graph))
  :enable (fix
           graphp
           empty))

(add-to-ruleset break-abstraction '(well-formedp-of-fix))

;; The same facts for a term already known to be a graph, where the fix has
;; been rewritten away.

(defruled mapp-when-graphp
  (implies (graphp graph)
           (treemap::mapp graph))
  :enable graphp)

(add-to-ruleset break-abstraction '(mapp-when-graphp))

(defruled map-values-all-adjacencyp-when-graphp
  (implies (graphp graph)
           (map-values-all-adjacencyp graph))
  :enable graphp)

(add-to-ruleset break-abstraction '(map-values-all-adjacencyp-when-graphp))

(defruled well-formedp-when-graphp
  (implies (graphp graph)
           (well-formedp graph))
  :enable graphp)

(add-to-ruleset break-abstraction '(well-formedp-when-graphp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define equiv
  ((x graphp)
   (y graphp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (graph)
  :short "Equivalence up to @(tsee fix)."
  (equal (fix x)
         (fix y))
  :inline t

  ///
  (defequiv equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule fix-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (fix graph0)
                  (fix graph1)))
  :rule-classes :congruence
  :enable equiv)

(defrule fix-under-equiv
  (equiv (fix graph)
         graph)
  :enable equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emptyp ((graph graphp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (graph)
  :short "Check if a @(see graph) has no nodes."
  (treemap::emptyp (fix graph))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule emptyp-when-equiv-congruence
  (implies (equiv graph0 graph1)
           (equal (emptyp graph0)
                  (emptyp graph1)))
  :rule-classes :congruence
  :enable emptyp)

(defrule emptyp-of-empty
  (emptyp (empty))
  :enable (empty
           emptyp
           fix))

(defruled fix-when-emptyp
  (implies (emptyp graph)
           (equal (fix graph)
                  (empty)))
  :enable (emptyp
           empty
           mapp-of-fix
           treemap::emptyp-alt-definition))

(defrule fix-when-emptyp-cheap
  (implies (emptyp graph)
           (equal (fix graph)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable fix-when-emptyp)

(defrule graphp-when-not-emptyp-forward-chaining
  (implies (not (emptyp graph))
           (graphp graph))
  :rule-classes :forward-chaining
  :enable (emptyp
           empty))

(defrule emptyp-when-not-graphp-forward-chaining
  (implies (not (graphp graph))
           (emptyp graph))
  :rule-classes :forward-chaining)

;; This definition is useful for proving emptiness by extensionality.

(defruled emptyp-alt-definition
  (equal (emptyp graph)
         (equal (fix graph) (empty)))
  :rule-classes :definition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy graph-extra-rules
  '(fix-when-not-graphp
    fix-when-emptyp
    ))
