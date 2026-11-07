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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules which expose the fact that an edge is a pair of conses. These are
;; disabled; enable this ruleset to reason about the representation directly.

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An edge is a triple of a source node, a target node, and a label. None of
;; the three is constrained, so this is just a pair of conses; the type exists
;; to name the slots, not to restrict them.
;;
;; The slot order matters. Edges are collected into treesets, which order their
;; elements by <<, and << compares conses by their cars first. Source first,
;; then target, then label is therefore the order in which an in-order walk of
;; an adjacency list visits the edges, so the edge set of an adjacency list
;; comes out already sorted, and the edges out of a node are contiguous in it.

(define edgep (x)
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (graph)
  :short "Recognizer for the edges of a @(see graph)."
  (and (consp x)
       (consp (cdr x)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule edgep-type-prescription
  (booleanp (edgep x))
  :rule-classes ((:type-prescription :typed-term (edgep x))))

(defruled edgep-compound-recognizer
  (implies (edgep x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable edgep)

(add-to-ruleset break-abstraction '(edgep-compound-recognizer))

(add-to-ruleset break-abstraction '((:e edgep)))
(in-theory (disable (:e edgep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-edge ()
  :type-prescription :none
  :returns (edge edgep
                 :hints (("Goal" :in-theory (enable* break-abstraction))))
  (list* nil nil nil))

;;;;;;;;;;;;;;;;;;;;

(add-to-ruleset break-abstraction '((:e irr-edge)))
(in-theory (disable (:e irr-edge)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge-fix ((edge edgep))
  :type-prescription :none
  :returns (edge$ edgep)
  :parents (edgep)
  :short "Fixer for edges."
  (mbe :logic (if (edgep edge) edge (irr-edge))
       :exec (the cons edge))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule edge-fix-when-edgep
  (implies (edgep edge)
           (equal (edge-fix edge)
                  edge))
  :enable edge-fix)

(defruled edge-fix-when-not-edgep
  (implies (not (edgep edge))
           (equal (edge-fix edge)
                  (irr-edge)))
  :enable edge-fix)

(defrule edge-fix-when-not-edgep-cheap
  (implies (not (edgep edge))
           (equal (edge-fix edge)
                  (irr-edge)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by edge-fix-when-not-edgep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge-equiv
  ((x edgep)
   (y edgep))
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (edgep)
  :short "Equivalence of edges up to @(tsee edge-fix)."
  (equal (edge-fix x)
         (edge-fix y))
  :inline t

  ///
  (defequiv edge-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule edge-equiv-type-prescription
  (booleanp (edge-equiv x y))
  :rule-classes ((:type-prescription :typed-term (edge-equiv x y))))

(defrule edge-fix-when-edge-equiv-congruence
  (implies (edge-equiv edge0 edge1)
           (equal (edge-fix edge0)
                  (edge-fix edge1)))
  :rule-classes :congruence
  :enable edge-equiv)

(defrule edge-fix-under-edge-equiv
  (edge-equiv (edge-fix edge)
              edge)
  :enable edge-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge->from ((edge edgep))
  :parents (edgep)
  :short "The source of an edge."
  (car (edge-fix edge))
  :inline t
  :guard-hints (("Goal" :in-theory (enable edgep))))

;;;;;;;;;;;;;;;;;;;;

(defrule edge->from-when-edge-equiv-congruence
  (implies (edge-equiv edge0 edge1)
           (equal (edge->from edge0)
                  (edge->from edge1)))
  :rule-classes :congruence
  :enable edge->from)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge->to ((edge edgep))
  :parents (edgep)
  :short "The target of an edge."
  (cadr (edge-fix edge))
  :inline t
  :guard-hints (("Goal" :in-theory (enable edgep))))

;;;;;;;;;;;;;;;;;;;;

(defrule edge->to-when-edge-equiv-congruence
  (implies (edge-equiv edge0 edge1)
           (equal (edge->to edge0)
                  (edge->to edge1)))
  :rule-classes :congruence
  :enable edge->to)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge->label ((edge edgep))
  :parents (edgep)
  :short "The label of an edge."
  (cddr (edge-fix edge))
  :inline t
  :guard-hints (("Goal" :in-theory (enable edgep))))

;;;;;;;;;;;;;;;;;;;;

(defrule edge->label-when-edge-equiv-congruence
  (implies (edge-equiv edge0 edge1)
           (equal (edge->label edge0)
                  (edge->label edge1)))
  :rule-classes :congruence
  :enable edge->label)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define edge (from to label)
  :type-prescription :none
  :returns (edge edgep :hints (("Goal" :in-theory (enable edgep))))
  :parents (edgep)
  :short "Construct an edge from its source, target, and label."
  (list* from to label)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule edge->from-of-edge
  (equal (edge->from (edge from to label))
         from)
  :enable (edge
           edge->from
           edgep))

(defrule edge->to-of-edge
  (equal (edge->to (edge from to label))
         to)
  :enable (edge
           edge->to
           edgep))

(defrule edge->label-of-edge
  (equal (edge->label (edge from to label))
         label)
  :enable (edge
           edge->label
           edgep))

(defrule edge-of-edge->from-and-edge->to-and-edge->label
  (equal (edge (edge->from edge)
               (edge->to edge)
               (edge->label edge))
         (edge-fix edge))
  :enable (edge
           edge->from
           edge->to
           edge->label
           edge-fix
           edgep
           irr-edge))

;; An edge is determined by its three components. The reconstruction rule
;; above stops applying once a component has been replaced by an equal term,
;; so equalities against a constructed edge are decided componentwise.

(defrule equal-of-edge
  (implies (edge-equiv x$ (double-rewrite x))
           (equal (equal (edge from to label) x)
                  (and (edgep x)
                       (equal (edge->from x$) from)
                       (equal (edge->to x$) to)
                       (equal (edge->label x$) label))))
  :enable (edge
           edge->from
           edge->to
           edge->label
           edgep))
