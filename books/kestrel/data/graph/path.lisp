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

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)

(include-book "edge-defs")
(include-book "step-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))

(local (include-book "edge"))
(local (include-book "step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules which expose the fact that a path is a cons of its start onto its
;; steps. These are disabled; enable this ruleset to reason about the
;; representation directly.

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pathp (x)
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (graph)
  :short "Recognizer for paths."
  :long
  (xdoc::topstring
    (xdoc::p
      "A path is a start node and a list of @(see stepp)s. Each step names
       the node the path moves to and the label of the edge it follows from
       the node it is at, so a path determines exactly which edges it takes,
       even between nodes joined by several edges. A path with no steps stays
       at its start.")
    (xdoc::p
      "This recognizer only constrains the shape of a path. Whether a path is
       a path in a particular @(see graph) is @(tsee path-in)."))
  (and (consp x)
       (step-listp (cdr x)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule pathp-type-prescription
  (booleanp (pathp x))
  :rule-classes ((:type-prescription :typed-term (pathp x))))

(defruled pathp-compound-recognizer
  (implies (pathp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable pathp)

(add-to-ruleset break-abstraction '(pathp-compound-recognizer))

(add-to-ruleset break-abstraction '((:e pathp)))
(in-theory (disable (:e pathp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-path ()
  :type-prescription :none
  :returns (path pathp
                 :hints (("Goal" :in-theory (enable* break-abstraction))))
  (list nil))

;;;;;;;;;;;;;;;;;;;;

(add-to-ruleset break-abstraction '((:e irr-path)))
(in-theory (disable (:e irr-path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-fix ((path pathp))
  :type-prescription :none
  :returns (path$ pathp)
  :parents (pathp)
  :short "Fixer for paths."
  (mbe :logic (if (pathp path) path (irr-path))
       :exec path)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule path-fix-when-pathp
  (implies (pathp path)
           (equal (path-fix path)
                  path))
  :enable path-fix)

(defruled path-fix-when-not-pathp
  (implies (not (pathp path))
           (equal (path-fix path)
                  (irr-path)))
  :enable path-fix)

(defrule path-fix-when-not-pathp-cheap
  (implies (not (pathp path))
           (equal (path-fix path)
                  (irr-path)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by path-fix-when-not-pathp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path-equiv
  ((x pathp)
   (y pathp))
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (pathp)
  :short "Equivalence of paths up to @(tsee path-fix)."
  (equal (path-fix x)
         (path-fix y))
  :inline t

  ///
  (defequiv path-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule path-equiv-type-prescription
  (booleanp (path-equiv x y))
  :rule-classes ((:type-prescription :typed-term (path-equiv x y))))

(defrule path-fix-when-path-equiv-congruence
  (implies (path-equiv path0 path1)
           (equal (path-fix path0)
                  (path-fix path1)))
  :rule-classes :congruence
  :enable path-equiv)

(defrule path-fix-under-path-equiv
  (path-equiv (path-fix path)
              path)
  :enable path-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path->start ((path pathp))
  :parents (pathp)
  :short "The node a path starts at."
  (car (path-fix path))
  :inline t
  :guard-hints (("Goal" :in-theory (enable pathp))))

;;;;;;;;;;;;;;;;;;;;

(defrule path->start-when-path-equiv-congruence
  (implies (path-equiv path0 path1)
           (equal (path->start path0)
                  (path->start path1)))
  :rule-classes :congruence
  :enable path->start)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path->steps ((path pathp))
  :returns (steps step-listp
                  :hints (("Goal" :in-theory (enable path-fix
                                                     pathp
                                                     irr-path))))
  :parents (pathp)
  :short "The steps of a path, in order."
  (cdr (path-fix path))
  :inline t
  :guard-hints (("Goal" :in-theory (enable pathp))))

;;;;;;;;;;;;;;;;;;;;

(defrule path->steps-when-path-equiv-congruence
  (implies (path-equiv path0 path1)
           (equal (path->steps path0)
                  (path->steps path1)))
  :rule-classes :congruence
  :enable path->steps)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define path (start (steps step-listp))
  :type-prescription :none
  :returns (path pathp :hints (("Goal" :in-theory (enable pathp))))
  :parents (pathp)
  :short "Construct a path from its start and its steps."
  (cons start (step-list-fix steps))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule path-when-step-list-equiv-of-arg2-congruence
  (implies (step-list-equiv steps0 steps1)
           (equal (path start steps0)
                  (path start steps1)))
  :rule-classes :congruence
  :enable path)

(defrule path->start-of-path
  (equal (path->start (path start steps))
         start)
  :enable (path
           path->start
           pathp))

(defrule path->steps-of-path
  (equal (path->steps (path start steps))
         (step-list-fix steps))
  :enable (path
           path->steps
           pathp))

(defrule path-of-path->start-and-path->steps
  (equal (path (path->start path)
               (path->steps path))
         (path-fix path))
  :enable (path
           path->start
           path->steps
           path-fix
           pathp
           irr-path))

;; A path is determined by its start and its steps. The reconstruction rule
;; above stops applying once a component has been replaced by an equal term,
;; so equalities against a constructed path are decided componentwise.

(defrule equal-of-path
  (implies (path-equiv x$ (double-rewrite x))
           (equal (equal (path start steps) x)
                  (and (pathp x)
                       (equal (path->start x$) start)
                       (equal (path->steps x$) (step-list-fix steps)))))
  :enable (path
           path->start
           path->steps
           pathp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The node a list of steps ends at, when taken from the given node.

(define steps-end (from (steps step-listp))
  :parents (path-end)
  (if (consp steps)
      (steps-end (step->to (car steps)) (cdr steps))
    from))

;;;;;;;;;;;;;;;;;;;;

(define path-end ((path pathp))
  :parents (pathp)
  :short "The node a path ends at."
  :long
  (xdoc::topstring-p
    "This is the node the last step moves to, or the start of a path with no
     steps. Time complexity: @($O(k)$), where @($k$) is the number of
     steps.")
  (steps-end (path->start path) (path->steps path))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule path-end-when-path-equiv-congruence
  (implies (path-equiv path0 path1)
           (equal (path-end path0)
                  (path-end path1)))
  :rule-classes :congruence
  :enable path-end)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The set of edges a list of steps follows, when taken from the given node.

(define steps-edges (from (steps step-listp))
  :type-prescription :none
  :returns (edges treeset::setp)
  :parents (path-edges)
  (if (consp steps)
      (treeset::insert (edge from
                             (step->to (car steps))
                             (step->label (car steps)))
                       (steps-edges (step->to (car steps)) (cdr steps)))
    (treeset::empty))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define path-edges ((path pathp))
  :type-prescription :none
  :returns (edges treeset::setp)
  :parents (pathp)
  :short "The set of edges a path follows."
  :long
  (xdoc::topstring-p
    "This is a set, so it forgets the order of the steps and how often an
     edge is followed. It is the logical view of a path's edges, used to
     state that a path is in a graph (see @(tsee path-in)). Time complexity:
     @($O(k\\log(k))$), where @($k$) is the number of steps.")
  (steps-edges (path->start path) (path->steps path))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule path-edges-when-path-equiv-congruence
  (implies (path-equiv path0 path1)
           (equal (path-edges path0)
                  (path-edges path1)))
  :rule-classes :congruence
  :enable path-edges)
