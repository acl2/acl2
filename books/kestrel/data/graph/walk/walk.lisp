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
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "../edge-defs")
(include-book "step-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "../edge"))
(local (include-book "step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules which expose the fact that a walk is a cons of its start onto its
;; steps. These are disabled; enable this ruleset to reason about the
;; representation directly.

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walkp (x)
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Recognizer for walks."
  :long
  (xdoc::topstring
    (xdoc::p
      "A walk is a start node and a list of @(see stepp)s. Each step names
       the node the walk moves to and the label of the edge it follows from
       the node it is at, so a walk determines exactly which edges it takes,
       even between nodes joined by several edges. A walk with no steps stays
       at its start. As usual in graph theory, a walk may visit a node or
       follow an edge more than once.")
    (xdoc::p
      "This recognizer only constrains the shape of a walk. Whether a walk is
       a walk in a particular @(see graph) is @(tsee walk-in)."))
  (and (consp x)
       (step-listp (cdr x)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walkp-type-prescription
  (booleanp (walkp x))
  :rule-classes ((:type-prescription :typed-term (walkp x))))

(defruled walkp-compound-recognizer
  (implies (walkp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable walkp)

(add-to-ruleset break-abstraction '(walkp-compound-recognizer))

(add-to-ruleset break-abstraction '((:e walkp)))
(in-theory (disable (:e walkp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-walk ()
  :type-prescription :none
  :returns (walk walkp
                 :hints (("Goal" :in-theory (enable* break-abstraction))))
  (cons nil nil))

;;;;;;;;;;;;;;;;;;;;

(add-to-ruleset break-abstraction '((:e irr-walk)))
(in-theory (disable (:e irr-walk)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk-fix ((walk walkp))
  :type-prescription :none
  :returns (walk$ walkp)
  :parents (walkp)
  :short "Fixer for walks."
  (mbe :logic (if (walkp walk) walk (irr-walk))
       :exec walk)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-fix-when-walkp
  (implies (walkp walk)
           (equal (walk-fix walk)
                  walk))
  :enable walk-fix)

(defruled walk-fix-when-not-walkp
  (implies (not (walkp walk))
           (equal (walk-fix walk)
                  (irr-walk)))
  :enable walk-fix)

(defrule walk-fix-when-not-walkp-cheap
  (implies (not (walkp walk))
           (equal (walk-fix walk)
                  (irr-walk)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by walk-fix-when-not-walkp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk-equiv
  ((x walkp)
   (y walkp))
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (walkp)
  :short "Equivalence of walks up to @(tsee walk-fix)."
  (equal (walk-fix x)
         (walk-fix y))
  :inline t

  ///
  (defequiv walk-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule walk-equiv-type-prescription
  (booleanp (walk-equiv x y))
  :rule-classes ((:type-prescription :typed-term (walk-equiv x y))))

(defrule walk-fix-when-walk-equiv-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk-fix walk0)
                  (walk-fix walk1)))
  :rule-classes :congruence
  :enable walk-equiv)

(defrule walk-fix-under-walk-equiv
  (walk-equiv (walk-fix walk)
              walk)
  :enable walk-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk->start ((walk walkp))
  :parents (walkp)
  :short "The node a walk starts at."
  (car (walk-fix walk))
  :inline t
  :guard-hints (("Goal" :in-theory (enable walkp))))

;;;;;;;;;;;;;;;;;;;;

(defrule walk->start-when-walk-equiv-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk->start walk0)
                  (walk->start walk1)))
  :rule-classes :congruence
  :enable walk->start)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk->steps ((walk walkp))
  :returns (steps step-listp
                  :hints (("Goal" :in-theory (enable walk-fix
                                                     walkp
                                                     irr-walk))))
  :parents (walkp)
  :short "The steps of a walk, in order."
  (cdr (walk-fix walk))
  :inline t
  :guard-hints (("Goal" :in-theory (enable walkp))))

;;;;;;;;;;;;;;;;;;;;

(defrule walk->steps-when-walk-equiv-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk->steps walk0)
                  (walk->steps walk1)))
  :rule-classes :congruence
  :enable walk->steps)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk (start (steps step-listp))
  :type-prescription :none
  :returns (walk walkp :hints (("Goal" :in-theory (enable walkp))))
  :parents (walkp)
  :short "Construct a walk from its start and its steps."
  (cons start (step-list-fix steps))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-when-step-list-equiv-of-arg2-congruence
  (implies (step-list-equiv steps0 steps1)
           (equal (walk start steps0)
                  (walk start steps1)))
  :rule-classes :congruence
  :enable walk)

(defrule walk->start-of-walk
  (equal (walk->start (walk start steps))
         start)
  :enable (walk
           walk->start
           walkp))

(defrule walk->steps-of-walk
  (equal (walk->steps (walk start steps))
         (step-list-fix steps))
  :enable (walk
           walk->steps
           walkp))

(defrule walk-of-walk->start-and-walk->steps
  (equal (walk (walk->start walk)
               (walk->steps walk))
         (walk-fix walk))
  :enable (walk
           walk->start
           walk->steps
           walk-fix
           walkp
           irr-walk))

;; A walk is determined by its start and its steps. The reconstruction rule
;; above stops applying once a component has been replaced by an equal term,
;; so equalities against a constructed walk are decided componentwise.

(defrule equal-of-walk
  (implies (walk-equiv x$ (double-rewrite x))
           (equal (equal (walk start steps) x)
                  (and (walkp x)
                       (equal (walk->start x$) start)
                       (equal (walk->steps x$) (step-list-fix steps)))))
  :enable (walk
           walk->start
           walk->steps
           walkp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk-end ((walk walkp))
  :parents (walkp)
  :short "The node a walk ends at."
  :long
  (xdoc::topstring-p
    "This is the node the last step moves to, or the start of a walk with no
     steps. Time complexity: @($O(k)$), where @($k$) is the number of
     steps.")
  (steps-end (walk->start walk) (walk->steps walk))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-end-when-walk-equiv-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk-end walk0)
                  (walk-end walk1)))
  :rule-classes :congruence
  :enable walk-end)

;; A walk with no steps ends at its start.

(defrule walk-end-when-not-consp-of-walk->steps
  (implies (not (consp (walk->steps walk)))
           (equal (walk-end walk)
                  (walk->start walk)))
  :enable (walk-end
           steps-end))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The set of edges a list of steps follows, when taken from the given node.

(define steps-edges (from (steps step-listp))
  :type-prescription :none
  :returns (edges treeset::setp)
  :parents (walk-edges)
  (if (consp steps)
      (treeset::insert (edge from
                             (step->to (car steps))
                             (step->label (car steps)))
                       (steps-edges (step->to (car steps)) (cdr steps)))
    (treeset::empty))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule steps-edges-of-append
  (equal (steps-edges from (append steps0 steps1))
         (treeset::union (steps-edges from steps0)
                         (steps-edges (steps-end from steps0) steps1)))
  :induct t
  :enable (steps-edges
           steps-end
           append))

;;;;;;;;;;;;;;;;;;;;

(define walk-edges ((walk walkp))
  :type-prescription :none
  :returns (edges treeset::setp)
  :parents (walkp)
  :short "The set of edges a walk follows."
  :long
  (xdoc::topstring-p
    "This is a set, so it forgets the order of the steps and how often an
     edge is followed. It is the logical view of a walk's edges, used to
     state that a walk is in a graph (see @(tsee walk-in)). Time complexity:
     @($O(k\\log(k))$), where @($k$) is the number of steps.")
  (steps-edges (walk->start walk) (walk->steps walk))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-edges-when-walk-equiv-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk-edges walk0)
                  (walk-edges walk1)))
  :rule-classes :congruence
  :enable walk-edges)

;; A walk with no steps follows no edges.

(defrule walk-edges-when-not-consp-of-walk->steps
  (implies (not (consp (walk->steps walk)))
           (equal (walk-edges walk)
                  (treeset::empty)))
  :enable (walk-edges
           steps-edges))
