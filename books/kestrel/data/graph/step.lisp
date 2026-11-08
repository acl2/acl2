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

;; Rules which expose the fact that a step is a cons. These are disabled;
;; enable this ruleset to reason about the representation directly.

(def-ruleset! break-abstraction ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A step of a path is the target node of an edge together with its label: an
;; edge without its source, which is the node the path is at before the step.
;; Neither part is constrained, so this is just a cons.
;;
;; The slot order is that of the target and label in an edge, so the tail of
;; an edge is a step, and an edge is a cons of its source onto a step.

(define stepp (x)
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (graph)
  :short "Recognizer for the steps of a path in a @(see graph)."
  (consp x)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule stepp-type-prescription
  (booleanp (stepp x))
  :rule-classes ((:type-prescription :typed-term (stepp x))))

(defruled stepp-compound-recognizer
  (equal (stepp x)
         (consp x))
  :rule-classes :compound-recognizer
  :enable stepp)

(add-to-ruleset break-abstraction '(stepp-compound-recognizer))

(add-to-ruleset break-abstraction '((:e stepp)))
(in-theory (disable (:e stepp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-step ()
  :type-prescription :none
  :returns (step stepp
                 :hints (("Goal" :in-theory (enable* break-abstraction))))
  (cons nil nil))

;;;;;;;;;;;;;;;;;;;;

(add-to-ruleset break-abstraction '((:e irr-step)))
(in-theory (disable (:e irr-step)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-fix ((step stepp))
  :type-prescription :none
  :returns (step$ stepp)
  :parents (stepp)
  :short "Fixer for steps."
  (mbe :logic (if (stepp step) step (irr-step))
       :exec (the cons step))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule step-fix-when-stepp
  (implies (stepp step)
           (equal (step-fix step)
                  step))
  :enable step-fix)

(defruled step-fix-when-not-stepp
  (implies (not (stepp step))
           (equal (step-fix step)
                  (irr-step)))
  :enable step-fix)

(defrule step-fix-when-not-stepp-cheap
  (implies (not (stepp step))
           (equal (step-fix step)
                  (irr-step)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by step-fix-when-not-stepp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-equiv
  ((x stepp)
   (y stepp))
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (stepp)
  :short "Equivalence of steps up to @(tsee step-fix)."
  (equal (step-fix x)
         (step-fix y))
  :inline t

  ///
  (defequiv step-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule step-equiv-type-prescription
  (booleanp (step-equiv x y))
  :rule-classes ((:type-prescription :typed-term (step-equiv x y))))

(defrule step-fix-when-step-equiv-congruence
  (implies (step-equiv step0 step1)
           (equal (step-fix step0)
                  (step-fix step1)))
  :rule-classes :congruence
  :enable step-equiv)

(defrule step-fix-under-step-equiv
  (step-equiv (step-fix step)
              step)
  :enable step-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step->to ((step stepp))
  :parents (stepp)
  :short "The node a step leads to."
  (car (step-fix step))
  :inline t
  :guard-hints (("Goal" :in-theory (enable stepp))))

;;;;;;;;;;;;;;;;;;;;

(defrule step->to-when-step-equiv-congruence
  (implies (step-equiv step0 step1)
           (equal (step->to step0)
                  (step->to step1)))
  :rule-classes :congruence
  :enable step->to)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step->label ((step stepp))
  :parents (stepp)
  :short "The label of the edge a step follows."
  (cdr (step-fix step))
  :inline t
  :guard-hints (("Goal" :in-theory (enable stepp))))

;;;;;;;;;;;;;;;;;;;;

(defrule step->label-when-step-equiv-congruence
  (implies (step-equiv step0 step1)
           (equal (step->label step0)
                  (step->label step1)))
  :rule-classes :congruence
  :enable step->label)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step (to label)
  :type-prescription :none
  :returns (step stepp :hints (("Goal" :in-theory (enable stepp))))
  :parents (stepp)
  :short "Construct a step from the node it leads to and the label of the
          edge it follows."
  (cons to label)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule step->to-of-step
  (equal (step->to (step to label))
         to)
  :enable (step
           step->to
           stepp))

(defrule step->label-of-step
  (equal (step->label (step to label))
         label)
  :enable (step
           step->label
           stepp))

(defrule step-of-step->to-and-step->label
  (equal (step (step->to step)
               (step->label step))
         (step-fix step))
  :enable (step
           step->to
           step->label
           step-fix
           stepp
           irr-step))

;; A step is determined by its two components. The reconstruction rule above
;; stops applying once a component has been replaced by an equal term, so
;; equalities against a constructed step are decided componentwise.

(defrule equal-of-step
  (implies (step-equiv x$ (double-rewrite x))
           (equal (equal (step to label) x)
                  (and (stepp x)
                       (equal (step->to x$) to)
                       (equal (step->label x$) label))))
  :enable (step
           step->to
           step->label
           stepp))
