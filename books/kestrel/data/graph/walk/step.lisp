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

;; A step of a walk is the target node of an edge together with its label: an
;; edge without its source, which is the node the walk is at before the step.
;; Neither part is constrained, so this is just a cons.
;;
;; The slot order is that of the target and label in an edge, so the tail of
;; an edge is a step, and an edge is a cons of its source onto a step.

(define stepp (x)
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (walks)
  :short "Recognizer for the steps of a walk in a @(see graph)."
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-listp (x)
  :returns (yes/no booleanp)
  :parents (stepp)
  :short "Recognizer for true lists of steps."
  (if (consp x)
      (and (stepp (car x))
           (step-listp (cdr x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;

(defrule step-listp-of-cons
  (equal (step-listp (cons step steps))
         (and (stepp step)
              (step-listp steps)))
  :enable step-listp)

(defrule step-listp-when-not-consp
  (implies (not (consp steps))
           (equal (step-listp steps)
                  (equal steps nil)))
  :enable step-listp)

(defrule stepp-of-car-when-step-listp
  (implies (and (step-listp steps)
                (consp steps))
           (stepp (car steps)))
  :enable step-listp)

(defrule step-listp-of-cdr-when-step-listp
  (implies (step-listp steps)
           (step-listp (cdr steps)))
  :enable step-listp)

(defrule true-listp-when-step-listp
  (implies (step-listp steps)
           (true-listp steps))
  :rule-classes (:rewrite :compound-recognizer)
  :induct t
  :enable step-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-list-fix ((steps step-listp))
  :returns (steps$ step-listp)
  :parents (step-listp)
  :short "Fixer for lists of steps."
  (mbe :logic (if (consp steps)
                  (cons (step-fix (car steps))
                        (step-list-fix (cdr steps)))
                nil)
       :exec steps)
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;

(defrule step-list-fix-when-step-listp
  (implies (step-listp steps)
           (equal (step-list-fix steps)
                  steps))
  :induct t
  :enable step-list-fix)

(verify-guards step-list-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-list-equiv
  ((x step-listp)
   (y step-listp))
  :type-prescription :none
  :returns (yes/no booleanp)
  :parents (step-listp)
  :short "Equivalence of lists of steps up to @(tsee step-list-fix)."
  (equal (step-list-fix x)
         (step-list-fix y))
  :inline t

  ///
  (defequiv step-list-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule step-list-equiv-type-prescription
  (booleanp (step-list-equiv x y))
  :rule-classes ((:type-prescription :typed-term (step-list-equiv x y))))

(defrule step-list-fix-when-step-list-equiv-congruence
  (implies (step-list-equiv steps0 steps1)
           (equal (step-list-fix steps0)
                  (step-list-fix steps1)))
  :rule-classes :congruence
  :enable step-list-equiv)

(defrule step-list-fix-under-step-list-equiv
  (step-list-equiv (step-list-fix steps)
                   steps)
  :enable step-list-equiv)

(defrule cons-when-step-equiv-of-arg1-congruence
  (implies (step-equiv step0 step1)
           (step-list-equiv (cons step0 steps)
                            (cons step1 steps)))
  :rule-classes :congruence
  :enable (step-list-equiv
           step-list-fix))

(defrule cons-when-step-list-equiv-of-arg2-congruence
  (implies (step-list-equiv steps0 steps1)
           (step-list-equiv (cons step steps0)
                            (cons step steps1)))
  :rule-classes :congruence
  :enable (step-list-equiv
           step-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule step-list-fix-of-cons
  (equal (step-list-fix (cons step steps))
         (cons (step-fix step)
               (step-list-fix steps)))
  :enable step-list-fix)

(defrule step-list-fix-when-not-consp
  (implies (not (consp steps))
           (equal (step-list-fix steps)
                  nil))
  :enable step-list-fix)

(defrule consp-of-step-list-fix
  (equal (consp (step-list-fix steps))
         (consp steps))
  :expand ((step-list-fix steps)))

(defrule car-of-step-list-fix
  (equal (car (step-list-fix steps))
         (if (consp steps)
             (step-fix (car steps))
           nil))
  :expand ((step-list-fix steps)))

(defrule cdr-of-step-list-fix
  (equal (cdr (step-list-fix steps))
         (step-list-fix (cdr steps)))
  :expand ((step-list-fix steps)))

(defrule step-listp-of-append
  (implies (and (step-listp steps0)
                (step-listp steps1))
           (step-listp (append steps0 steps1)))
  :induct t
  :enable append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The node a list of steps ends at, when taken from the given node.

(define steps-end (from (steps step-listp))
  :parents (step-listp)
  (if (consp steps)
      (steps-end (step->to (car steps)) (cdr steps))
    from))

;;;;;;;;;;;;;;;;;;;;

(defrule steps-end-of-append
  (equal (steps-end from (append steps0 steps1))
         (steps-end (steps-end from steps0) steps1))
  :induct t
  :enable (steps-end
           append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy step-extra-rules
  '(step-fix-when-not-stepp))
