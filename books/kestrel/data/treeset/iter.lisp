; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "set-defs")
(include-book "min-max-defs")
(include-book "in-defs")
(include-book "internal/iter")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "set"))
(local (include-book "min-max"))
(local (include-book "internal/min-max"))
(local (include-book "in"))
(local (include-book "internal/in"))
(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/heap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc iterator
  :parents (treeset)
  :short "A position within a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Walking a @(see treeset) with @(tsee min) and @(tsee tail) is
      inefficient. An iterator walks it in order instead, one element at a
      time, at an amortized cost of @($O(1)$) per step.")
   (xdoc::p
     "An iterator sits at one of @($n+2$) positions: at one of the @($n$)
      elements, before the first, or after the last. @(tsee iter) starts at the
      first element, @(tsee next) advances, and @(tsee prev) retreats; each
      saturates at the end it runs into. @(tsee after-lastp) and @(tsee
      before-firstp) recognize the two ends, where there is no element to
      read.")
   (xdoc::p
     "An iterator carries the whole set, not just what is left of it. So
      @(tsee from-iter) recovers that set at no cost from any position, and a
      walk can go either way without having to rebuild anything.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iterp (x)
  :returns (yes/no booleanp)
  :parents (iterator)
  :short "Recognizer for @(see iterator)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "An iterator is a position within a tree which is a @(see treeset). Time
      complexity: @($O(n)$), since it checks the @(see treeset) invariants."))
  (and (tree-iter-p x)
       (setp (tree-iter-plug x))))

;;;;;;;;;;;;;;;;;;;;

(add-to-ruleset break-abstraction '(iterp))

(defrule tree-iter-p-when-iterp-forward-chaining
  (implies (iterp iter)
           (tree-iter-p iter))
  :rule-classes :forward-chaining
  :enable iterp)

(defrule setp-of-tree-iter-plug-when-iterp-forward-chaining
  (implies (iterp iter)
           (setp (tree-iter-plug iter)))
  :rule-classes :forward-chaining
  :enable iterp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter ((set setp))
  :returns (iter iterp
                 :hints (("Goal" :in-theory (enable* iterp break-abstraction))))
  :parents (iterator)
  :short "Construct an @(see iterator) over a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The iterator starts at the first element, or past the end when the
      @(see treeset) is empty.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the first element."))
  (tree-iter-next (tree-iter-before-first (fix set)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter)))

(defrule iter-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (iter set0)
                  (iter set1)))
  :rule-classes :congruence
  :enable iter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-fix ((iter iterp))
  :returns (iter$ iterp)
  :parents (iterator)
  :short "Fixer for @(see iterator)s."
  (mbe :logic (if (iterp iter) iter (iter (empty)))
       :exec iter)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-fix)))

(defrule tree-iter-p-of-iter-fix
  (tree-iter-p (iter-fix iter))
  :enable iterp
  :use iterp-of-iter-fix
  :disable iterp-of-iter-fix)

(defrule tree-iter-fix-of-iter-fix
  (equal (tree-iter-fix (iter-fix iter))
         (iter-fix iter)))

(defrule iter-fix-of-tree-iter-next-of-iter-fix
  (equal (iter-fix (tree-iter-next (iter-fix iter)))
         (tree-iter-next (iter-fix iter)))
  :enable (iterp iter-fix)
  :use ((:instance setp-of-tree-iter-plug-when-iterp-forward-chaining
                   (iter (iter-fix iter)))
        (:instance tree-in-of-tree-iter-value (iter (iter-fix iter))))
  :disable tree-iter-plug-when-tree-iter-has-value-p)

(defrule iter-fix-of-tree-iter-prev-of-iter-fix
  (equal (iter-fix (tree-iter-prev (iter-fix iter)))
         (tree-iter-prev (iter-fix iter)))
  :enable (iterp iter-fix)
  :use (:instance setp-of-tree-iter-plug-when-iterp-forward-chaining
                  (iter (iter-fix iter))))

(defrule iter-fix-when-iterp
  (implies (iterp iter)
           (equal (iter-fix iter)
                  iter))
  :enable iter-fix)

(defruled iter-fix-when-not-iterp
  (implies (not (iterp iter))
           (equal (iter-fix iter)
                  (iter (empty))))
  :enable iter-fix)

(defrule iter-fix-when-not-iterp-cheap
  (implies (not (iterp iter))
           (equal (iter-fix iter)
                  (iter (empty))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by iter-fix-when-not-iterp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-equiv
  ((x iterp)
   (y iterp))
  :returns (yes/no booleanp)
  :parents (iterator)
  :short "Equivalence up to @(tsee iter-fix)."
  (equal (iter-fix x)
         (iter-fix y))
  :inline t
  ///
  (defequiv iter-equiv
    :hints (("Goal" :in-theory (enable iter-equiv))))

  (defrule iter-fix-under-iter-equiv
    (iter-equiv (iter-fix iter)
                iter)
    :enable iter-equiv)

  (defrule iter-fix-when-iter-equiv-congruence
    (implies (iter-equiv iter0 iter1)
             (equal (iter-fix iter0)
                    (iter-fix iter1)))
    :rule-classes :congruence
    :enable iter-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The three positions. The two ends hold no value; @(tsee has-valuep) is
;; where there is one to read. Neither end is privileged: a walk in either
;; direction stops at the one it is heading towards.

(define after-lastp ((iter iterp))
  :returns (yes/no booleanp)
  :parents (iterator)
  :short "Check whether an @(see iterator) is after the last element."
  (tree-iter-after-last-p (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define before-firstp ((iter iterp))
  :returns (yes/no booleanp)
  :parents (iterator)
  :short "Check whether an @(see iterator) is before the first element."
  :long
  (xdoc::topstring
   (xdoc::p
     "Only @(tsee prev) can reach this position; @(tsee iter) never starts
      there."))
  (tree-iter-before-first-p (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define has-valuep ((iter iterp))
  :returns (yes/no booleanp)
  :parents (iterator)
  :short "Check whether an @(see iterator) has a value to read."
  (tree-iter-has-value-p (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t after-lastp) (:t before-firstp) (:t has-valuep)))

(defrule after-lastp-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (after-lastp iter0)
                  (after-lastp iter1)))
  :rule-classes :congruence
  :enable after-lastp)

(defrule before-firstp-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (before-firstp iter0)
                  (before-firstp iter1)))
  :rule-classes :congruence
  :enable before-firstp)

(defrule has-valuep-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (has-valuep iter0)
                  (has-valuep iter1)))
  :rule-classes :congruence
  :enable has-valuep)

;; Exactly one of the three holds.

(defrule has-valuep-when-neither-end
  (implies (and (not (after-lastp iter))
                (not (before-firstp iter)))
           (has-valuep iter))
  :enable (after-lastp
           before-firstp
           has-valuep))

(defrule not-after-lastp-when-has-valuep
  (implies (has-valuep iter)
           (not (after-lastp iter)))
  :enable (after-lastp
           has-valuep))

(defrule not-before-firstp-when-has-valuep
  (implies (has-valuep iter)
           (not (before-firstp iter)))
  :enable (before-firstp
           has-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-iter ((iter iterp))
  :returns (set setp
                :hints (("Goal"
                         :use
                         (:instance
                          setp-of-tree-iter-plug-when-iterp-forward-chaining
                          (iter (iter-fix iter))))))
  :parents (iterator)
  :short "The @(see treeset) an @(see iterator) walks."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the whole set, not the part an iterator has yet to reach. An
      iterator carries that set, so this costs @($O(1)$) and gives the same
      answer from every position; see @(tsee nexts) and @(tsee prevs) for how
      far it has left to go in each direction."))
  (tree-iter-plug (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-iter)))

(defrule from-iter-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (from-iter iter0)
                  (from-iter iter1)))
  :rule-classes :congruence
  :enable from-iter)

(defruledl tree-iter-plug-of-iter
  (equal (tree-iter-plug (iter set))
         (fix set))
  :hints (("Goal" :in-theory (enable* iter break-abstraction))))

(defrule from-iter-of-iter
  (equal (from-iter (iter set))
         (fix set))
  :enable (from-iter
           tree-iter-plug-of-iter))

;; A fresh iterator is at the end exactly when there is nothing to walk.

(defruledl tree-iter-after-last-p-of-iter
  (equal (tree-iter-after-last-p (iter set))
         (tree-empty-p (fix set)))
  :enable (iter
           tree-iter-next
           tree-iter-has-value-p))

(defrule after-lastp-of-iter
  (equal (after-lastp (iter set))
         (emptyp set))
  :enable (after-lastp
           emptyp
           tree-iter-after-last-p-of-iter))

;; A fresh iterator is never rewound: it is built by stepping forward from the
;; rewound position, and a step never lands there.

(defruledl tree-iter-before-first-p-of-iter
  (not (tree-iter-before-first-p (iter set)))
  :enable iter)

(defrule not-before-firstp-of-iter
  (not (before-firstp (iter set)))
  :enable (before-firstp
           tree-iter-before-first-p-of-iter))

;; So a fresh iterator is at a value exactly when there is one to be at.

(defrule has-valuep-of-iter
  (equal (has-valuep (iter set))
         (not (emptyp set)))
  :enable ((:t has-valuep))
  :use ((:instance has-valuep-when-neither-end (iter (iter set)))
        (:instance not-after-lastp-when-has-valuep (iter (iter set))))
  :disable (has-valuep-when-neither-end
            not-after-lastp-when-has-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value ((iter iterp))
  :guard (has-valuep iter)
  :parents (iterator)
  :short "The value an @(see iterator) is at."
  (tree-iter-value (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable has-valuep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t value)))

(defrule value-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (value iter0)
                  (value iter1)))
  :rule-classes :congruence
  :enable value)

;; What a walk yields first: the minimum. This is what ties the values an
;; iterator produces to the set it walks; everything else here is structural.

(defruledl tree-iter-value-of-iter
  (implies (not (tree-empty-p (fix set)))
           (equal (tree-iter-value (iter set))
                  (tree-leftmost (fix set))))
  :enable (iter
           tree-iter-next
           tree-iter-value
           tree-iter-has-value-p))

(defrule value-of-iter
  (implies (not (emptyp set))
           (equal (value (iter set))
                  (min set)))
  :hints (("Goal"
           :in-theory (enable* value min emptyp setp
                               tree-iter-value-of-iter
                               break-abstraction)
           :use ((:instance tree-leftmost-when-bstp (tree (fix set)))
                 (:instance setp-of-fix (set set))))))

;; The value an @(see iterator) is at is an element of the @(see treeset) it
;; walks. With @(tsee value-of-iter) this is what connects a walk to the
;; contents of the set rather than just to its shape.
;;
;; Both internal functions are held folded here: the public definitions unfold
;; to exactly the internal terms the lemma below is stated about, and letting
;; those rewrite any further would lose the match.

(defrule in-of-value
  (implies (has-valuep iter)
           (in (value iter) (from-iter iter)))
  :enable (value
           from-iter
           has-valuep
           in)
  :use ((:instance tree-in-of-tree-iter-value (iter (iter-fix iter)))
        (:instance setp-of-tree-iter-plug-when-iterp-forward-chaining
                   (iter (iter-fix iter))))
  :disable (tree-iter-plug
            tree-iter-plug-when-tree-iter-has-value-p
            tree-iter-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next ((iter iterp))
  :returns (iter$ iterp
                  :hints (("Goal"
                           :in-theory (enable iterp)
                           :use
                           (:instance
                            setp-of-tree-iter-plug-when-iterp-forward-chaining
                            (iter (iter-fix iter))))))
  :parents (iterator)
  :short "Advance an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Past the last element this stays put. Time complexity: @($O(\\log(n))$)
      in the worst case, @($O(1)$) amortized over a walk."))
  (tree-iter-next (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prev ((iter iterp))
  :returns (iter$ iterp
                  :hints (("Goal"
                           :in-theory (enable iterp)
                           :use
                           (:instance
                            setp-of-tree-iter-plug-when-iterp-forward-chaining
                            (iter (iter-fix iter))))))
  :parents (iterator)
  :short "Retreat an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror of @(tsee next). Before the first element this stays put."))
  (tree-iter-prev (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t next) (:t prev)))

(defrule next-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (next iter0)
                  (next iter1)))
  :rule-classes :congruence
  :enable next)

(defrule prev-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (prev iter0)
                  (prev iter1)))
  :rule-classes :congruence
  :enable prev)

;; Moving never changes the set being walked.

(defruledl tree-iter-plug-of-next
  (equal (tree-iter-plug (next iter))
         (tree-iter-plug (iter-fix iter)))
  :enable next)

(defruledl tree-iter-plug-of-prev
  (equal (tree-iter-plug (prev iter))
         (tree-iter-plug (iter-fix iter)))
  :enable prev)

(defrule from-iter-of-next
  (equal (from-iter (next iter))
         (from-iter iter))
  :enable (from-iter
           tree-iter-plug-of-next))

(defrule from-iter-of-prev
  (equal (from-iter (prev iter))
         (from-iter iter))
  :enable (from-iter
           tree-iter-plug-of-prev))

;; Each move is the identity exactly at the end it saturates against.

(defrule next-identity-iff-after-lastp
  (equal (equal (next iter) (iter-fix iter))
         (after-lastp iter))
  :enable (next
           after-lastp)
  :use (:instance tree-iter-next-identity-iff-tree-iter-after-last-p
                  (iter (iter-fix iter))))

(defrule not-before-firstp-of-next
  (not (before-firstp (next iter)))
  :enable (before-firstp
           next))

(defrule not-after-lastp-of-prev
  (not (after-lastp (prev iter)))
  :enable (after-lastp
           prev))

(defrule prev-identity-iff-before-firstp
  (equal (equal (prev iter) (iter-fix iter))
         (before-firstp iter))
  :enable (prev
           before-firstp)
  :use (:instance tree-iter-prev-identity-iff-tree-iter-before-first-p
                  (iter (iter-fix iter))))

;; The two are inverse everywhere they have somewhere to go.

(defrule prev-of-next
  (implies (not (after-lastp iter))
           (equal (prev (next iter))
                  (iter-fix iter)))
  :enable (next
           prev
           after-lastp))

(defrule next-of-prev
  (implies (not (before-firstp iter))
           (equal (next (prev iter))
                  (iter-fix iter)))
  :enable (next
           prev
           before-firstp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The measures. Each counts the moves left in one direction, so each is a
;; suitable measure for a walk that way.

(define nexts ((iter iterp))
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "The number of @(tsee next) moves an @(see iterator) has left."
  (tree-iter-nexts (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prevs ((iter iterp))
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "The number of @(tsee prev) moves an @(see iterator) has left."
  (tree-iter-prevs (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t nexts) (:t prevs)))

(defrule nexts-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (nexts iter0)
                  (nexts iter1)))
  :rule-classes :congruence
  :enable nexts)

(defrule prevs-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (prevs iter0)
                  (prevs iter1)))
  :rule-classes :congruence
  :enable prevs)

(defrule nexts-equal-0
  (equal (equal (nexts iter) 0)
         (after-lastp iter))
  :enable (nexts
           after-lastp))

(defrule prevs-equal-0
  (equal (equal (prevs iter) 0)
         (before-firstp iter))
  :enable (prevs
           before-firstp))

(defrule nexts-of-next
  (implies (not (after-lastp iter))
           (equal (nexts (next iter))
                  (- (nexts iter) 1)))
  :enable (nexts
           next
           after-lastp))

(defrule prevs-of-prev
  (implies (not (before-firstp iter))
           (equal (prevs (prev iter))
                  (- (prevs iter) 1)))
  :enable (prevs
           prev
           before-firstp))

(defrule nexts-linear
  (implies (not (after-lastp iter))
           (< (nexts (next iter))
              (nexts iter)))
  :rule-classes :linear)

(defrule prevs-linear
  (implies (not (before-firstp iter))
           (< (prevs (prev iter))
              (prevs iter)))
  :rule-classes :linear)
