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

(include-book "internal/iter")
(include-book "set-defs")
(include-book "min-max-defs")
(include-book "in-defs")
(include-book "insert-defs")
(include-book "delete-defs")
(include-book "cardinality-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/oset" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/min-max"))
(local (include-book "internal/in"))
(local (include-book "internal/heap"))
(local (include-book "internal/in-order"))
(local (include-book "set"))
(local (include-book "min-max"))
(local (include-book "insert"))
(local (include-book "in"))
(local (include-book "delete"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The rules which rewrite @(tsee tree-iter-plug) to a zipper's plug are held
;; off for this whole book: the proofs here are stated against the folded
;; form, and unfolding it loses every rule which matches it.

(local (in-theory (disable tree-iter-plug-when-tree-iter-has-value-p
                           tree-iter-plug-when-zipp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc iterator
  :parents (treeset)
  :short "A position within a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Walking a @(see treeset) with @(tsee min) and @(tsee tail) is
      inefficient. For this and other reasons, we provide iterator objects,
      which may be used to walk over the set in-order,
      one element at a time, at an amortized cost of @($O(1)$) per step.")
   (xdoc::p
     "An iterator sits at one of @($n+2$) positions: at one of the @($n$)
      elements, before the first, or after the last. @(tsee iter-min) starts at
      the first element and @(tsee iter-max) at the last; @(tsee next) advances
      and @(tsee prev) retreats, each saturating at the end it runs into.
      @(tsee after-lastp) and @(tsee before-firstp) recognize the two ends,
      where there is no element to read.")
   (xdoc::p
     "Neither direction is privileged. Over an empty @(see treeset) each
      constructor lands on the end its own walk would stop at, so a walk from
      either is immediately over.")
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

(defruled iterp-compound-recognizer
  (implies (iterp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable iterp)

(add-to-ruleset break-abstraction '(iterp-compound-recognizer))

(defruled tree-iter-p-when-iterp-forward-chaining
  (implies (iterp iter)
           (tree-iter-p iter))
  :rule-classes :forward-chaining
  :enable iterp)

(add-to-ruleset break-abstraction '(tree-iter-p-when-iterp-forward-chaining))

(defruled setp-of-tree-iter-plug-when-iterp-forward-chaining
  (implies (iterp iter)
           (setp (tree-iter-plug iter)))
  :rule-classes :forward-chaining
  :enable iterp)

(add-to-ruleset break-abstraction
                '(setp-of-tree-iter-plug-when-iterp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-min ((set setp))
  :returns (iter iterp
                 :hints (("Goal" :in-theory (enable* iterp break-abstraction))))
  :parents (iterator)
  :short "Construct an @(see iterator) at the first element of a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The iterator starts at the first element, or past the end when the
      @(see treeset) is empty.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the first element."))
  (tree-iter-min (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-min)))

(defrule iter-min-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (iter-min set0)
                  (iter-min set1)))
  :rule-classes :congruence
  :enable iter-min)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-max ((set setp))
  :returns (iter iterp
                 :hints (("Goal" :in-theory (enable* iterp break-abstraction))))
  :parents (iterator)
  :short "Construct an @(see iterator) at the last element of a @(see treeset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror of @(tsee iter-min): the iterator starts at the last element,
      or before the first when the @(see treeset) is empty. Either way it is
      the position a walk in its own direction begins from, and the empty case
      is the one where that walk is immediately over.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the last element."))
  (tree-iter-max (fix set))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-max)))

(defrule iter-max-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (iter-max set0)
                  (iter-max set1)))
  :rule-classes :congruence
  :enable iter-max)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-fix ((iter iterp))
  :returns (iter$ iterp)
  :parents (iterator)
  :short "Fixer for @(see iterator)s."
  (mbe :logic (if (iterp iter)
                  iter
                (iter-min (empty)))
       :exec iter)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-fix)))

;; Rules mentioning an internal function are disabled and registered in
;; break-abstraction, so that internal terms do not enter a caller's proof
;; unbidden.

(defruled tree-iter-p-of-iter-fix
  (tree-iter-p (iter-fix iter))
  :enable iterp
  :use iterp-of-iter-fix
  :disable iterp-of-iter-fix)

(add-to-ruleset break-abstraction '(tree-iter-p-of-iter-fix))

(defruled setp-of-tree-iter-plug-of-iter-fix
  (setp (tree-iter-plug (iter-fix iter)))
  :use (:instance setp-of-tree-iter-plug-when-iterp-forward-chaining
                  (iter (iter-fix iter))))

(add-to-ruleset break-abstraction '(setp-of-tree-iter-plug-of-iter-fix))

(defruled tree-iter-fix-of-iter-fix
  (equal (tree-iter-fix (iter-fix iter))
         (iter-fix iter))
  :enable tree-iter-p-of-iter-fix)

(add-to-ruleset break-abstraction '(tree-iter-fix-of-iter-fix))

(defruled iter-fix-of-tree-iter-next-of-iter-fix
  (equal (iter-fix (tree-iter-next (iter-fix iter)))
         (tree-iter-next (iter-fix iter)))
  :enable (iterp iter-fix)
  :use (setp-of-tree-iter-plug-of-iter-fix))

(add-to-ruleset break-abstraction '(iter-fix-of-tree-iter-next-of-iter-fix))

(defruled iter-fix-of-tree-iter-prev-of-iter-fix
  (equal (iter-fix (tree-iter-prev (iter-fix iter)))
         (tree-iter-prev (iter-fix iter)))
  :enable (iterp iter-fix)
  :use setp-of-tree-iter-plug-of-iter-fix)

(add-to-ruleset break-abstraction '(iter-fix-of-tree-iter-prev-of-iter-fix))

;; Locally these five stay enabled: the proofs in this book constantly cross
;; the boundary the rules police, and each is the identity the fixer needs.

(local (in-theory (enable tree-iter-p-of-iter-fix
                          setp-of-tree-iter-plug-of-iter-fix
                          tree-iter-fix-of-iter-fix
                          iter-fix-of-tree-iter-next-of-iter-fix
                          iter-fix-of-tree-iter-prev-of-iter-fix)))

(defrule iter-fix-when-iterp
  (implies (iterp iter)
           (equal (iter-fix iter)
                  iter))
  :enable iter-fix)

(defruled iter-fix-when-not-iterp
  (implies (not (iterp iter))
           (equal (iter-fix iter)
                  (iter-min (empty))))
  :enable iter-fix)

(defrule iter-fix-when-not-iterp-cheap
  (implies (not (iterp iter))
           (equal (iter-fix iter)
                  (iter-min (empty))))
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

  (defequiv iter-equiv)

  (defrule iter-fix-under-iter-equiv
    (iter-equiv (iter-fix iter)
                iter))

  (defrule iter-fix-when-iter-equiv-congruence
    (implies (iter-equiv iter0 iter1)
             (equal (iter-fix iter0)
                    (iter-fix iter1)))
    :rule-classes :congruence))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The three positions. The two ends hold no value; @(tsee has-valuep) is
;; where there is one to read. Neither end is privileged: a walk in either
;; direction stops at the one it is heading towards.

(define after-lastp ((iter iterp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (iterator)
  :short "Check whether an @(see iterator) is after the last element."
  (tree-iter-after-last-p (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define before-firstp ((iter iterp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (iterator)
  :short "Check whether an @(see iterator) is before the first element."
  :long
  (xdoc::topstring
   (xdoc::p
     "A forward walk never reaches this position: neither @(tsee iter-min) nor
      @(tsee next) yields it. It is reached by @(tsee prev), or by @(tsee
      iter-max) over an empty @(see treeset), where a backward walk is over
      before it begins."))
  (tree-iter-before-first-p (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define has-valuep ((iter iterp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (iterator)
  :short "Check whether an @(see iterator) has a value to read."
  ;; The logical value could instead be defined as the conjunction of (not
  ;; (before-firstp iter)) and (not (after-lastp iter)). We keep the direct
  ;; form: the trichotomy is available as rewrite rules below, and the direct
  ;; form keeps this definition independent of the other two.
  (tree-iter-has-value-p (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

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
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :enable (after-lastp
           before-firstp
           has-valuep))

(defrule not-after-lastp-when-has-valuep
  (implies (has-valuep iter)
           (not (after-lastp iter)))
  :rule-classes (:rewrite :forward-chaining)
  :enable (after-lastp
           has-valuep))

(defrule not-before-firstp-when-has-valuep
  (implies (has-valuep iter)
           (not (before-firstp iter)))
  :rule-classes (:rewrite :forward-chaining)
  :enable (before-firstp
           has-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-iter ((iter iterp))
  :returns (set setp
                :hints (("Goal"
                         :in-theory
                         (enable setp-of-tree-iter-plug-of-iter-fix))))
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

(defruledl iter-fix-of-tree-iter-min-of-fix
  (equal (iter-fix (tree-iter-min (fix set)))
         (tree-iter-min (fix set)))
  :enable ( iterp break-abstraction))

(defruledl iter-fix-of-tree-iter-max-of-fix
  (equal (iter-fix (tree-iter-max (fix set)))
         (tree-iter-max (fix set)))
  :enable ( iterp break-abstraction))

(defrule from-iter-of-iter-min
  (equal (from-iter (iter-min set))
         (fix set))
  :enable (from-iter
           iter-min
           iter-fix-of-tree-iter-min-of-fix
           break-abstraction))

;; An @(tsee iter-min) iterator is past the end exactly when the set is empty:
;; with nothing to walk, a forward walk is over before it begins.

(defrule after-lastp-of-iter-min
  (equal (after-lastp (iter-min set))
         (emptyp set))
  :enable (after-lastp
           emptyp
           iter-min
           iter-fix-of-tree-iter-min-of-fix))

;; An @(tsee iter-min) iterator is never rewound: it is built by stepping
;; forward from the rewound position, and a step never lands there.

(defrule not-before-firstp-of-iter-min
  (not (before-firstp (iter-min set)))
  :enable (before-firstp
           iter-min
           iter-fix-of-tree-iter-min-of-fix))

;; So an @(tsee iter-min) iterator is at a value exactly when there is one to
;; be at.

(defrule has-valuep-of-iter-min
  (equal (has-valuep (iter-min set))
         (not (emptyp set)))
  :use ((:instance has-valuep-when-neither-end (iter (iter-min set)))
        (:instance not-after-lastp-when-has-valuep (iter (iter-min set))))
  :disable has-valuep-when-neither-end)

;;;;;;;;;;;;;;;;;;;;

;; The same four facts for @(tsee iter-max), with the two ends exchanged.

(defrule from-iter-of-iter-max
  (equal (from-iter (iter-max set))
         (fix set))
  :enable (from-iter
           iter-max
           iter-fix-of-tree-iter-max-of-fix
           break-abstraction))

(defrule before-firstp-of-iter-max
  (equal (before-firstp (iter-max set))
         (emptyp set))
  :enable (before-firstp
           emptyp
           iter-max
           iter-fix-of-tree-iter-max-of-fix))

(defrule not-after-lastp-of-iter-max
  (not (after-lastp (iter-max set)))
  :enable (after-lastp
           iter-max
           iter-fix-of-tree-iter-max-of-fix))

(defrule has-valuep-of-iter-max
  (equal (has-valuep (iter-max set))
         (not (emptyp set)))
  :use ((:instance has-valuep-when-neither-end (iter (iter-max set)))
        (:instance not-before-firstp-when-has-valuep (iter (iter-max set))))
  :disable has-valuep-when-neither-end)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The set on each side of an iterator. Both exclude the value it is at, so the
;; two are disjoint and, with that value, account for the whole set; at an end,
;; where there is no value, they account for it between them.
;;
;; The sequences these are built from are already ordered, so an oset is
;; exactly what they are; @(tsee from-oset) only changes the representation.

;; Over a search tree each side's built tree and its oset denote the same
;; elements, and treesets are canonical, so they are the same object. This is
;; what lets the builders serve as the executable branch below while the
;; logical definitions stay on the osets.

(defruledl tree-iter-tree-before-becomes-from-oset
  (implies (setp (tree-iter-plug iter))
           (equal (tree-iter-tree-before iter)
                  (from-oset (tree-iter-oset-before iter))))
  :enable (extensionality
           setp
           in))

(defruledl tree-iter-tree-after-becomes-from-oset
  (implies (setp (tree-iter-plug iter))
           (equal (tree-iter-tree-after iter)
                  (from-oset (tree-iter-oset-after iter))))
  :enable (extensionality
           setp
           in))

(define before ((iter iterp))
  :returns (set setp)
  :parents (iterator)
  :short "The @(see treeset) of elements before an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The elements a forward walk has already passed. This excludes the value
      the iterator is at: that one has not been passed yet.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) expected. The result is built with
      one fresh node per step of the iterator's path; every subtree hangs off
      the underlying set unchanged."))
  (mbe :logic (from-oset (tree-iter-oset-before (iter-fix iter)))
       :exec (tree-iter-tree-before (iter-fix iter)))
  :guard-hints
  (("Goal"
    :in-theory (enable* tree-iter-tree-before-becomes-from-oset
                        break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t before)))

(defrule before-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (before iter0)
                  (before iter1)))
  :rule-classes :congruence
  :enable before)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define after ((iter iterp))
  :returns (set setp)
  :parents (iterator)
  :short "The @(see treeset) of elements after an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The elements a forward walk has yet to reach. This excludes the value the
      iterator is at, so it is what remains strictly after the current step.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) expected. The result is built with
      one fresh node per step of the iterator's path; every subtree hangs off
      the underlying set unchanged."))
  (mbe :logic (from-oset (tree-iter-oset-after (iter-fix iter)))
       :exec (tree-iter-tree-after (iter-fix iter)))
  :guard-hints
  (("Goal"
    :in-theory (enable* tree-iter-tree-after-becomes-from-oset
                        break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t after)))

(defrule after-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (after iter0)
                  (after iter1)))
  :rule-classes :congruence
  :enable after)

;;;;;;;;;;;;;;;;;;;;

;; Each side is empty at its own end, and at the constructor which starts a
;; walk in that direction. Together with the step laws these say what a walk
;; begins and ends with: nothing behind it, and finally nothing ahead.

(defrule before-when-before-firstp
  (implies (before-firstp iter)
           (equal (before iter)
                  (empty)))
  ;; Enabling (:e empty) follows the precedent in set.lisp, which keeps it out
  ;; of break-abstraction and enables it pointwise where (empty) must compute.
  :enable (before
           before-firstp
           tree-iter-oset-before
           tree-iter-tree-before
           (:e empty)))

(defrule after-when-after-lastp
  (implies (after-lastp iter)
           (equal (after iter)
                  (empty)))
  :enable (after
           after-lastp
           tree-iter-oset-after
           tree-iter-tree-after
           (:e empty)))

;; At the constructors the same holds with no hypothesis, including over the
;; empty @(see treeset), where the iterator lands on the far end and the side
;; in question is empty for the other reason.

(defrule before-of-iter-min
  (equal (before (iter-min set))
         (empty))
  :enable (before
           iter-min
           iter-fix-of-tree-iter-min-of-fix
           tree-iter-oset-before-when-not-consp-of-tree-iter-before
           (:e empty)))

(defrule after-of-iter-max
  (equal (after (iter-max set))
         (empty))
  :enable (after
           iter-max
           iter-fix-of-tree-iter-max-of-fix
           tree-iter-oset-after-when-not-consp-of-tree-iter-after
           (:e empty)))

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

(defrule value-of-iter-min
  (implies (not (emptyp set))
           (equal (value (iter-min set))
                  (min set)))
  :enable (value min iter-min
           iter-fix-of-tree-iter-min-of-fix
           break-abstraction))

;; And symmetrically, what a backward walk yields first: the maximum.

(defrule value-of-iter-max
  (implies (not (emptyp set))
           (equal (value (iter-max set))
                  (max set)))
  :enable (value max iter-max
           iter-fix-of-tree-iter-max-of-fix
           break-abstraction))

;; The value an @(see iterator) is at is an element of the @(see treeset) it
;; walks. With @(tsee value-of-iter-min) this is what connects a walk to the
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
           in))

;;;;;;;;;;;;;;;;;;;;

;; The tree an iterator is a position in is a search tree. This is what makes
;; the two sequences ordered, and so makes them osets. The rule cannot live in
;; an internal book because @(tsee iter-fix) is a public function; it is the
;; bst half of setp-of-tree-iter-plug-of-iter-fix, projected out because the
;; internal ordering lemmas hypothesize @(tsee bstp) alone.

(defruledl bstp-of-tree-iter-plug-of-iter-fix
  (bstp (tree-iter-plug (iter-fix iter)))
  :use setp-of-tree-iter-plug-of-iter-fix
  :enable bstp-when-setp-forward-chaining)

;; Membership on each side, at each level of representation: the oset the side
;; is defined from, and the ordered element list that oset is read off of. The
;; walk's step laws are proved by extensionality over those element lists,
;; whose membership is @(tsee member-equal); the -member-equal rules carry a
;; set membership question all the way down to that level. Left disabled:
;; crossing from sets back to the underlying sequences is only what a proof
;; about the order of a walk wants.

(defruled in-of-before-becomes-set-in
  (equal (in x (before iter))
         (set::in x (tree-iter-oset-before (iter-fix iter))))
  :enable before)

(add-to-ruleset break-abstraction '(in-of-before-becomes-set-in))

(defruled in-of-after-becomes-set-in
  (equal (in x (after iter))
         (set::in x (tree-iter-oset-after (iter-fix iter))))
  :enable after)

(add-to-ruleset break-abstraction '(in-of-after-becomes-set-in))

(defruled in-of-before-becomes-member-equal
  (equal (in x (before iter))
         (and (member-equal x (tree-iter-before (iter-fix iter))) t))
  :enable in-of-before-becomes-set-in)

(add-to-ruleset break-abstraction '(in-of-before-becomes-member-equal))

(defruled in-of-after-becomes-member-equal
  (equal (in x (after iter))
         (and (member-equal x (tree-iter-after (iter-fix iter))) t))
  :enable in-of-after-becomes-set-in)

(add-to-ruleset break-abstraction '(in-of-after-becomes-member-equal))

;;;;;;;;;;;;;;;;;;;;

;; The iteration follows the set order: the value an iterator is at lies above
;; everything behind it and below everything ahead of it. These are what tie a
;; traversal's order to @(tsee <<); the laws below are all consequences.
;;
;; These read straight off the filter characterizations: each side collects
;; the elements of the set on its own side of the value. The rules which
;; rewrite @(tsee tree-iter-plug) to a zipper's plug are held off so that the
;; @(tsee bstp) hypothesis keeps its folded form.

(defrule <<-of-value-when-in-of-after
  (implies (and (has-valuep iter)
                (in x (after iter)))
           (<< (value iter) x))
  :enable (value
           has-valuep
           in-of-after-becomes-set-in
           bstp-of-tree-iter-plug-of-iter-fix)
  :disable in-of-tree-iter-oset-after)

(defrule <<-of-arg1-and-value-when-in-of-before
  (implies (and (has-valuep iter)
                (in x (before iter)))
           (<< x (value iter)))
  :enable (value
           has-valuep
           in-of-before-becomes-set-in
           bstp-of-tree-iter-plug-of-iter-fix)
  :disable in-of-tree-iter-oset-before)

;; So the value is on neither side, and the sides are disjoint.

(defrule not-in-of-value-and-before
  (implies (has-valuep iter)
           (not (in (value iter) (before iter))))
  :use (:instance <<-of-arg1-and-value-when-in-of-before (x (value iter)))
  :disable <<-of-arg1-and-value-when-in-of-before
  :enable data::<<-rules)

(defrule not-in-of-value-and-after
  (implies (has-valuep iter)
           (not (in (value iter) (after iter))))
  :use (:instance <<-of-value-when-in-of-after (x (value iter)))
  :disable <<-of-value-when-in-of-after
  :enable data::<<-rules)

(defrule not-in-of-after-when-in-of-before
  (implies (and (has-valuep iter)
                (in x (before iter)))
           (not (in x (after iter))))
  :use (<<-of-value-when-in-of-after
        <<-of-arg1-and-value-when-in-of-before)
  :disable (<<-of-value-when-in-of-after
            <<-of-arg1-and-value-when-in-of-before)
  :enable data::<<-rules)

;; The same split at the public layer: the two sides and the value account for
;; the set, and since the sides exclude the value they do so without overlap.
;;
;; Both rules which rewrite @(tsee tree-iter-plug) to a zipper's plug are held
;; off, so that the term still matches the lemma above.

;; Membership in the whole set, in the same folded form. Like the -becomes-
;; rules above, this carries the public membership question down to the level
;; where the internal split lemma is stated; having it as its own rule is what
;; lets the split below leave @(tsee in) alone, so that the two rules above
;; are the only thing rewriting the sides.

(defruledl in-of-from-iter-becomes-tree-in
  (equal (in x (from-iter iter))
         (and (tree-in x (tree-iter-plug (iter-fix iter))) t))
  :enable (in
           from-iter))

(defrule in-of-from-iter-when-has-valuep
  (implies (has-valuep iter)
           (equal (in x (from-iter iter))
                  (or (in x (before iter))
                      (equal x (value iter))
                      (in x (after iter)))))
  :enable (in-of-before-becomes-member-equal
           in-of-after-becomes-member-equal
           in-of-from-iter-becomes-tree-in
           tree-in-of-tree-iter-plug-split
           value
           has-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule after-of-iter-min
  (equal (after (iter-min set))
         (delete (min set) set))
  :cases ((emptyp set))
  :enable extensionality
  :use ((:instance in-of-from-iter-when-has-valuep
                   (iter (iter-min set))
                   (x (ext-equal-witness (after (iter-min set))
                                         (delete (min set) set))))
        (:instance not-in-of-value-and-after
                   (iter (iter-min set))))
  :disable (in-of-from-iter-when-has-valuep
            not-in-of-value-and-after))

(defrule before-of-iter-max
  (equal (before (iter-max set))
         (delete (max set) set))
  :cases ((emptyp set))
  :enable extensionality
  :use ((:instance in-of-from-iter-when-has-valuep
                   (iter (iter-max set))
                   (x (ext-equal-witness (before (iter-max set))
                                         (delete (max set) set))))
        (:instance not-in-of-value-and-before
                   (iter (iter-max set))))
  :disable (in-of-from-iter-when-has-valuep
            not-in-of-value-and-before))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next ((iter iterp))
  :guard (not (after-lastp iter))
  :returns (iter$ iterp
                  :hints (("Goal"
                           :in-theory
                           (enable iterp
                                   setp-of-tree-iter-plug-of-iter-fix))))
  :parents (iterator)
  :short "Advance an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Past the last element this stays put. Time complexity: @($O(\\log(n))$)
      in the worst case, @($O(1)$) amortized over a walk."))
  (tree-iter-next (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable after-lastp))))

;; A step forward moves the value across the cut: what lies behind gains it.

(defrule before-of-next
  (implies (has-valuep iter)
           (equal (before (next iter))
                  (insert (value iter) (before iter))))
  :enable (extensionality
           in-of-before-becomes-member-equal
           next
           value
           has-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prev ((iter iterp))
  :guard (not (before-firstp iter))
  :returns (iter$ iterp
                  :hints (("Goal"
                           :in-theory
                           (enable iterp
                                   setp-of-tree-iter-plug-of-iter-fix))))
  :parents (iterator)
  :short "Retreat an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror of @(tsee next). Before the first element this stays put."))
  (tree-iter-prev (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable before-firstp))))

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

;;;;;;;;;;;;;;;;;;;;

;; A step drops the element it moves onto from what lies ahead. This is the law
;; a walk's proof runs on: it says each step makes progress, and says it as a
;; @(tsee delete) rather than as a fact about the underlying sequence.
;;
;; An oset has no duplicates, so dropping the head of the sequence is deleting
;; that one element from the set it denotes.

(defrule after-of-next
  (implies (has-valuep (next iter))
           (equal (after (next iter))
                  (delete (value (next iter)) (after iter))))
  :enable (extensionality
           in-of-after-becomes-member-equal
           data::member-equal-of-cdr-when-osetp
           bstp-of-tree-iter-plug-of-iter-fix
           next
           value
           has-valuep))

;; The mirror, stated the way the sequence law is: a step back does not have a
;; @(tsee delete) form as cheap as the one above, because dropping the last
;; element of an ordered list is not a @(tsee cdr). Read right to left this
;; says the same thing -- what lies behind loses exactly the value stepped
;; back onto.

(defrule before-becomes-insert-of-before-of-prev
  (implies (has-valuep (prev iter))
           (equal (before iter)
                  (insert (value (prev iter)) (before (prev iter)))))
  :enable (extensionality
           in-of-before-becomes-member-equal
           prev
           value
           has-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A step forward has a value to land on exactly when something lies ahead,
;; and the value it lands on is the least of what lay ahead. So a forward walk
;; visits the elements in @(tsee <<) order, from the least on up.

(defrule has-valuep-of-next
  (equal (has-valuep (next iter))
         (not (emptyp (after iter))))
  :enable (not
           after
           has-valuep
           next))

;; The proof characterizes the minimum through its defchoose witness (the
;; equal-of-min-becomes-sk machinery); the two instances place the witness in
;; the sequence and rule out the empty side.
(defrule value-of-next
  (implies (has-valuep (next iter))
           (equal (value (next iter))
                  (min (after iter))))
  :enable (equal-of-min-becomes-sk
           not-<<-all-l-sk
           in-of-after-becomes-member-equal
           bstp-of-tree-iter-plug-of-iter-fix
           value
           next
           has-valuep
           data::<<-rules)
  :use ((:instance data::<<-of-car-when-member-equal-of-cdr
                   (data::l (tree-iter-after (iter-fix iter)))
                   (data::x (not-<<-all-l-sk-witness
                              (after iter)
                              (car (tree-iter-after (iter-fix iter))))))
        (:instance in-when-emptyp
                   (x (car (tree-iter-after (iter-fix iter))))
                   (set (after iter)))))

;; The step law again, phrased on the position stepped from rather than the
;; position landed on: what lies ahead loses its least element. Unlike @(tsee
;; after-of-next) this covers the step off the last element, where what lay
;; ahead was already empty and stays so.

(defrule after-of-next-when-has-valuep
  (implies (has-valuep iter)
           (equal (after (next iter))
                  (delete (min (after iter)) (after iter))))
  :cases ((has-valuep (next iter)))
  :enable (
           extensionality)
  :use ((:instance has-valuep-when-neither-end (iter (next iter))))
  :disable has-valuep-when-neither-end)

;;;;;;;;;;;;;;;;;;;;

;; The mirror laws for a step back. What lies ahead gains the value stepped
;; away from; a step back has a value to land on exactly when something lies
;; behind; and the value it lands on is the greatest of what lay behind. So a
;; backward walk visits the elements in reverse @(tsee <<) order.

(defrule after-of-prev
  (implies (has-valuep iter)
           (equal (after (prev iter))
                  (insert (value iter) (after iter))))
  :enable (extensionality
           in-of-after-becomes-member-equal
           prev
           value
           has-valuep))

(defrule has-valuep-of-prev
  (equal (has-valuep (prev iter))
         (not (emptyp (before iter))))
  :enable (not
           before
           has-valuep
           prev))

;; Left disabled: with @(tsee before-becomes-insert-of-before-of-prev) it
;; loops, since that rule introduces the very @(tsee value) term this one
;; rewrites back into a @(tsee before) term.

(defruled value-of-prev
  (implies (has-valuep (prev iter))
           (equal (value (prev iter))
                  (max (before iter))))
  :enable (data::binary-max-<<
           data::<<-rules)
  :use ((:instance <<-of-arg1-and-value-when-in-of-before
                   (iter (prev iter))
                   (x (max (before (prev iter))))))
  :disable <<-of-arg1-and-value-when-in-of-before)

(theory-invariant
  (incompatible! (:rewrite value-of-prev)
                 (:rewrite before-becomes-insert-of-before-of-prev)))

(defrule before-of-prev-when-has-valuep
  (implies (has-valuep iter)
           (equal (before (prev iter))
                  (delete (max (before iter)) (before iter))))
  :cases ((has-valuep (prev iter)))
  ;; The hint load is forced by the rewrite loop between value-of-prev and
  ;; before-becomes-insert-of-before-of-prev: the proof needs both, so one
  ;; must arrive by :use. The other instances each carry one case: the
  ;; trichotomy puts a valueless prev at the rewound end, and the
  ;; disjointness instance discharges the delete of the absent maximum.
  :enable (
           extensionality)
  :use ((:instance value-of-prev)
        (:instance not-in-of-value-and-before (iter (prev iter)))
        (:instance has-valuep-when-neither-end (iter (prev iter)))
        (:instance has-valuep-of-prev))
  :disable (not-in-of-value-and-before
            has-valuep-when-neither-end
            has-valuep-of-prev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The measures. Each counts the moves left in one direction, so each is a
;; suitable measure for a walk that way.

(define nexts ((iter iterp))
  (declare (xargs :type-prescription :none))
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "The number of @(tsee next) moves an @(see iterator) has left."
  (tree-iter-nexts (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prevs ((iter iterp))
  (declare (xargs :type-prescription :none))
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (iterator)
  :short "The number of @(tsee prev) moves an @(see iterator) has left."
  (tree-iter-prevs (iter-fix iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

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

;; The measures against the public sets: the moves left in a direction are one
;; more than the count of elements on that side. Behind the fixer the plug is
;; a search tree, so cardinality and sequence length agree. Left disabled:
;; termination proofs run on the decrement laws above, which match the
;; measures folded.

(defruled nexts-becomes-cardinality-of-after
  (implies (not (after-lastp iter))
           (equal (nexts iter)
                  (+ 1 (cardinality (after iter)))))
  :enable (nexts
           after
           after-lastp
           tree-iter-nexts
           data::cardinality-becomes-len-when-osetp
           tree-iter-oset-after-becomes-tree-iter-after
           bstp-of-tree-iter-plug-of-iter-fix))


(defruled prevs-becomes-cardinality-of-before
  (implies (not (before-firstp iter))
           (equal (prevs iter)
                  (+ 1 (cardinality (before iter)))))
  :enable (prevs
           before
           before-firstp
           tree-iter-prevs
           data::cardinality-becomes-len-when-osetp
           tree-iter-oset-before-becomes-tree-iter-before
           bstp-of-tree-iter-plug-of-iter-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Uniqueness. Two iterators are equal exactly when they walk the same set and
;; sit at the same position: both before the first, both after the last, or
;; both at an element and at the same element. At an element this is the
;; zipper's own uniqueness; the two positions past the ends carry nothing but
;; their tree, so each is recovered from that tree alone.

(defrule iter-uniqueness-when-before-firstp
  (implies (and (iterp iter1)
                (iterp iter2)
                (before-firstp iter1)
                (before-firstp iter2)
                (equal (from-iter iter1) (from-iter iter2)))
           (equal iter1 iter2))
  :rule-classes nil
  :enable (before-firstp from-iter break-abstraction)
  :use ((:instance tree-iter-fix-when-tree-iter-before-first-p (iter iter1))
        (:instance tree-iter-fix-when-tree-iter-before-first-p (iter iter2))))

(defrule iter-uniqueness-when-after-lastp
  (implies (and (iterp iter1)
                (iterp iter2)
                (after-lastp iter1)
                (after-lastp iter2)
                (equal (from-iter iter1) (from-iter iter2)))
           (equal iter1 iter2))
  :rule-classes nil
  :enable (after-lastp from-iter break-abstraction)
  :use ((:instance tree-iter-fix-when-tree-iter-after-last-p (iter iter1))
        (:instance tree-iter-fix-when-tree-iter-after-last-p (iter iter2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule iter-uniqueness
  (implies (and (iterp iter1)
                (iterp iter2)
                (equal (from-iter iter1) (from-iter iter2))
                (or (and (before-firstp iter1) (before-firstp iter2))
                    (and (after-lastp iter1) (after-lastp iter2))
                    (and (has-valuep iter1)
                         (has-valuep iter2)
                         (equal (value iter1) (value iter2)))))
           (equal iter1 iter2))
  :rule-classes nil
  :use (iter-uniqueness-when-before-firstp
        iter-uniqueness-when-after-lastp
        (:instance zip-uniqueness-when-same-value (zip1 iter1) (zip2 iter2)))
  :enable (from-iter
           value
           has-valuep
           tree-iter-value
           iterp
           setp
           tree-iter-plug-when-tree-iter-has-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled equal-of-iters-no-double-rewrite
  (implies (and (iterp iter1)
                (iterp iter2))
           (equal (equal iter1 iter2)
                  (and (equal (from-iter iter1)
                              (from-iter iter2))
                       (or (and (before-firstp iter1)
                                (before-firstp iter2))
                           (and (after-lastp iter1)
                                (after-lastp iter2))
                           (and (has-valuep iter1)
                                (has-valuep iter2)
                                (equal (value iter1)
                                       (value iter2)))))))
  :use iter-uniqueness)

(defruled equal-of-iters
  (implies (and (iterp iter1)
                (iterp iter2)
                (iter-equiv iter1$ (double-rewrite iter1))
                (iter-equiv iter2$ (double-rewrite iter2)))
           (equal (equal iter1 iter2)
                  (and (equal (from-iter iter1$)
                              (from-iter iter2$))
                       (or (and (before-firstp iter1$)
                                (before-firstp iter2$))
                           (and (after-lastp iter1$)
                                (after-lastp iter2$))
                           (and (has-valuep iter1$)
                                (has-valuep iter2$)
                                (equal (value iter1$)
                                       (value iter2$)))))))
  :use equal-of-iters-no-double-rewrite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled equal-of-iters-when-has-valuep-no-double-rewrite
  (implies (and (iterp iter1)
                (iterp iter2)
                (has-valuep iter1)
                (has-valuep iter2))
           (equal (equal iter1 iter2)
                  (and (equal (from-iter iter1)
                              (from-iter iter2))
                       (equal (value iter1)
                              (value iter2)))))
  :enable equal-of-iters)

(defruled equal-of-iters-when-has-valuep
  (implies (and (iterp iter1)
                (iterp iter2)
                (iter-equiv iter1$ (double-rewrite iter1))
                (iter-equiv iter2$ (double-rewrite iter2))
                (has-valuep iter1)
                (has-valuep iter2))
           (equal (equal iter1 iter2)
                  (and (equal (from-iter iter1)
                              (from-iter iter2))
                       (equal (value iter1)
                              (value iter2)))))
  :use equal-of-iters-when-has-valuep-no-double-rewrite)