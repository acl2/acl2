; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "internal/iter")
(include-book "map-defs")
(include-book "min-max-defs")
(include-book "in-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "update-defs")
(include-book "delete-defs")
(include-book "size-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "std/omaps/extensionality" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "std/omaps/inverse" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "internal/tree"))
(local (include-book "internal/bst"))
(local (include-book "internal/min-max"))
(local (include-book "internal/keys"))
(local (include-book "internal/lookup"))
(local (include-book "internal/heap"))
(local (include-book "internal/in-order"))
(local (include-book "map"))
(local (include-book "min-max"))
(local (include-book "update"))
(local (include-book "keys"))
(local (include-book "lookup"))
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
  :parents (treemap)
  :short "A position within a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Walking a @(see treemap) with @(tsee min) and @(tsee tail) is
      inefficient. For this and other reasons, we provide iterator objects,
      which may be used to walk over the map in-order,
      one entry at a time, at an amortized cost of @($O(1)$) per step.")
   (xdoc::p
     "An iterator sits at one of @($n+2$) positions: at one of the @($n$)
      entries, before the first, or after the last. @(tsee iter-min) starts at
      the first element and @(tsee iter-max) at the last; @(tsee next) advances
      and @(tsee prev) retreats, each saturating at the end it runs into.
      @(tsee after-lastp) and @(tsee before-firstp) recognize the two ends,
      where there is no entry to read.")
   (xdoc::p
     "Neither direction is privileged. Over an empty @(see treemap) each
      constructor lands on the end its own walk would stop at, so a walk from
      either is immediately over.")
   (xdoc::p
     "An iterator carries the whole map, not just what is left of it. So
      @(tsee from-iter) recovers that map at no cost from any position, and a
      walk can go either way without having to rebuild anything.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iterp (x)
  :returns (yes/no booleanp)
  :parents (iterator)
  :short "Recognizer for @(see iterator)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "An iterator is a position within a tree which is a @(see treemap). Time
      complexity: @($O(n)$), since it checks the @(see treemap) invariants."))
  (and (tree-iter-p x)
       (mapp (tree-iter-plug x))))

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

(defruled mapp-of-tree-iter-plug-when-iterp-forward-chaining
  (implies (iterp iter)
           (mapp (tree-iter-plug iter)))
  :rule-classes :forward-chaining
  :enable iterp)

(add-to-ruleset break-abstraction
                '(mapp-of-tree-iter-plug-when-iterp-forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-min ((map mapp))
  :returns (iter iterp
                 :hints (("Goal" :in-theory (enable* iterp break-abstraction))))
  :parents (iterator)
  :short "Construct an @(see iterator) at the first entry of a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The iterator starts at the first entry, or past the end when the
      @(see treemap) is empty.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the first entry."))
  (tree-iter-min (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-min)))

(defrule iter-min-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (iter-min map0)
                  (iter-min map1)))
  :rule-classes :congruence
  :enable iter-min)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-max ((map mapp))
  :returns (iter iterp
                 :hints (("Goal" :in-theory (enable* iterp break-abstraction))))
  :parents (iterator)
  :short "Construct an @(see iterator) at the last entry of a @(see treemap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror of @(tsee iter-min): the iterator starts at the last entry,
      or before the first when the @(see treemap) is empty. Either way it is
      the position a walk in its own direction begins from, and the empty case
      is the one where that walk is immediately over.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$), to descend to the last entry."))
  (tree-iter-max (fix map))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t iter-max)))

(defrule iter-max-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (iter-max map0)
                  (iter-max map1)))
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

(defruled mapp-of-tree-iter-plug-of-iter-fix
  (mapp (tree-iter-plug (iter-fix iter)))
  :use (:instance mapp-of-tree-iter-plug-when-iterp-forward-chaining
                  (iter (iter-fix iter))))

(add-to-ruleset break-abstraction '(mapp-of-tree-iter-plug-of-iter-fix))

(defruled tree-iter-fix-of-iter-fix
  (equal (tree-iter-fix (iter-fix iter))
         (iter-fix iter))
  :enable tree-iter-p-of-iter-fix)

(add-to-ruleset break-abstraction '(tree-iter-fix-of-iter-fix))

(defruled iter-fix-of-tree-iter-next-of-iter-fix
  (equal (iter-fix (tree-iter-next (iter-fix iter)))
         (tree-iter-next (iter-fix iter)))
  :enable (iterp iter-fix)
  :use (mapp-of-tree-iter-plug-of-iter-fix))

(add-to-ruleset break-abstraction '(iter-fix-of-tree-iter-next-of-iter-fix))

(defruled iter-fix-of-tree-iter-prev-of-iter-fix
  (equal (iter-fix (tree-iter-prev (iter-fix iter)))
         (tree-iter-prev (iter-fix iter)))
  :enable (iterp iter-fix)
  :use mapp-of-tree-iter-plug-of-iter-fix)

(add-to-ruleset break-abstraction '(iter-fix-of-tree-iter-prev-of-iter-fix))

;; Locally these five stay enabled: the proofs in this book constantly cross
;; the boundary the rules police, and each is the identity the fixer needs.

(local (in-theory (enable tree-iter-p-of-iter-fix
                          mapp-of-tree-iter-plug-of-iter-fix
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
      iter-max) over an empty @(see treemap), where a backward walk is over
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
  :returns (map mapp
                :hints (("Goal"
                         :in-theory
                         (enable mapp-of-tree-iter-plug-of-iter-fix))))
  :parents (iterator)
  :short "The @(see treemap) an @(see iterator) walks."
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
  (equal (iter-fix (tree-iter-min (fix map)))
         (tree-iter-min (fix map)))
  :enable ( iterp break-abstraction))

(defruledl iter-fix-of-tree-iter-max-of-fix
  (equal (iter-fix (tree-iter-max (fix map)))
         (tree-iter-max (fix map)))
  :enable ( iterp break-abstraction))

(defrule from-iter-of-iter-min
  (equal (from-iter (iter-min map))
         (fix map))
  :enable (from-iter
           iter-min
           iter-fix-of-tree-iter-min-of-fix
           break-abstraction))

;; An @(tsee iter-min) iterator is past the end exactly when the set is empty:
;; with nothing to walk, a forward walk is over before it begins.

(defrule after-lastp-of-iter-min
  (equal (after-lastp (iter-min map))
         (emptyp map))
  :enable (after-lastp
           emptyp
           iter-min
           iter-fix-of-tree-iter-min-of-fix))

;; An @(tsee iter-min) iterator is never rewound: it is built by stepping
;; forward from the rewound position, and a step never lands there.

(defrule not-before-firstp-of-iter-min
  (not (before-firstp (iter-min map)))
  :enable (before-firstp
           iter-min
           iter-fix-of-tree-iter-min-of-fix))

;; So an @(tsee iter-min) iterator is at a value exactly when there is one to
;; be at.

(defrule has-valuep-of-iter-min
  (equal (has-valuep (iter-min map))
         (not (emptyp map)))
  :use ((:instance has-valuep-when-neither-end (iter (iter-min map)))
        (:instance not-after-lastp-when-has-valuep (iter (iter-min map))))
  :disable has-valuep-when-neither-end)

;;;;;;;;;;;;;;;;;;;;

;; The same four facts for @(tsee iter-max), with the two ends exchanged.

(defrule from-iter-of-iter-max
  (equal (from-iter (iter-max map))
         (fix map))
  :enable (from-iter
           iter-max
           iter-fix-of-tree-iter-max-of-fix
           break-abstraction))

(defrule before-firstp-of-iter-max
  (equal (before-firstp (iter-max map))
         (emptyp map))
  :enable (before-firstp
           emptyp
           iter-max
           iter-fix-of-tree-iter-max-of-fix))

(defrule not-after-lastp-of-iter-max
  (not (after-lastp (iter-max map)))
  :enable (after-lastp
           iter-max
           iter-fix-of-tree-iter-max-of-fix))

(defrule has-valuep-of-iter-max
  (equal (has-valuep (iter-max map))
         (not (emptyp map)))
  :use ((:instance has-valuep-when-neither-end (iter (iter-max map)))
        (:instance not-before-firstp-when-has-valuep (iter (iter-max map))))
  :disable has-valuep-when-neither-end)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The set on each side of an iterator. Both exclude the value it is at, so the
;; two are disjoint and, with that value, account for the whole set; at an end,
;; where there is no value, they account for it between them.
;;
;; The sequences these are built from are already ordered, so an oset is
;; exactly what they are; @(tsee from-omap) only changes the representation.

;; Over a search tree each side's built tree and its oset denote the same
;; elements, and treesets are canonical, so they are the same object. This is
;; what lets the builders serve as the executable branch below while the
;; logical definitions stay on the osets.

(defruledl tree-iter-tree-before-becomes-from-omap
  (implies (mapp (tree-iter-plug iter))
           (equal (tree-iter-tree-before iter)
                  (from-omap (tree-iter-omap-before iter))))
  ;; Unlike TREESET, where canonicity of sets settles this from membership,
  ;; the map version goes round the `to-omap'/`from-omap' trip: the side tree's
  ;; in-order alist is its omap over a search tree.
  :use (:instance from-omap-of-to-omap
                  (map (tree-iter-tree-before iter)))
  :enable (to-omap$inline
           mapp
           tree-in-order-of-tree-iter-tree-before
           tree-iter-omap-before-becomes-tree-iter-before))

(defruledl tree-iter-tree-after-becomes-from-omap
  (implies (mapp (tree-iter-plug iter))
           (equal (tree-iter-tree-after iter)
                  (from-omap (tree-iter-omap-after iter))))
  ;; Unlike TREESET, where canonicity of sets settles this from membership,
  ;; the map version goes round the `to-omap'/`from-omap' trip: the side tree's
  ;; in-order alist is its omap over a search tree.
  :use (:instance from-omap-of-to-omap
                  (map (tree-iter-tree-after iter)))
  :enable (to-omap$inline
           mapp
           tree-in-order-of-tree-iter-tree-after
           tree-iter-omap-after-becomes-tree-iter-after))

(define before ((iter iterp))
  :returns (map mapp)
  :parents (iterator)
  :short "The @(see treemap) of entries before an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The entries a forward walk has already passed. This excludes the entry
      the iterator is at: that one has not been passed yet.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) expected. The result is built with
      one fresh node per step of the iterator's path; every subtree hangs off
      the underlying map unchanged."))
  (mbe :logic (from-omap (tree-iter-omap-before (iter-fix iter)))
       :exec (tree-iter-tree-before (iter-fix iter)))
  :guard-hints
  (("Goal"
    :in-theory (enable* tree-iter-tree-before-becomes-from-omap
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
  :returns (map mapp)
  :parents (iterator)
  :short "The @(see treemap) of entries after an @(see iterator)."
  :long
  (xdoc::topstring
   (xdoc::p
     "The entries a forward walk has yet to reach. This excludes the entry the
      iterator is at, so it is what remains strictly after the current step.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) expected. The result is built with
      one fresh node per step of the iterator's path; every subtree hangs off
      the underlying map unchanged."))
  (mbe :logic (from-omap (tree-iter-omap-after (iter-fix iter)))
       :exec (tree-iter-tree-after (iter-fix iter)))
  :guard-hints
  (("Goal"
    :in-theory (enable* tree-iter-tree-after-becomes-from-omap
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
           tree-iter-omap-before
           tree-iter-tree-before
           (:e empty)
           (:e tree-omap)))

(defrule after-when-after-lastp
  (implies (after-lastp iter)
           (equal (after iter)
                  (empty)))
  :enable (after
           after-lastp
           tree-iter-omap-after
           tree-iter-tree-after
           (:e empty)
           (:e tree-omap)))

;; At the constructors the same holds with no hypothesis, including over the
;; empty @(see treemap), where the iterator lands on the far end and the side
;; in question is empty for the other reason.

(defrule before-of-iter-min
  (equal (before (iter-min map))
         (empty))
  :enable (before
           iter-min
           iter-fix-of-tree-iter-min-of-fix
           tree-iter-omap-before-when-not-consp-of-tree-iter-before
           (:e empty)
           (:e tree-omap)))

(defrule after-of-iter-max
  (equal (after (iter-max map))
         (empty))
  :enable (after
           iter-max
           iter-fix-of-tree-iter-max-of-fix
           tree-iter-omap-after-when-not-consp-of-tree-iter-after
           (:e empty)
           (:e tree-omap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The entry an iterator is at, split the way TREEMAP splits @(tsee head),
;; @(tsee min), and @(tsee max): the key and the value are the primitives, and
;; the paired form returns both.

(define entry-key ((iter iterp))
  :guard (has-valuep iter)
  :parents (iterator)
  :short "The key an @(see iterator) is at."
  (tree-iter-key (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable has-valuep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t entry-key)))

(defrule entry-key-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (entry-key iter0)
                  (entry-key iter1)))
  :rule-classes :congruence
  :enable entry-key)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry-val ((iter iterp))
  :guard (has-valuep iter)
  :parents (iterator)
  :short "The value an @(see iterator) is at."
  (tree-iter-val (iter-fix iter))
  :inline t
  :guard-hints (("Goal" :in-theory (enable has-valuep))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t entry-val)))

(defrule entry-val-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (entry-val iter0)
                  (entry-val iter1)))
  :rule-classes :congruence
  :enable entry-val)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define entry ((iter iterp))
  :guard (has-valuep iter)
  :parents (iterator)
  :short "The @(tsee entry-key) and @(tsee entry-val)."
  :returns (mv key val)
  (mv (entry-key iter) (entry-val iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t entry)))


;; What a walk yields first: the minimum. This is what ties the entries an
;; iterator produces to the map it walks; everything else here is structural.

(defrule entry-key-of-iter-min
  (implies (not (emptyp map))
           (equal (entry-key (iter-min map))
                  (min-key map)))
  :enable (entry-key min-key iter-min
           iter-fix-of-tree-iter-min-of-fix
           car-of-tree-leftmost-becomes-min
           keys
           break-abstraction))

(defrule entry-val-of-iter-min
  (implies (not (emptyp map))
           (equal (entry-val (iter-min map))
                  (min-val map)))
  :enable (entry-val min-val iter-min
           iter-fix-of-tree-iter-min-of-fix
           cdr-of-tree-leftmost
           keys
           lookup
           break-abstraction))

;; And symmetrically, what a backward walk yields first: the maximum.

(defrule entry-key-of-iter-max
  (implies (not (emptyp map))
           (equal (entry-key (iter-max map))
                  (max-key map)))
  :enable (entry-key max-key iter-max
           iter-fix-of-tree-iter-max-of-fix
           car-of-tree-rightmost-becomes-max
           keys
           break-abstraction))

(defrule entry-val-of-iter-max
  (implies (not (emptyp map))
           (equal (entry-val (iter-max map))
                  (max-val map)))
  :enable (entry-val max-val iter-max
           iter-fix-of-tree-iter-max-of-fix
           cdr-of-tree-rightmost
           keys
           lookup
           break-abstraction))

;; The entry-key an @(see iterator) is at is an element of the @(see treemap) it
;; walks. With @(tsee entry-key-of-iter-min) this is what connects a walk to the
;; contents of the set rather than just to its shape.
;;
;; Both internal functions are held folded here: the public definitions unfold
;; to exactly the internal terms the lemma below is stated about, and letting
;; those rewrite any further would lose the match.

(defrule in-of-keys-of-entry-key
  (implies (has-valuep iter)
           (treeset::in (entry-key iter) (keys (from-iter iter))))
  :enable (entry-key
           from-iter
           has-valuep
           keys))

;;;;;;;;;;;;;;;;;;;;

;; The tree an iterator is a position in is a search tree. This is what makes
;; the two sequences ordered, and so makes them osets. The rule cannot live in
;; an internal book because @(tsee iter-fix) is a public function; it is the
;; bst half of mapp-of-tree-iter-plug-of-iter-fix, projected out because the
;; internal ordering lemmas hypothesize @(tsee bstp) alone.

(defruledl bstp-of-tree-iter-plug-of-iter-fix
  (bstp (tree-iter-plug (iter-fix iter)))
  :use mapp-of-tree-iter-plug-of-iter-fix
  :enable bstp-when-mapp-forward-chaining)

;; Membership on each side, at each level of representation: the oset the side
;; is defined from, and the ordered element list that oset is read off of. The
;; walk's step laws are proved by extensionality over those element lists,
;; whose membership is @(tsee assoc-equal); the -assoc-equal rules carry a
;; key membership question all the way down to that level. Left disabled:
;; crossing from sets back to the underlying sequences is only what a proof
;; about the order of a walk wants.

(defruled in-of-keys-of-before-becomes-omap-assoc
  (equal (treeset::in x (keys (before iter)))
         (and (omap::assoc x (tree-iter-omap-before (iter-fix iter))) t))
  :enable (before
           treeset::in-of-from-oset
           omap::in-of-keys-to-assoc))

(add-to-ruleset break-abstraction '(in-of-keys-of-before-becomes-omap-assoc))

(defruled in-of-keys-of-after-becomes-omap-assoc
  (equal (treeset::in x (keys (after iter)))
         (and (omap::assoc x (tree-iter-omap-after (iter-fix iter))) t))
  :enable (after
           treeset::in-of-from-oset
           omap::in-of-keys-to-assoc))

(add-to-ruleset break-abstraction '(in-of-keys-of-after-becomes-omap-assoc))

(defruled in-of-keys-of-before-becomes-assoc-equal
  (equal (treeset::in x (keys (before iter)))
         (and (assoc-equal x (tree-iter-before (iter-fix iter))) t))
  :enable (in-of-keys-of-before-becomes-omap-assoc
           assoc-of-tree-iter-omap-before))

(add-to-ruleset break-abstraction '(in-of-keys-of-before-becomes-assoc-equal))

(defruled in-of-keys-of-after-becomes-assoc-equal
  (equal (treeset::in x (keys (after iter)))
         (and (assoc-equal x (tree-iter-after (iter-fix iter))) t))
  :enable (in-of-keys-of-after-becomes-omap-assoc
           assoc-of-tree-iter-omap-after))

(add-to-ruleset break-abstraction '(in-of-keys-of-after-becomes-assoc-equal))

;; The value counterparts. TREESET needs only the membership bridges above,
;; because set extensionality is settled by membership; map extensionality
;; compares the values too, so every step law below needs these as well.

(defruled lookup-of-before-becomes-assoc-equal
  (equal (lookup key (before iter) :default d)
         (if (assoc-equal key (tree-iter-before (iter-fix iter)))
             (cdr (assoc-equal key (tree-iter-before (iter-fix iter))))
           d))
  :enable (before
           lookup
           assoc-of-tree-iter-omap-before
           tree-iter-omap-before-becomes-tree-iter-before
           bstp-of-tree-iter-plug-of-iter-fix
           data::omap-assoc-becomes-assoc-equal))

(add-to-ruleset break-abstraction '(lookup-of-before-becomes-assoc-equal))

(defruled lookup-of-after-becomes-assoc-equal
  (equal (lookup key (after iter) :default d)
         (if (assoc-equal key (tree-iter-after (iter-fix iter)))
             (cdr (assoc-equal key (tree-iter-after (iter-fix iter))))
           d))
  :enable (after
           lookup
           assoc-of-tree-iter-omap-after
           tree-iter-omap-after-becomes-tree-iter-after
           bstp-of-tree-iter-plug-of-iter-fix
           data::omap-assoc-becomes-assoc-equal))

(add-to-ruleset break-abstraction '(lookup-of-after-becomes-assoc-equal))

;;;;;;;;;;;;;;;;;;;;

;; The iteration follows the set order: the entry-key an iterator is at lies above
;; everything behind it and below everything ahead of it. These are what tie a
;; traversal's order to @(tsee <<); the laws below are all consequences.
;;
;; These read straight off the filter characterizations: each side collects
;; the elements of the set on its own side of the entry-key. The rules which
;; rewrite @(tsee tree-iter-plug) to a zipper's plug are held off so that the
;; @(tsee bstp) hypothesis keeps its folded form.

(defrule <<-of-entry-key-when-in-of-keys-of-after
  (implies (and (has-valuep iter)
                (treeset::in x (keys (after iter))))
           (<< (entry-key iter) x))
  :enable (entry-key
           has-valuep
           in-of-keys-of-after-becomes-omap-assoc
           bstp-of-tree-iter-plug-of-iter-fix)
  :disable assoc-of-tree-iter-omap-after)

(defrule <<-of-arg1-and-entry-key-when-in-of-keys-of-before
  (implies (and (has-valuep iter)
                (treeset::in x (keys (before iter))))
           (<< x (entry-key iter)))
  :enable (entry-key
           has-valuep
           in-of-keys-of-before-becomes-omap-assoc
           bstp-of-tree-iter-plug-of-iter-fix)
  :disable assoc-of-tree-iter-omap-before)

;; So the entry-key is on neither side, and the sides are disjoint.

(defrule not-in-of-keys-of-entry-key-and-before
  (implies (has-valuep iter)
           (not (treeset::in (entry-key iter) (keys (before iter)))))
  :use (:instance <<-of-arg1-and-entry-key-when-in-of-keys-of-before (x (entry-key iter)))
  :disable <<-of-arg1-and-entry-key-when-in-of-keys-of-before
  :enable data::<<-rules)

(defrule not-in-of-keys-of-entry-key-and-after
  (implies (has-valuep iter)
           (not (treeset::in (entry-key iter) (keys (after iter)))))
  :use (:instance <<-of-entry-key-when-in-of-keys-of-after (x (entry-key iter)))
  :disable <<-of-entry-key-when-in-of-keys-of-after
  :enable data::<<-rules)

(defrule not-in-of-keys-of-after-when-in-of-keys-of-before
  (implies (and (has-valuep iter)
                (treeset::in x (keys (before iter))))
           (not (treeset::in x (keys (after iter)))))
  :use (<<-of-entry-key-when-in-of-keys-of-after
        <<-of-arg1-and-entry-key-when-in-of-keys-of-before)
  :disable (<<-of-entry-key-when-in-of-keys-of-after
            <<-of-arg1-and-entry-key-when-in-of-keys-of-before)
  :enable data::<<-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each side agrees with the whole map on the values of its own keys. This is
;; the value counterpart of @(tsee in-of-keys-of-from-iter-when-has-valuep):
;; that one says where a key of the map is, this one says a side binds it to
;; what the map binds it to. TREESET needs nothing like it, because a set
;; carries no values, but a walk over a map is only useful if what it reads is
;; what the map holds.
;;
;; The sides are slices of the plug's in-order alist, so the argument opens
;; that alist and picks out the slice the key falls in. Opening it is the
;; inverse of the two rules which close it, so a proof picks one direction.

(defruledl tree-in-order-of-tree-iter-plug-becomes-append
  (equal (tree-in-order (tree-iter-plug iter))
         (if (tree-iter-has-value-p iter)
             (append (tree-iter-before iter)
                     (cons (tree-iter-key+val iter)
                           (tree-iter-after iter)))
           (append (tree-iter-before iter)
                   (tree-iter-after iter))))
  :use (append-of-tree-iter-before-and-tree-iter-after-when-has-value
        append-of-tree-iter-before-and-tree-iter-after-when-no-value)
  :disable (append-of-tree-iter-before-and-tree-iter-after-when-has-value
            append-of-tree-iter-before-and-tree-iter-after-when-no-value))

(local
  (theory-invariant
    (incompatible! (:rewrite tree-in-order-of-tree-iter-plug-becomes-append)
                   (:rewrite append-of-tree-iter-before-and-tree-iter-after-when-has-value))))

(local
  (theory-invariant
    (incompatible! (:rewrite tree-in-order-of-tree-iter-plug-becomes-append)
                   (:rewrite append-of-tree-iter-before-and-tree-iter-after-when-no-value))))

(defrulel assoc-equal-of-tree-iter-before-becomes-tree-lookup
  (implies (and (iterp iter)
                (has-valuep iter)
                (assoc-equal key (tree-iter-before iter)))
           (equal (assoc-equal key (tree-iter-before iter))
                  (cons key (tree-lookup key (tree-iter-plug iter)))))
  :use ((:instance assoc-equal-of-tree-in-order-when-bstp
                   (tree (tree-iter-plug iter))))
  :enable (tree-in-order-of-tree-iter-plug-becomes-append
           acl2::assoc-equal-of-append
           mapp-of-tree-iter-plug-when-iterp-forward-chaining
           bstp-when-mapp-forward-chaining)
  :disable (assoc-equal-of-tree-in-order-when-bstp
            append-of-tree-iter-before-and-tree-iter-after-when-has-value
            append-of-tree-iter-before-and-tree-iter-after-when-no-value
            tree-iter-plug-when-tree-iter-has-value-p
            tree-iter-plug-when-zipp))

(defrulel assoc-equal-of-tree-iter-after-becomes-tree-lookup
  (implies (and (iterp iter)
                (has-valuep iter)
                (assoc-equal key (tree-iter-after iter)))
           (equal (assoc-equal key (tree-iter-after iter))
                  (cons key (tree-lookup key (tree-iter-plug iter)))))
  ;; The sides are disjoint, which rules out the key being found in the
  ;; earlier slice instead.
  :use ((:instance assoc-equal-of-tree-in-order-when-bstp
                   (tree (tree-iter-plug iter)))
        (:instance not-in-of-keys-of-after-when-in-of-keys-of-before
                   (x key))
        not-in-of-keys-of-entry-key-and-after)
  :enable (tree-in-order-of-tree-iter-plug-becomes-append
           acl2::assoc-equal-of-append
           in-of-keys-of-before-becomes-assoc-equal
           in-of-keys-of-after-becomes-assoc-equal
           mapp-of-tree-iter-plug-when-iterp-forward-chaining
           bstp-when-mapp-forward-chaining
           ;; With `iterp' the public and internal has-value tests coincide.
           has-valuep
           entry-key)
  :disable (assoc-equal-of-tree-in-order-when-bstp
            not-in-of-keys-of-after-when-in-of-keys-of-before
            not-in-of-keys-of-entry-key-and-after
            append-of-tree-iter-before-and-tree-iter-after-when-has-value
            append-of-tree-iter-before-and-tree-iter-after-when-no-value
            tree-iter-plug-when-tree-iter-has-value-p
            tree-iter-plug-when-zipp))

(defrule lookup-of-from-iter-when-in-of-keys-of-before
  (implies (and (has-valuep iter)
                (treeset::in key (keys (before iter))))
           (equal (lookup key (from-iter iter))
                  (lookup key (before iter))))
  :enable (from-iter
           lookup
           keys
           lookup-of-before-becomes-assoc-equal
           in-of-keys-of-before-becomes-assoc-equal
           bstp-of-tree-iter-plug-of-iter-fix)
  :use ((:instance assoc-equal-of-tree-iter-before-becomes-tree-lookup
                   (iter (iter-fix iter)))
        (:instance in-of-keys-of-before-becomes-assoc-equal
                   (x key)))
  :disable (assoc-equal-of-tree-iter-before-becomes-tree-lookup
            in-of-keys-of-before-becomes-assoc-equal))

(defrule lookup-of-from-iter-when-in-of-keys-of-after
  (implies (and (has-valuep iter)
                (treeset::in key (keys (after iter))))
           (equal (lookup key (from-iter iter))
                  (lookup key (after iter))))
  :enable (from-iter
           lookup
           keys
           lookup-of-after-becomes-assoc-equal
           in-of-keys-of-after-becomes-assoc-equal
           bstp-of-tree-iter-plug-of-iter-fix)
  :use ((:instance assoc-equal-of-tree-iter-after-becomes-tree-lookup
                   (iter (iter-fix iter)))
        (:instance in-of-keys-of-after-becomes-assoc-equal
                   (x key)))
  :disable (assoc-equal-of-tree-iter-after-becomes-tree-lookup
            in-of-keys-of-after-becomes-assoc-equal))

;; The same split at the public layer: the two sides and the entry-key account for
;; the set, and since the sides exclude the entry-key they do so without overlap.
;;
;; Both rules which rewrite @(tsee tree-iter-plug) to a zipper's plug are held
;; off, so that the term still matches the lemma above.

;; Membership in the whole set, in the same folded form. Like the -becomes-
;; rules above, this carries the public membership question down to the level
;; where the internal split lemma is stated; having it as its own rule is what
;; lets the split below leave @(tsee in) alone, so that the two rules above
;; are the only thing rewriting the sides.

(defruledl in-of-keys-of-from-iter-becomes-in-of-tree-key-set
  (equal (treeset::in x (keys (from-iter iter)))
         (treeset::in x (tree-key-set (tree-iter-plug (iter-fix iter)))))
  :enable (from-iter
           keys))

(defrule in-of-keys-of-from-iter-when-has-valuep
  (implies (has-valuep iter)
           (equal (treeset::in x (keys (from-iter iter)))
                  (or (treeset::in x (keys (before iter)))
                      (equal x (entry-key iter))
                      (treeset::in x (keys (after iter))))))
  :enable (in-of-keys-of-before-becomes-assoc-equal
           in-of-keys-of-after-becomes-assoc-equal
           in-of-keys-of-from-iter-becomes-in-of-tree-key-set
           entry-key
           has-valuep
           (:t treeset::in$inline))
  ;; The split is an `iff' rule, so it cannot rewrite under the `equal' here.
  :use (:instance in-of-tree-key-set-of-tree-iter-plug-split
                  (key x)
                  (iter (iter-fix iter))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next ((iter iterp))
  :guard (not (after-lastp iter))
  :returns (iter$ iterp
                  :hints (("Goal"
                           :in-theory
                           (enable iterp
                                   mapp-of-tree-iter-plug-of-iter-fix))))
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

;; A step forward moves the entry-key across the cut: what lies behind gains it.

(defrule before-of-next
  (implies (has-valuep iter)
           (equal (before (next iter))
                  (update (entry-key iter) (entry-val iter) (before iter))))
  :enable (extensionality
           in-of-keys-of-before-becomes-assoc-equal
           lookup-of-before-becomes-assoc-equal
           next
           entry-key
           entry-val
           has-valuep)
  ;; The cursor's key is not already behind it, which rules out the case where
  ;; the update would have to agree with an existing binding.
  :use not-in-of-keys-of-entry-key-and-before)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prev ((iter iterp))
  :guard (not (before-firstp iter))
  :returns (iter$ iterp
                  :hints (("Goal"
                           :in-theory
                           (enable iterp
                                   mapp-of-tree-iter-plug-of-iter-fix))))
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
                  (delete (entry-key (next iter)) (after iter))))
  :enable (extensionality
           in-of-keys-of-after-becomes-assoc-equal
           lookup-of-after-becomes-assoc-equal
           data::assoc-equal-of-cdr-when-omapp
           assoc-equal
           bstp-of-tree-iter-plug-of-iter-fix
           tree-iter-omap-after-becomes-tree-iter-after
           data::omap-assoc-becomes-assoc-equal
           next
           entry-key
           entry-val
           has-valuep))

;; The mirror, stated the way the sequence law is: a step back does not have a
;; @(tsee delete) form as cheap as the one above, because dropping the last
;; element of an ordered list is not a @(tsee cdr). Read right to left this
;; says the same thing -- what lies behind loses exactly the entry-key stepped
;; back onto.

(defrule before-becomes-insert-of-before-of-prev
  (implies (has-valuep (prev iter))
           (equal (before iter)
                  (update (entry-key (prev iter)) (entry-val (prev iter)) (before (prev iter)))))
  :enable (extensionality
           in-of-keys-of-before-becomes-assoc-equal
           lookup-of-before-becomes-assoc-equal
           assoc-equal
           prev
           entry-key
           entry-val
           has-valuep)
  ;; The key stepped back to is not already behind the previous position.
  :use (:instance not-in-of-keys-of-entry-key-and-before
                  (iter (prev iter))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A step forward has a entry-key to land on exactly when something lies ahead,
;; and the entry-key it lands on is the least of what lay ahead. So a forward walk
;; visits the elements in @(tsee <<) order, from the least on up.

(defrule has-valuep-of-next
  (equal (has-valuep (next iter))
         (not (emptyp (after iter))))
  :enable (not
           after
           has-valuep
           next))

;; What a step forward lands on: the least of what lay ahead. This is TREESET's
;; proof, read on keys: `equal-of-min-becomes-sk' reduces the claim to
;; membership plus minimality, and the ordered alist supplies minimality
;; through `<<-of-caar-when-assoc-equal-of-cdr'.

(defrule entry-key-of-next
  (implies (has-valuep (next iter))
           (equal (entry-key (next iter))
                  (min-key (after iter))))
  :enable (treeset::equal-of-min-becomes-sk
           treeset::not-<<-all-l-sk
           in-of-keys-of-after-becomes-assoc-equal
           bstp-of-tree-iter-plug-of-iter-fix
           entry-key
           next
           min-key
           has-valuep
           assoc-equal
           ;; The head of the side alist is a pair, hence non-nil.
           data::<<-rules)
  :use ((:instance alistp-of-tree-iter-after
                   (iter (iter-fix iter)))
        (:instance acl2::consp-of-car-when-alistp-alt
                   (x (tree-iter-after (iter-fix iter))))
        (:instance data::<<-of-caar-when-assoc-equal-of-cdr
                   (l (tree-iter-after (iter-fix iter)))
                   (x (treeset::not-<<-all-l-sk-witness
                        (keys (after iter))
                        (car (car (tree-iter-after (iter-fix iter)))))))
        (:instance treeset::in-when-emptyp
                   (treeset::x (car (car (tree-iter-after (iter-fix iter)))))
                   (treeset::set (keys (after iter))))))


;; The step law again, phrased on the position stepped from rather than the
;; position landed on: what lies ahead loses its least element. Unlike @(tsee
;; after-of-next) this covers the step off the last element, where what lay
;; ahead was already empty and stays so.

(defrule after-of-next-when-has-valuep
  (implies (has-valuep iter)
           (equal (after (next iter))
                  (delete (min-key (after iter)) (after iter))))
  :cases ((has-valuep (next iter)))
  :enable extensionality
  :use ((:instance has-valuep-when-neither-end (iter (next iter))))
  :disable has-valuep-when-neither-end)

;;;;;;;;;;;;;;;;;;;;

;; The mirror laws for a step back. What lies ahead gains the entry-key stepped
;; away from; a step back has a entry-key to land on exactly when something lies
;; behind; and the entry-key it lands on is the greatest of what lay behind. So a
;; backward walk visits the elements in reverse @(tsee <<) order.

(defrule after-of-prev
  (implies (has-valuep iter)
           (equal (after (prev iter))
                  (update (entry-key iter) (entry-val iter) (after iter))))
  :enable (extensionality
           in-of-keys-of-after-becomes-assoc-equal
           lookup-of-after-becomes-assoc-equal
           assoc-equal
           prev
           entry-key
           entry-val
           has-valuep)
  ;; The cursor's key is not already ahead of it.
  :use not-in-of-keys-of-entry-key-and-after)

(defrule has-valuep-of-prev
  (equal (has-valuep (prev iter))
         (not (emptyp (before iter))))
  :enable (not
           before
           has-valuep
           prev))

;; Left disabled: with @(tsee before-becomes-insert-of-before-of-prev) it
;; loops, since that rule introduces the very @(tsee entry-key) term this one
;; rewrites back into a @(tsee before) term.

(defruled entry-key-of-prev
  (implies (has-valuep (prev iter))
           (equal (entry-key (prev iter))
                  (max-key (before iter))))
  :enable (data::binary-max-<<
           data::<<-rules
           ;; The empty-side case is vacuous once `(emptyp (empty))' resolves.
           treeset::emptyp-of-empty)
  :use ((:instance <<-of-arg1-and-entry-key-when-in-of-keys-of-before
                   (iter (prev iter))
                   (x (max-key (before (prev iter))))))
  :disable <<-of-arg1-and-entry-key-when-in-of-keys-of-before)

(theory-invariant
  (incompatible! (:rewrite entry-key-of-prev)
                 (:rewrite before-becomes-insert-of-before-of-prev)))

(defrulel assoc-equal-of-tree-iter-before-becomes-in-of-keys-when-iterp
  (implies (iterp iter)
           (iff (assoc-equal x (tree-iter-before iter))
                (treeset::in x (keys (before iter)))))
  :enable in-of-keys-of-before-becomes-assoc-equal)

(defrule before-of-prev-when-has-valuep
  (implies (has-valuep iter)
           (equal (before (prev iter))
                  (delete (max-key (before iter)) (before iter))))
  :cases ((has-valuep (prev iter)))
  ;; The hint load is forced by the rewrite loop between entry-key-of-prev and
  ;; before-becomes-insert-of-before-of-prev: the proof needs both, so one
  ;; must arrive by :use. The other instances each carry one case: the
  ;; trichotomy puts a valueless prev at the rewound end, and the
  ;; disjointness instance discharges the delete of the absent maximum.
  :enable (extensionality
           lookup-of-before-becomes-assoc-equal
           treeset::in-when-emptyp
           assoc-equal
           entry-val
           treeset::emptyp-of-empty)
  :use ((:instance entry-key-of-prev)
        (:instance not-in-of-keys-of-entry-key-and-before (iter (prev iter)))
        (:instance has-valuep-when-neither-end (iter (prev iter)))
        (:instance has-valuep-of-prev))
  :disable (not-in-of-keys-of-entry-key-and-before
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
;; a search tree, so size and sequence length agree. Left disabled:
;; termination proofs run on the decrement laws above, which match the
;; measures folded.

(defruled nexts-becomes-size-of-after
  (implies (not (after-lastp iter))
           (equal (nexts iter)
                  (+ 1 (size (after iter)))))
  :enable (nexts
           after
           after-lastp
           tree-iter-nexts
           size$inline
           omap::cardinality-of-keys-to-size
           omapp-of-tree-iter-after-when-bstp
           tree-iter-omap-after-becomes-tree-iter-after
           bstp-of-tree-iter-plug-of-iter-fix)
  ;; Brought in as an instance so its left side unfolds alongside the goal's
  ;; `cardinality' of the key oset.
  :use (:instance data::size-becomes-len-when-omapp
                  (omap (tree-iter-after (iter-fix iter)))))


(defruled prevs-becomes-size-of-before
  (implies (not (before-firstp iter))
           (equal (prevs iter)
                  (+ 1 (size (before iter)))))
  :enable (prevs
           before
           before-firstp
           tree-iter-prevs
           size$inline
           omap::cardinality-of-keys-to-size
           omapp-of-tree-iter-before-when-bstp
           tree-iter-omap-before-becomes-tree-iter-before
           bstp-of-tree-iter-plug-of-iter-fix)
  ;; Brought in as an instance so its left side unfolds alongside the goal's
  ;; `cardinality' of the key oset.
  :use (:instance data::size-becomes-len-when-omapp
                  (omap (tree-iter-before (iter-fix iter)))))
