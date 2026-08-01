; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/data/utilities/oset-defs" :dir :system)

(include-book "tree-defs")
(include-book "zipper")
(include-book "in-defs")
(include-book "min-max-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/oset" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "tree"))
(local (include-book "in-order"))
(local (include-book "min-max"))
(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tree-iterator
  :parents (implementation)
  :short "A position in the in-order sequence of a @(see tree)."
  :long
  (xdoc::topstring
    (xdoc::p
      "An iterator is either a @(see zipper), which is at an element, or one of
       the two ends. A tree with @($n$) elements therefore has @($n+2$)
       iterators, running from before the first element to after the last.")
    (xdoc::p
      "The two ends are supplied here rather than found inside the tree. A
       zipper cannot serve as an end, because the empty subtrees which sit in
       the gaps of the in-order sequence number @($n+1$), so the empty tree
       has only one of them and could not tell its two ends apart. Carrying
       the tree alongside the tag keeps the ends distinct in every case, and
       keeps an iterator self-contained: it knows which tree it is a position
       in, whether or not it is at an element."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-p (x)
  (declare (xargs :type-prescription (booleanp (tree-iter-p x))))
  :short "Recognizer for @(see tree-iterator)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "The three cases cannot be confused: a zipper's focus is a nonempty tree,
      so the @(tsee car) of a zipper is a @(tsee consp), never a keyword."))
  (or (zipp x)
      (and (consp x)
           (or (eq (car x) :before-first)
               (eq (car x) :after-last))
           (treep (cdr x)))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-iter-p-when-zipp
  (implies (zipp zip)
           (tree-iter-p zip))
  :enable tree-iter-p)

(defrule tree-iter-p-compound-recognizer
  (implies (tree-iter-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable (tree-iter-p
           zipp))

;; A zipper is at an element, so its car is a tree node: a @(tsee consp), never
;; a tag. This is what keeps the three cases apart, and it does so by type
;; reasoning alone.

(defrule consp-of-car-when-zipp
  (implies (zipp zip)
           (consp (car zip)))
  :rule-classes (:rewrite :forward-chaining)
  :enable (zipp
           tree-empty-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-tree-iter ()
  :returns (iter tree-iter-p
                 :hints (("Goal" :in-theory (enable tree-iter-p))))
  :short "An irrelevant @(see tree-iterator), used as the fixer's default."
  :long
  (xdoc::topstring
   (xdoc::p
     "Unlike a zipper, an iterator of the empty tree exists, so the default can
      be an honest one: the position before the first element of the empty
      tree."))
  (cons :before-first nil))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-tree-iter) (:e irr-tree-iter)))

(defrule irr-tree-iter-type-prescription
  (tree-iter-p (irr-tree-iter))
  :rule-classes ((:type-prescription :typed-term (irr-tree-iter))))

;; The default is an end, not an element. Since its executable counterpart is
;; disabled, this has to be said rather than computed.

(defrule not-zipp-of-irr-tree-iter
  (not (zipp (irr-tree-iter)))
  :enable irr-tree-iter)

(defrule car-of-irr-tree-iter
  (equal (car (irr-tree-iter))
         :before-first)
  :enable irr-tree-iter)

(defrule cdr-of-irr-tree-iter
  (equal (cdr (irr-tree-iter))
         nil)
  :enable irr-tree-iter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-fix ((iter tree-iter-p))
  :returns (iter$ tree-iter-p)
  :short "Fixer for @(see tree-iterator)s."
  (mbe :logic (if (tree-iter-p iter) iter (irr-tree-iter))
       :exec (the cons iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-fix)))

(defrule tree-iter-fix-type-prescription
  (tree-iter-p (tree-iter-fix iter))
  :rule-classes ((:type-prescription :typed-term (tree-iter-fix iter))))

(defrule tree-iter-fix-when-tree-iter-p
  (implies (tree-iter-p iter)
           (equal (tree-iter-fix iter)
                  iter))
  :enable tree-iter-fix)

(defruled tree-iter-fix-when-not-tree-iter-p
  (implies (not (tree-iter-p iter))
           (equal (tree-iter-fix iter)
                  (irr-tree-iter)))
  :enable tree-iter-fix)

(defrule tree-iter-fix-when-not-tree-iter-p-cheap
  (implies (not (tree-iter-p iter))
           (equal (tree-iter-fix iter)
                  (irr-tree-iter)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-iter-fix-when-not-tree-iter-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-equiv
  ((x tree-iter-p)
   (y tree-iter-p))
  (declare (xargs :type-prescription (booleanp (tree-iter-equiv x y))))
  :short "Equivalence up to @(tsee tree-iter-fix)."
  (equal (tree-iter-fix x)
         (tree-iter-fix y))
  :inline t
  ///
  (defequiv tree-iter-equiv)

  (defrule tree-iter-fix-under-tree-iter-equiv
    (tree-iter-equiv (tree-iter-fix iter)
                     iter))

  (defrule tree-iter-fix-when-tree-iter-equiv-congruence
    (implies (tree-iter-equiv iter0 iter1)
             (equal (tree-iter-fix iter0)
                    (tree-iter-fix iter1)))
    :rule-classes :congruence))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The three constructors. The zipper case needs none: a zipper is already an
;; iterator.

(define tree-iter-before-first ((tree treep))
  :returns (iter tree-iter-p
                 :hints (("Goal" :in-theory (enable tree-iter-p))))
  :short "The iterator before the first element of a tree."
  (cons :before-first (tree-fix tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-after-last ((tree treep))
  :returns (iter tree-iter-p
                 :hints (("Goal" :in-theory (enable tree-iter-p))))
  :short "The iterator after the last element of a tree."
  (cons :after-last (tree-fix tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-before-first) (:t tree-iter-after-last)))

(defrule tree-iter-before-first-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-iter-before-first tree0)
                  (tree-iter-before-first tree1)))
  :rule-classes :congruence
  :enable tree-iter-before-first)

(defrule tree-iter-after-last-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-iter-after-last tree0)
                  (tree-iter-after-last tree1)))
  :rule-classes :congruence
  :enable tree-iter-after-last)

;; The two ends are distinct for every tree, including the empty one. This is
;; the whole reason they are added here rather than found in the tree.

(defrule tree-iter-before-first-not-equal-tree-iter-after-last
  (not (equal (tree-iter-before-first tree0)
              (tree-iter-after-last tree1)))
  :enable (tree-iter-before-first
           tree-iter-after-last))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each test goes through the fixer, so that all three respect @(tsee
;; tree-iter-equiv). This costs nothing to execute: @(tsee tree-iter-fix) is
;; itself an @(tsee mbe) whose executable form is the identity, so these read
;; the tag directly. Only @(tsee tree-iter-has-value-p) needs an @(tsee mbe) of
;; its own, to avoid running the full @(tsee zipp) check.

(define tree-iter-before-first-p ((iter tree-iter-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the iterator is before the first element."
  (eq (car (tree-iter-fix iter)) :before-first)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-after-last-p ((iter tree-iter-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the iterator is after the last element."
  (eq (car (tree-iter-fix iter)) :after-last)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-has-value-p ((iter tree-iter-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the iterator has a value to read."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically this is being a @(see zipper), which is the form the proofs
      want. Executing it that way would walk the path and recompute both
      counts, so the executable form instead just checks that neither tag is
      present, which is what having a value amounts to."))
  (mbe :logic (zipp (tree-iter-fix iter))
       :exec (and (not (eq (car iter) :before-first))
                  (not (eq (car iter) :after-last))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-iter-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-before-first-p)
                    (:t tree-iter-after-last-p)
                    (:t tree-iter-has-value-p)))

(defrule tree-iter-before-first-p-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-before-first-p iter0)
                  (tree-iter-before-first-p iter1)))
  :rule-classes :congruence
  :enable (tree-iter-before-first-p
           tree-iter-equiv))

(defrule tree-iter-after-last-p-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-after-last-p iter0)
                  (tree-iter-after-last-p iter1)))
  :rule-classes :congruence
  :enable (tree-iter-after-last-p
           tree-iter-equiv))

(defrule tree-iter-has-value-p-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-has-value-p iter0)
                  (tree-iter-has-value-p iter1)))
  :rule-classes :congruence
  :enable (tree-iter-has-value-p
           tree-iter-equiv))

;; The three cases are exclusive and exhaustive.

(defrule tree-iter-has-value-p-when-zipp
  (implies (zipp zip)
           (tree-iter-has-value-p zip))
  :enable tree-iter-has-value-p)

(defrule not-tree-iter-before-first-p-when-tree-iter-has-value-p
  (implies (tree-iter-has-value-p iter)
           (not (tree-iter-before-first-p iter)))
  :enable (tree-iter-has-value-p
           tree-iter-before-first-p
           tree-iter-fix
           zipp
           tree-empty-p
           irr-tree-iter))

(defrule not-tree-iter-after-last-p-when-tree-iter-has-value-p
  (implies (tree-iter-has-value-p iter)
           (not (tree-iter-after-last-p iter)))
  :enable (tree-iter-has-value-p
           tree-iter-after-last-p
           tree-iter-fix
           zipp
           tree-empty-p
           irr-tree-iter))

(defrule not-tree-iter-before-first-p-when-tree-iter-after-last-p
  (implies (tree-iter-after-last-p iter)
           (not (tree-iter-before-first-p iter)))
  :enable (tree-iter-after-last-p
           tree-iter-before-first-p))

;; A zipper carries no tag, so it is neither end.

(defrule not-tree-iter-before-first-p-when-zipp
  (implies (zipp zip)
           (not (tree-iter-before-first-p zip)))
  :enable (tree-iter-before-first-p
           tree-iter-fix))

(defrule not-tree-iter-after-last-p-when-zipp
  (implies (zipp zip)
           (not (tree-iter-after-last-p zip)))
  :enable (tree-iter-after-last-p
           tree-iter-fix))

;; A zipper is never equal to an end, whichever tree the end carries. This is
;; the form the move proofs need, where one side is a constructed end and the
;; other is a zipper a move landed on.

(defrule not-equal-of-zipp-and-tree-iter-before-first
  (implies (zipp zip)
           (not (equal zip (tree-iter-before-first tree))))
  :enable (tree-iter-before-first
           zipp
           treep))

(defrule not-equal-of-zipp-and-tree-iter-after-last
  (implies (zipp zip)
           (not (equal zip (tree-iter-after-last tree))))
  :enable (tree-iter-after-last
           zipp
           treep))

;; The same disjointness with no equality to match on, which is what a proof
;; needs when it has just built an end and is asking whether it is at a value.

(defrule not-zipp-of-tree-iter-before-first
  (not (zipp (tree-iter-before-first tree)))
  :enable (tree-iter-before-first
           zipp
           treep))

(defrule not-zipp-of-tree-iter-after-last
  (not (zipp (tree-iter-after-last tree)))
  :enable (tree-iter-after-last
           zipp
           treep))

;; And conversely, in the direction which lets a proof conclude that an iterator
;; landing on a zipper was not at an end to begin with.

(defrule not-tree-iter-has-value-p-when-tree-iter-before-first-p
  (implies (tree-iter-before-first-p iter)
           (not (tree-iter-has-value-p iter)))
  :enable (tree-iter-has-value-p
           tree-iter-before-first-p))

(defrule not-tree-iter-has-value-p-when-tree-iter-after-last-p
  (implies (tree-iter-after-last-p iter)
           (not (tree-iter-has-value-p iter)))
  :enable (tree-iter-has-value-p
           tree-iter-after-last-p))

;; No @(tsee tree-iter-p) hypothesis is needed: anything which is not an
;; iterator fixes to @(tsee irr-tree-iter), which is before the first
;; element, so failing both tests already implies being one.

(defrule tree-iter-has-value-p-when-neither-end
  (implies (and (not (tree-iter-before-first-p iter))
                (not (tree-iter-after-last-p iter)))
           (tree-iter-has-value-p iter))
  :enable (tree-iter-p
           tree-iter-has-value-p
           tree-iter-before-first-p
           tree-iter-after-last-p
           tree-iter-fix
           irr-tree-iter))

;; The same fact phrased on @(tsee zipp), which is what the guards of the
;; zipper operations actually ask for.

(defrule zipp-when-neither-end
  (implies (and (not (tree-iter-before-first-p iter))
                (not (tree-iter-after-last-p iter)))
           (zipp iter))
  :enable (tree-iter-p
           tree-iter-before-first-p
           tree-iter-after-last-p
           tree-iter-fix
           irr-tree-iter))

;; What the predicates say about the constructors.

(defrule tree-iter-before-first-p-of-tree-iter-before-first
  (tree-iter-before-first-p (tree-iter-before-first tree))
  :enable (tree-iter-before-first-p
           tree-iter-before-first
           tree-iter-fix
           tree-iter-p))

(defrule tree-iter-after-last-p-of-tree-iter-after-last
  (tree-iter-after-last-p (tree-iter-after-last tree))
  :enable (tree-iter-after-last-p
           tree-iter-after-last
           tree-iter-fix
           tree-iter-p))

(defrule not-tree-iter-after-last-p-of-tree-iter-before-first
  (not (tree-iter-after-last-p (tree-iter-before-first tree)))
  :enable (tree-iter-after-last-p
           tree-iter-before-first
           tree-iter-fix
           tree-iter-p))

(defrule not-tree-iter-before-first-p-of-tree-iter-after-last
  (not (tree-iter-before-first-p (tree-iter-after-last tree)))
  :enable (tree-iter-before-first-p
           tree-iter-after-last
           tree-iter-fix
           tree-iter-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter->zip ((iter tree-iter-p))
  :guard (tree-iter-has-value-p iter)
  :returns (zip zipp)
  :short "Get the zipper of an iterator which is at an element."
  (mbe :logic (if (zipp (tree-iter-fix iter))
                  (tree-iter-fix iter)
                (irr-zip))
       :exec iter)
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-iter-has-value-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter->zip)))

(defrule tree-iter->zip-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter->zip iter0)
                  (tree-iter->zip iter1)))
  :rule-classes :congruence
  :enable (tree-iter->zip
           tree-iter-equiv))

(defrule tree-iter->zip-when-zipp
  (implies (zipp zip)
           (equal (tree-iter->zip zip)
                  zip))
  :enable tree-iter->zip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; At either end, what the iterator carries is the tree.

(defrule treep-of-cdr-when-tree-iter-p-and-no-value
  (implies (and (tree-iter-p iter)
                (not (tree-iter-has-value-p iter)))
           (treep (cdr iter)))
  :enable (tree-iter-p
           tree-iter-has-value-p
           tree-iter-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-plug ((iter tree-iter-p))
  :returns (tree treep)
  :short "Recover the tree an iterator is a position in."
  :long
  (xdoc::topstring
   (xdoc::p
     "At an element this is the zipper's own @(tsee zip-plug); at either
      end it is the tree the iterator carries."))
  (if (tree-iter-has-value-p iter)
      (zip-plug (tree-iter->zip iter))
    (tree-fix (cdr (tree-iter-fix iter))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-plug)))

(defrule tree-iter-plug-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-plug iter0)
                  (tree-iter-plug iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-plug iter0)
           (tree-iter-plug iter1)))

(defrule tree-iter-plug-when-zipp
  (implies (zipp zip)
           (equal (tree-iter-plug zip)
                  (zip-plug zip)))
  :enable tree-iter-plug)

;; The two cases of the definition, as rules, so that proofs about the moves
;; never have to open it.

(defrule tree-iter-plug-when-tree-iter-has-value-p
  (implies (tree-iter-has-value-p iter)
           (equal (tree-iter-plug iter)
                  (zip-plug (tree-iter->zip iter))))
  :enable tree-iter-plug)

(defruledl tree-iter-plug-when-not-tree-iter-has-value-p
  (implies (not (tree-iter-has-value-p iter))
           (equal (tree-iter-plug iter)
                  (tree-fix (cdr (tree-iter-fix iter)))))
  :enable tree-iter-plug)

;; An end carries nothing but its tree, so it is recovered from that tree
;; alone. This is what makes the two ends unique, and so what the round trips
;; come down to once a move has landed on one.

(defruledl tree-iter-fix-when-tree-iter-before-first-p
  (implies (tree-iter-before-first-p iter)
           (equal (tree-iter-fix iter)
                  (tree-iter-before-first (tree-iter-plug iter))))
  :enable (tree-iter-before-first-p
           tree-iter-before-first
           tree-iter-has-value-p
           tree-iter-plug
           tree-iter-fix
           tree-iter-p))

(defruledl tree-iter-fix-when-tree-iter-after-last-p
  (implies (tree-iter-after-last-p iter)
           (equal (tree-iter-fix iter)
                  (tree-iter-after-last (tree-iter-plug iter))))
  :enable (tree-iter-after-last-p
           tree-iter-after-last
           tree-iter-has-value-p
           tree-iter-plug
           tree-iter-fix
           tree-iter-p))

;; The two rules just above rewrite a fixed iter into a plugged one, and the
;; rule above them rewrites a plugged iter back into a fixed one. Enabling
;; both directions at once loops. They are all disabled, but they are natural
;; companions and easy to reach for together, so say so rather than leaving a
;; trap.

(theory-invariant
  (incompatible (:rewrite tree-iter-fix-when-tree-iter-before-first-p)
                (:rewrite tree-iter-plug-when-not-tree-iter-has-value-p)))

(theory-invariant
  (incompatible (:rewrite tree-iter-fix-when-tree-iter-after-last-p)
                (:rewrite tree-iter-plug-when-not-tree-iter-has-value-p)))

(defrule tree-iter-plug-of-tree-iter-before-first
  (equal (tree-iter-plug (tree-iter-before-first tree))
         (tree-fix tree))
  :enable (tree-iter-plug
           tree-iter-has-value-p
           tree-iter-before-first
           tree-iter-fix
           zipp
           tree-empty-p
           tree-iter-p))

(defrule tree-iter-plug-of-tree-iter-after-last
  (equal (tree-iter-plug (tree-iter-after-last tree))
         (tree-fix tree))
  :enable (tree-iter-plug
           tree-iter-has-value-p
           tree-iter-after-last
           tree-iter-fix
           zipp
           tree-empty-p
           tree-iter-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-next ((iter tree-iter-p))
  :guard (not (tree-iter-after-last-p iter))
  :returns (iter$ tree-iter-p)
  :short "Move the iterator to the next position."
  :long
  (xdoc::topstring
   (xdoc::p
     "After the last element the move saturates. From before the first it
      steps to the first element, or straight to the other end when the tree
      is empty, since then there is no element to stop at. At an element it
      hands the step to @(tsee zip-next), except at the last element, where it
      leaves the elements behind.")
   (xdoc::p
     "Time complexity: @($O(d)$) in the worst case -- @($O(\\log(n))$) over a
      @(see treeset) -- but @($O(1)$) amortized over a traversal."))
  ;; Logically the move saturates at the far end, which is what @(tsee
  ;; next-identity-iff-after-lastp) reports. The guard rules that case out for
  ;; execution only, so the executable form need not test for it: one keyword
  ;; comparison saved on every step of a traversal.
  (mbe :logic (cond ((tree-iter-after-last-p iter)
                     (tree-iter-fix iter))
                    ((tree-iter-before-first-p iter)
                     (let ((tree (tree-iter-plug iter)))
                       (if (tree-empty-p tree)
                           (tree-iter-after-last tree)
                         (zip-first tree))))
                    (t
                     (let ((zip (tree-iter->zip iter)))
                       (if (zip-at-last-p zip)
                           (tree-iter-after-last (zip-plug zip))
                         (zip-next zip)))))
       :exec (if (tree-iter-before-first-p iter)
                 (let ((tree (tree-iter-plug iter)))
                   (if (tree-empty-p tree)
                       (tree-iter-after-last tree)
                     (zip-first tree)))
               (let ((zip (tree-iter->zip iter)))
                 (if (zip-at-last-p zip)
                     (tree-iter-after-last (zip-plug zip))
                   (zip-next zip)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-iter-has-value-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-prev ((iter tree-iter-p))
  :guard (not (tree-iter-before-first-p iter))
  :returns (iter$ tree-iter-p)
  :short "Move the iterator to the previous position."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee tree-iter-next)."))
  ;; The mirror of @(tsee tree-iter-next), guard and all.
  (mbe :logic (cond ((tree-iter-before-first-p iter)
                     (tree-iter-fix iter))
                    ((tree-iter-after-last-p iter)
                     (let ((tree (tree-iter-plug iter)))
                       (if (tree-empty-p tree)
                           (tree-iter-before-first tree)
                         (zip-last tree))))
                    (t
                     (let ((zip (tree-iter->zip iter)))
                       (if (zip-at-first-p zip)
                           (tree-iter-before-first (zip-plug zip))
                         (zip-prev zip)))))
       :exec (if (tree-iter-after-last-p iter)
                 (let ((tree (tree-iter-plug iter)))
                   (if (tree-empty-p tree)
                       (tree-iter-before-first tree)
                     (zip-last tree)))
               (let ((zip (tree-iter->zip iter)))
                 (if (zip-at-first-p zip)
                     (tree-iter-before-first (zip-plug zip))
                   (zip-prev zip)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-iter-has-value-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-next) (:t tree-iter-prev)))

(defrule tree-iter-next-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-next iter0)
                  (tree-iter-next iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-next iter0)
           (tree-iter-next iter1)))

(defrule tree-iter-prev-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-prev iter0)
                  (tree-iter-prev iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-prev iter0)
           (tree-iter-prev iter1)))

;; Emptiness of a plugged tree, in the two forms the move proofs need. Stated
;; here rather than enabling @(tsee tree-empty-p) in those proofs, which would
;; rewrite it out of the very rules that mention it.

(defrulel tree-iter-plug-when-tree-empty-p-of-tree-iter-plug
  (implies (tree-empty-p (tree-iter-plug iter))
           (equal (tree-iter-plug iter)
                  nil))
  :use (:instance tree-empty-p-when-treep (tree (tree-iter-plug iter))))

(defrulel not-tree-empty-p-of-tree-iter-plug-when-consp
  (implies (consp (tree-iter-plug iter))
           (not (tree-empty-p (tree-iter-plug iter))))
  :use (:instance tree-empty-p-when-treep (tree (tree-iter-plug iter))))

;; Moving never changes the tree the iterator is a position in.

(defrule tree-iter-plug-of-tree-iter-next
  (equal (tree-iter-plug (tree-iter-next iter))
         (tree-iter-plug iter))
  :enable (tree-iter-next
           tree-iter-has-value-p))

(defrule tree-iter-plug-of-tree-iter-prev
  (equal (tree-iter-plug (tree-iter-prev iter))
         (tree-iter-plug iter))
  :enable (tree-iter-prev
           tree-iter-has-value-p))

;; The ends saturate.

(defrule tree-iter-next-when-tree-iter-after-last-p
  (implies (tree-iter-after-last-p iter)
           (equal (tree-iter-next iter)
                  (tree-iter-fix iter)))
  :enable tree-iter-next)

(defrule tree-iter-prev-when-tree-iter-before-first-p
  (implies (tree-iter-before-first-p iter)
           (equal (tree-iter-prev iter)
                  (tree-iter-fix iter)))
  :enable tree-iter-prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two moves are inverse everywhere they have somewhere to go. Unlike the
;; zipper laws these need no side conditions at all beyond the end being
;; stepped away from: every position a traversal can occupy is an iterator,
;; so there is nothing left to exclude.

(defrule tree-iter-prev-of-tree-iter-next
  (implies (not (tree-iter-after-last-p iter))
           (equal (tree-iter-prev (tree-iter-next iter))
                  (tree-iter-fix iter)))
  :enable (tree-iter-next
           tree-iter-prev
           tree-iter-has-value-p
           tree-iter-fix-when-tree-iter-before-first-p
           tree-iter-fix-when-tree-iter-after-last-p))

(defrule tree-iter-next-of-tree-iter-prev
  (implies (not (tree-iter-before-first-p iter))
           (equal (tree-iter-next (tree-iter-prev iter))
                  (tree-iter-fix iter)))
  :enable (tree-iter-next
           tree-iter-prev
           tree-iter-has-value-p
           tree-iter-fix-when-tree-iter-before-first-p
           tree-iter-fix-when-tree-iter-after-last-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A move is the identity exactly at the end it saturates against. Reaching a
;; fixed point means being done, not being stuck, which is what lets a
;; traversal test for completion by comparing against the previous iterator.
;;
;; The three cases are separate: at an element the zipper law applies; from an
;; end, a step either lands on an element or crosses to the other end, and both
;; differ from where it started, the latter because the two ends carry
;; different tags.

(defrule tree-iter-next-identity-iff-tree-iter-after-last-p
  (equal (equal (tree-iter-next iter) (tree-iter-fix iter))
         (tree-iter-after-last-p iter))
  :use (:instance zip-next-identity-iff-zip-at-last-p (zip iter))
  :disable zip-next-identity-iff-zip-at-last-p
  :enable (tree-iter-next
           tree-iter->zip
           tree-iter-has-value-p
           tree-iter-fix-when-tree-iter-before-first-p
           tree-iter-fix-when-tree-iter-after-last-p))

(defrule tree-iter-prev-identity-iff-tree-iter-before-first-p
  (equal (equal (tree-iter-prev iter) (tree-iter-fix iter))
         (tree-iter-before-first-p iter))
  :use (:instance zip-prev-identity-iff-zip-at-first-p (zip iter))
  :disable zip-prev-identity-iff-zip-at-first-p
  :enable (tree-iter-prev
           tree-iter->zip
           tree-iter-has-value-p
           tree-iter-fix-when-tree-iter-before-first-p
           tree-iter-fix-when-tree-iter-after-last-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-value ((iter tree-iter-p))
  :guard (tree-iter-has-value-p iter)
  :short "The value at the iterator."
  (zip-value (tree-iter->zip iter))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-value)))

(defrule tree-iter-value-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-value iter0)
                  (tree-iter-value iter1)))
  :rule-classes :congruence
  :enable tree-iter-value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What lies to either side of the iterator. Both exclude the element in focus,
;; matching @(tsee zip-before) and @(tsee zip-after), so that the two
;; sides are symmetric and the element sits between them.

(define tree-iter-before ((iter tree-iter-p))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values to the left of the iterator, in order."
  (cond ((tree-iter-before-first-p iter) nil)
        ((tree-iter-after-last-p iter) (tree-in-order (tree-iter-plug iter)))
        (t (zip-before (tree-iter->zip iter))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-after ((iter tree-iter-p))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values to the right of the iterator, in order."
  (cond ((tree-iter-after-last-p iter) nil)
        ((tree-iter-before-first-p iter) (tree-in-order (tree-iter-plug iter)))
        (t (zip-after (tree-iter->zip iter))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-before) (:t tree-iter-after)))

(defrule tree-iter-before-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-before iter0)
                  (tree-iter-before iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-before iter0)
           (tree-iter-before iter1)))

(defrule tree-iter-after-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-after iter0)
                  (tree-iter-after iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-after iter0)
           (tree-iter-after iter1)))

;; The two sides, with the element between them where there is one, are the
;; whole sequence.

(defrule append-of-tree-iter-before-and-tree-iter-after-when-has-value
  (implies (tree-iter-has-value-p iter)
           (equal (append (tree-iter-before iter)
                          (cons (tree-iter-value iter)
                                (tree-iter-after iter)))
                  (tree-in-order (tree-iter-plug iter))))
  :enable (tree-iter-before
           tree-iter-after
           tree-iter-value
           tree-in-order-of-zip-plug-split-at-cursor))

;; The whole sequence is the two sides with the value between them, so an
;; element of the tree is on one side, on the other, or is the value itself.
;; Stated over @(tsee tree-iter-plug), where every function is still folded.

(defruled tree-in-of-tree-iter-plug-split
  (implies (tree-iter-has-value-p iter)
           (equal (tree-in x (tree-iter-plug iter))
                  (or (and (member-equal x (tree-iter-before iter)) t)
                      (equal x (tree-iter-value iter))
                      (and (member-equal x (tree-iter-after iter)) t))))
  :use ((:instance member-equal-of-tree-in-order-under-iff
                   (tree (tree-iter-plug iter)))
        (:instance append-of-tree-iter-before-and-tree-iter-after-when-has-value))
  :disable (member-equal-of-tree-in-order-under-iff
            append-of-tree-iter-before-and-tree-iter-after-when-has-value
            tree-in-order-of-zip-plug))

(defrule append-of-tree-iter-before-and-tree-iter-after-when-no-value
  (implies (not (tree-iter-has-value-p iter))
           (equal (append (tree-iter-before iter)
                          (tree-iter-after iter))
                  (tree-in-order (tree-iter-plug iter))))
  :enable (tree-iter-before
           tree-iter-after))

;; At either end the whole sequence lies on one side: a rewound iterator has
;; all of it ahead, and an exhausted one has all of it behind.

(defrule tree-iter-after-of-tree-iter-before-first
  (equal (tree-iter-after (tree-iter-before-first tree))
         (tree-in-order tree))
  :enable tree-iter-after)

(defrule tree-iter-before-of-tree-iter-after-last
  (equal (tree-iter-before (tree-iter-after-last tree))
         (tree-in-order tree))
  :enable tree-iter-before)

;; At the first element nothing lies behind, so the whole sequence is that
;; element followed by what lies ahead of it.

(defruledl tree-in-order-becomes-value-and-after-of-zip-first
  (implies (not (tree-empty-p tree))
           (equal (tree-in-order tree)
                  (cons (zip-value (zip-first tree))
                        (zip-after (zip-first tree)))))
  :use (:instance tree-in-order-of-zip-plug-split-at-cursor
                  (zip (zip-first tree))))

;; Symmetrically, at the last element nothing lies ahead.

(defruledl tree-in-order-becomes-before-and-value-of-zip-last
  (implies (not (tree-empty-p tree))
           (equal (tree-in-order tree)
                  (append (zip-before (zip-last tree))
                          (list (zip-value (zip-last tree))))))
  :use (:instance tree-in-order-of-zip-plug-split-at-cursor
                  (zip (zip-last tree))))

;; The same two facts as counts, which is the form the measures need: the
;; length rule has already turned any in-order length into a node count.

(defruledl tree-nodes-count-becomes-1-plus-len-of-after-of-zip-first
  (implies (not (tree-empty-p tree))
           (equal (tree-nodes-count tree)
                  (+ 1 (len (zip-after (zip-first tree))))))
  :use ((:instance tree-in-order-becomes-value-and-after-of-zip-first)
        (:instance len-of-tree-in-order))
  :disable len-of-tree-in-order)

(defruledl tree-nodes-count-becomes-1-plus-len-of-before-of-zip-last
  (implies (not (tree-empty-p tree))
           (equal (tree-nodes-count tree)
                  (+ 1 (len (zip-before (zip-last tree))))))
  :use ((:instance tree-in-order-becomes-before-and-value-of-zip-last)
        (:instance len-of-tree-in-order))
  :disable len-of-tree-in-order)

;; A step drops the value it moves onto from what lies ahead. Because @(tsee
;; cdr) of @('nil') is @('nil'), this needs no hypotheses: it holds at both
;; saturating ends as well as everywhere between.

(defrule tree-iter-after-of-tree-iter-next
  (equal (tree-iter-after (tree-iter-next iter))
         (cdr (tree-iter-after iter)))
  :enable (tree-iter-after
           tree-iter-next
           tree-iter-has-value-p
           tree-in-order-becomes-value-and-after-of-zip-first))

;; What lies behind gains the value stepped away from, at its back. Unlike the
;; rule above this needs the iterator to be at a value: from the rewound
;; position a step lands on the first element having passed nothing.

(defrule tree-iter-before-of-tree-iter-next
  (implies (tree-iter-has-value-p iter)
           (equal (tree-iter-before (tree-iter-next iter))
                  (append (tree-iter-before iter)
                          (list (tree-iter-value iter)))))
  :enable (tree-iter-before
           tree-iter-next
           tree-iter-value
           tree-iter-has-value-p
           tree-in-order-of-zip-plug-split-at-cursor))

;; The mirror, which cannot be stated the same way: a step back drops the LAST
;; value from what lies behind, and there is no @(tsee cdr) for that. So it is
;; stated in the reconstructive direction instead, and needs the step to land
;; on a value -- unlike the rule above, which holds at both ends because
;; @(tsee cdr) of @('nil') is @('nil').

(defrule tree-iter-before-of-tree-iter-prev
  (implies (tree-iter-has-value-p (tree-iter-prev iter))
           (equal (tree-iter-before iter)
                  (append (tree-iter-before (tree-iter-prev iter))
                          (list (tree-iter-value (tree-iter-prev iter))))))
  :enable (tree-iter-before
           tree-iter-prev
           tree-iter-value
           tree-iter-has-value-p
           tree-in-order-becomes-before-and-value-of-zip-last
           zip-before-of-zip-prev))

;; And what lies ahead of a step back gains the value stepped away from, at
;; its front.

(defrule tree-iter-after-of-tree-iter-prev
  (implies (tree-iter-has-value-p iter)
           (equal (tree-iter-after (tree-iter-prev iter))
                  (cons (tree-iter-value iter)
                        (tree-iter-after iter))))
  :enable (tree-iter-after
           tree-iter-prev
           tree-iter-value
           tree-iter-has-value-p
           zip-after-of-zip-prev
           tree-in-order-of-zip-plug-split-at-cursor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; How many moves remain in each direction: how many times @(tsee
;; tree-iter-next) can be called before it saturates, and likewise for @(tsee
;; tree-iter-prev). These are the measures for traversals.
;;
;; They cannot simply count elements. A tree with @($n$) elements has @($n+2$)
;; positions but only @($n+1$) possible element counts, so some step would
;; always be free. Counting positions instead costs one extra unit at whichever
;; end is not being approached, and the two then sum to @($n+1$) everywhere.

(define tree-iter-nexts ((iter tree-iter-p))
  :returns (count natp :rule-classes :type-prescription)
  :short "The number of @(tsee tree-iter-next) moves before saturating."
  (if (tree-iter-after-last-p iter)
      0
    (+ 1 (len (tree-iter-after iter))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-prevs ((iter tree-iter-p))
  :returns (count natp :rule-classes :type-prescription)
  :short "The number of @(tsee tree-iter-prev) moves before saturating."
  (if (tree-iter-before-first-p iter)
      0
    (+ 1 (len (tree-iter-before iter))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-nexts) (:t tree-iter-prevs)))

(defrule tree-iter-nexts-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-nexts iter0)
                  (tree-iter-nexts iter1)))
  :rule-classes :congruence
  :enable tree-iter-nexts)

(defrule tree-iter-prevs-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-prevs iter0)
                  (tree-iter-prevs iter1)))
  :rule-classes :congruence
  :enable tree-iter-prevs)

;; Each count is zero exactly at the end it measures the distance to.

(defrule tree-iter-nexts-equal-0
  (equal (equal (tree-iter-nexts iter) 0)
         (tree-iter-after-last-p iter))
  :enable tree-iter-nexts)

(defrule tree-iter-prevs-equal-0
  (equal (equal (tree-iter-prevs iter) 0)
         (tree-iter-before-first-p iter))
  :enable tree-iter-prevs)

;; And each strictly decreases on the move it counts. This is what admits a
;; traversal in either direction.

(defrule tree-iter-nexts-of-tree-iter-next
  (implies (not (tree-iter-after-last-p iter))
           (equal (tree-iter-nexts (tree-iter-next iter))
                  (- (tree-iter-nexts iter) 1)))
  :enable (tree-iter-nexts
           tree-iter-next
           tree-iter-has-value-p
           tree-iter-after
           tree-nodes-count-becomes-1-plus-len-of-after-of-zip-first))

(defrule tree-iter-prevs-of-tree-iter-prev
  (implies (not (tree-iter-before-first-p iter))
           (equal (tree-iter-prevs (tree-iter-prev iter))
                  (- (tree-iter-prevs iter) 1)))
  :enable (tree-iter-prevs
           tree-iter-prev
           tree-iter-has-value-p
           tree-iter-before
           tree-nodes-count-becomes-1-plus-len-of-before-of-zip-last
           zip-before-of-zip-prev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Both sides are ordered, whenever the tree is. An oset is just an ordered
;; list, and each side is a contiguous slice of the tree's in-order sequence,
;; which is an oset by @(tsee osetp-of-tree-in-order-when-bstp). So the sets to
;; either side of the iterator are available without building anything.

(defrule osetp-of-tree-iter-before-when-bstp
  (implies (bstp (tree-iter-plug iter))
           (set::setp (tree-iter-before iter)))
  :cases ((tree-iter-has-value-p iter))
  :enable (tree-iter-before
           tree-in-order-of-zip-plug-split-at-cursor
           data::setp-of-prefix-when-osetp-of-append
           data::setp-of-suffix-when-osetp-of-append)
  :disable tree-in-order-of-zip-plug
  :use ((:instance osetp-of-tree-in-order-when-bstp
                   (tree (tree-iter-plug iter)))))

(defrule osetp-of-tree-iter-after-when-bstp
  (implies (bstp (tree-iter-plug iter))
           (set::setp (tree-iter-after iter)))
  :cases ((tree-iter-has-value-p iter))
  :enable (tree-iter-after
           tree-in-order-of-zip-plug-split-at-cursor)
  :disable tree-in-order-of-zip-plug
  :use ((:instance osetp-of-tree-in-order-when-bstp
                   (tree (tree-iter-plug iter)))
        (:instance data::setp-of-suffix-when-osetp-of-append
                   (data::x (zip-before iter))
                   (data::y (cons (zip-value iter) (zip-after iter))))
        (:instance data::setp-of-cdr-when-osetp
                   (data::l (cons (zip-value iter) (zip-after iter))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two sides as osets, lifted through the three shapes: nothing lies
;; behind the left end or ahead of the right one, and at either end the whole
;; tree lies on the other side. Structurally @(tsee set::setp), like the
;; zipper versions they wrap.

(define tree-iter-oset-before ((iter tree-iter-p))
  :returns (oset set::setp)
  :short "The elements to the left of the iterator, as an oset."
  (cond ((tree-iter-before-first-p iter) nil)
        ((tree-iter-after-last-p iter) (tree-oset (tree-iter-plug iter)))
        (t (zip-oset-before (tree-iter->zip iter)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-oset-after ((iter tree-iter-p))
  :returns (oset set::setp)
  :short "The elements to the right of the iterator, as an oset."
  (cond ((tree-iter-after-last-p iter) nil)
        ((tree-iter-before-first-p iter) (tree-oset (tree-iter-plug iter)))
        (t (zip-oset-after (tree-iter->zip iter)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-oset-before) (:t tree-iter-oset-after)))

(defrule tree-iter-oset-before-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-oset-before iter0)
                  (tree-iter-oset-before iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-oset-before iter0)
           (tree-iter-oset-before iter1)))

(defrule tree-iter-oset-after-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-oset-after iter0)
                  (tree-iter-oset-after iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-oset-after iter0)
           (tree-iter-oset-after iter1)))

;; Membership in each oset is membership in the corresponding sequence, with
;; no hypothesis.

(defrule in-of-tree-iter-oset-before
  (iff (set::in x (tree-iter-oset-before iter))
       (member-equal x (tree-iter-before iter)))
  :enable (tree-iter-oset-before
           tree-iter-before))

(defrule in-of-tree-iter-oset-after
  (iff (set::in x (tree-iter-oset-after iter))
       (member-equal x (tree-iter-after iter)))
  :enable (tree-iter-oset-after
           tree-iter-after))

;; Each oset is empty exactly when its sequence is.

(defrule emptyp-of-tree-iter-oset-before
  (equal (set::emptyp (tree-iter-oset-before iter))
         (not (consp (tree-iter-before iter))))
  :use ((:instance in-of-tree-iter-oset-before
                   (x (set::head (tree-iter-oset-before iter))))
        (:instance in-of-tree-iter-oset-before
                   (x (car (tree-iter-before iter))))
        (:instance set::in-head
                   (set::x (tree-iter-oset-before iter))))
  :disable (in-of-tree-iter-oset-before
            set::in-head))

(defrule emptyp-of-tree-iter-oset-after
  (equal (set::emptyp (tree-iter-oset-after iter))
         (not (consp (tree-iter-after iter))))
  :use ((:instance in-of-tree-iter-oset-after
                   (x (set::head (tree-iter-oset-after iter))))
        (:instance in-of-tree-iter-oset-after
                   (x (car (tree-iter-after iter))))
        (:instance set::in-head
                   (set::x (tree-iter-oset-after iter))))
  :disable (in-of-tree-iter-oset-after
            set::in-head))

;; An empty sequence means an empty oset on the same side, since the oset is
;; the sequence's members.

(defruled tree-iter-oset-before-when-not-consp-of-tree-iter-before
  (implies (not (consp (tree-iter-before iter)))
           (equal (tree-iter-oset-before iter)
                  nil))
  :use emptyp-of-tree-iter-oset-before
  :enable set::emptyp
  :disable emptyp-of-tree-iter-oset-before)

(defruled tree-iter-oset-after-when-not-consp-of-tree-iter-after
  (implies (not (consp (tree-iter-after iter)))
           (equal (tree-iter-oset-after iter)
                  nil))
  :use emptyp-of-tree-iter-oset-after
  :enable set::emptyp
  :disable emptyp-of-tree-iter-oset-after)

;; Over a search tree the oset and sequence versions are the same object.

(defruled tree-iter-oset-before-becomes-tree-iter-before
  (implies (bstp (tree-iter-plug iter))
           (equal (tree-iter-oset-before iter)
                  (tree-iter-before iter)))
  :enable (tree-iter-oset-before
           tree-iter-before
           tree-oset-becomes-tree-in-order
           zip-oset-before-becomes-zip-before))

(defruled tree-iter-oset-after-becomes-tree-iter-after
  (implies (bstp (tree-iter-plug iter))
           (equal (tree-iter-oset-after iter)
                  (tree-iter-after iter)))
  :enable (tree-iter-oset-after
           tree-iter-after
           tree-oset-becomes-tree-in-order
           zip-oset-after-becomes-zip-after))

;; The order filters, lifted: at an element, each side holds exactly the
;; elements of the tree on that side of the value in the @(tsee <<) order.

(defrule in-of-tree-iter-oset-before-when-bstp
  (implies (and (bstp (tree-iter-plug iter))
                (tree-iter-has-value-p iter))
           (equal (set::in x (tree-iter-oset-before iter))
                  (and (tree-in x (tree-iter-plug iter))
                       (<< x (tree-iter-value iter)))))
  :enable (tree-iter-oset-before
           tree-iter-value)
  :disable in-of-tree-iter-oset-before)

(defrule in-of-tree-iter-oset-after-when-bstp
  (implies (and (bstp (tree-iter-plug iter))
                (tree-iter-has-value-p iter))
           (equal (set::in x (tree-iter-oset-after iter))
                  (and (tree-in x (tree-iter-plug iter))
                       (<< (tree-iter-value iter) x))))
  :enable (tree-iter-oset-after
           tree-iter-value)
  :disable in-of-tree-iter-oset-after)

;; A step forward can never land before the first element, whichever
;; position it began at. This is what lets a forward walk know it may read
;; the element it is on.

(defrule not-tree-iter-before-first-p-of-tree-iter-next
  (not (tree-iter-before-first-p (tree-iter-next iter)))
  :enable (tree-iter-next
           tree-iter-has-value-p))

(defrule not-tree-iter-after-last-p-of-tree-iter-prev
  (not (tree-iter-after-last-p (tree-iter-prev iter)))
  :enable (tree-iter-prev
           tree-iter-has-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What a walk yields first. The whole sequence begins with the value at the
;; first element, and the head of a tree's in-order sequence is its leftmost
;; node, so the two agree.

(defrule zip-value-of-zip-first
  (implies (not (tree-empty-p tree))
           (equal (zip-value (zip-first tree))
                  (tree-leftmost tree)))
  :use ((:instance tree-in-order-becomes-value-and-after-of-zip-first)
        (:instance car-of-tree-in-order))
  :disable car-of-tree-in-order)

(defruledl car-of-last-of-append-of-singleton
  (equal (car (last (append x (list y))))
         y)
  :induct t
  :enable append)

(defrule zip-value-of-zip-last
  (implies (not (tree-empty-p tree))
           (equal (zip-value (zip-last tree))
                  (tree-rightmost tree)))
  :enable car-of-last-of-append-of-singleton
  :use ((:instance tree-in-order-becomes-before-and-value-of-zip-last)
        (:instance car-of-last-of-tree-in-order))
  :disable car-of-last-of-tree-in-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The iterators at the two extremes: step inward from an end. Each starts a
;; walk in its own direction, landing on a value exactly when there is one.

(define tree-iter-min ((tree treep))
  :returns (iter tree-iter-p)
  :short "The tree iterator at the least element."
  (tree-iter-next (tree-iter-before-first tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-max ((tree treep))
  :returns (iter tree-iter-p)
  :short "The tree iterator at the greatest element."
  (tree-iter-prev (tree-iter-after-last tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-min) (:t tree-iter-max)))

(defrule tree-iter-min-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-iter-min tree0)
                  (tree-iter-min tree1)))
  :rule-classes :congruence
  :enable tree-iter-min)

(defrule tree-iter-max-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-iter-max tree0)
                  (tree-iter-max tree1)))
  :rule-classes :congruence
  :enable tree-iter-max)

(defrule tree-iter-plug-of-tree-iter-min
  (equal (tree-iter-plug (tree-iter-min tree))
         (tree-fix tree))
  :enable tree-iter-min)

(defrule tree-iter-plug-of-tree-iter-max
  (equal (tree-iter-plug (tree-iter-max tree))
         (tree-fix tree))
  :enable tree-iter-max)

;; A fresh iterator is at its far end exactly when there is nothing to walk,
;; and is never at its near end, since a step never lands there.

(defrule tree-iter-after-last-p-of-tree-iter-min
  (equal (tree-iter-after-last-p (tree-iter-min tree))
         (tree-empty-p tree))
  :enable (tree-iter-min
           tree-iter-next
           tree-iter-has-value-p))

(defrule tree-iter-before-first-p-of-tree-iter-max
  (equal (tree-iter-before-first-p (tree-iter-max tree))
         (tree-empty-p tree))
  :enable (tree-iter-max
           tree-iter-prev
           tree-iter-has-value-p))

(defrule not-tree-iter-before-first-p-of-tree-iter-min
  (not (tree-iter-before-first-p (tree-iter-min tree)))
  :enable tree-iter-min)

(defrule not-tree-iter-after-last-p-of-tree-iter-max
  (not (tree-iter-after-last-p (tree-iter-max tree)))
  :enable tree-iter-max)

;; Nothing lies behind a walk about to begin.

(defrule tree-iter-before-of-tree-iter-min
  (equal (tree-iter-before (tree-iter-min tree))
         nil)
  :enable (tree-iter-min
           tree-iter-before
           tree-iter-next
           tree-iter-has-value-p))

(defrule tree-iter-after-of-tree-iter-max
  (equal (tree-iter-after (tree-iter-max tree))
         nil)
  :enable (tree-iter-max
           tree-iter-after
           tree-iter-prev
           tree-iter-has-value-p))

;; What each walk reads first: the extremum on its own side.

(defrule tree-iter-value-of-tree-iter-min
  (implies (not (tree-empty-p tree))
           (equal (tree-iter-value (tree-iter-min tree))
                  (tree-leftmost tree)))
  :enable (tree-iter-min
           tree-iter-next
           tree-iter-value
           tree-iter-has-value-p))

(defrule tree-iter-value-of-tree-iter-max
  (implies (not (tree-empty-p tree))
           (equal (tree-iter-value (tree-iter-max tree))
                  (tree-rightmost tree)))
  :enable (tree-iter-max
           tree-iter-prev
           tree-iter-value
           tree-iter-has-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The value an iterator is at belongs to the tree it walks. This is what ties
;; the values a traversal produces to the contents of the tree, rather than
;; merely to its shape.

(defrule tree-in-of-tree-iter-value
  (implies (tree-iter-has-value-p iter)
           (tree-in (tree-iter-value iter)
                    (tree-iter-plug iter)))
  :enable (tree-iter-value
           tree-iter-plug
           tree-iter-has-value-p
           tree-in-order-of-zip-plug-split-at-cursor)
  :use (:instance member-equal-of-tree-in-order-under-iff
                  (x (zip-value (tree-iter->zip iter)))
                  (tree (zip-plug (tree-iter->zip iter))))
  :disable (member-equal-of-tree-in-order-under-iff
            tree-in-order-of-zip-plug))

;; The value a step lands on is the one that was at the head of what lay ahead.
;; With @(tsee tree-iter-after-of-tree-iter-next), which drops that same head,
;; this says a walk reads exactly the values to its right, in order.

(defrule tree-iter-value-of-tree-iter-next
  (implies (not (tree-iter-after-last-p (tree-iter-next iter)))
           (equal (tree-iter-value (tree-iter-next iter))
                  (car (tree-iter-after iter))))
  :enable (tree-iter-value
           tree-iter-next
           tree-iter-after
           tree-iter-has-value-p
           tree-in-order-becomes-value-and-after-of-zip-first))

;; A step lands on a value exactly when there was something ahead to land on.
;; This is what makes @(tsee tree-iter-after-of-tree-iter-next) usable: that
;; rule shortens the list ahead unconditionally, and this one says when the
;; list was nonempty to begin with.

(defrule tree-iter-has-value-p-of-tree-iter-next
  (equal (tree-iter-has-value-p (tree-iter-next iter))
         (consp (tree-iter-after iter)))
  :enable (tree-iter-after
           tree-iter-next
           tree-iter-has-value-p))

(defrule tree-iter-has-value-p-of-tree-iter-prev
  (equal (tree-iter-has-value-p (tree-iter-prev iter))
         (consp (tree-iter-before iter)))
  :enable (tree-iter-before
           tree-iter-prev
           tree-iter-has-value-p))

;; The only positions with no value are the two ends, and nothing lies ahead of
;; the right one. So anywhere but the left end, something ahead means a value
;; here. Left disabled: the conclusion is a type-like predicate that would
;; otherwise be tried against every position.

(defruled tree-iter-has-value-p-when-consp-of-tree-iter-after
  (implies (and (not (tree-iter-before-first-p iter))
                (consp (tree-iter-after iter)))
           (tree-iter-has-value-p iter))
  :enable (tree-iter-after
           tree-iter-has-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The sides as trees, through the three shapes. At an end the near side is
;; empty and the far side is the whole tree -- which is the plug itself, with
;; nothing to build.

(define tree-iter-tree-before ((iter tree-iter-p))
  :returns (tree treep)
  :short "The elements to the left of the iterator, as a tree."
  (cond ((tree-iter-before-first-p iter) nil)
        ((tree-iter-after-last-p iter) (tree-iter-plug iter))
        (t (zip-tree-before (tree-iter->zip iter)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-iter-tree-after ((iter tree-iter-p))
  :returns (tree treep)
  :short "The elements to the right of the iterator, as a tree."
  (cond ((tree-iter-after-last-p iter) nil)
        ((tree-iter-before-first-p iter) (tree-iter-plug iter))
        (t (zip-tree-after (tree-iter->zip iter)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-iter-tree-before) (:t tree-iter-tree-after)))

(defrule tree-iter-tree-before-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-tree-before iter0)
                  (tree-iter-tree-before iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-tree-before iter0)
           (tree-iter-tree-before iter1)))

(defrule tree-iter-tree-after-when-tree-iter-equiv-congruence
  (implies (tree-iter-equiv iter0 iter1)
           (equal (tree-iter-tree-after iter0)
                  (tree-iter-tree-after iter1)))
  :rule-classes :congruence
  :expand ((tree-iter-tree-after iter0)
           (tree-iter-tree-after iter1)))

;; The built trees hold exactly the elements of the oset sides.

(defrule tree-in-of-tree-iter-tree-before
  (equal (tree-in x (tree-iter-tree-before iter))
         (set::in x (tree-iter-oset-before iter)))
  :enable (tree-iter-tree-before
           tree-iter-oset-before))

(defrule tree-in-of-tree-iter-tree-after
  (equal (tree-in x (tree-iter-tree-after iter))
         (set::in x (tree-iter-oset-after iter)))
  :enable (tree-iter-tree-after
           tree-iter-oset-after))

;; Both invariants pass from the plug, so over a search tree the built sides
;; are proper treesets.

(defrule bstp-of-tree-iter-tree-before-when-bstp
  (implies (bstp (tree-iter-plug iter))
           (bstp (tree-iter-tree-before iter)))
  :enable (tree-iter-tree-before
           tree-iter-plug-when-tree-iter-has-value-p))

(defrule heapp-of-tree-iter-tree-before-when-heapp
  (implies (heapp (tree-iter-plug iter))
           (heapp (tree-iter-tree-before iter)))
  :enable (tree-iter-tree-before
           tree-iter-plug-when-tree-iter-has-value-p))

(defrule bstp-of-tree-iter-tree-after-when-bstp
  (implies (bstp (tree-iter-plug iter))
           (bstp (tree-iter-tree-after iter)))
  :enable (tree-iter-tree-after
           tree-iter-plug-when-tree-iter-has-value-p))

(defrule heapp-of-tree-iter-tree-after-when-heapp
  (implies (heapp (tree-iter-plug iter))
           (heapp (tree-iter-tree-after iter)))
  :enable (tree-iter-tree-after
           tree-iter-plug-when-tree-iter-has-value-p))
