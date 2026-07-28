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

(include-book "tree-defs")
(include-book "zipper")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cursor
  :parents (implementation)
  :short "A position in the in-order sequence of a @(see tree)."
  :long
  (xdoc::topstring
    (xdoc::p
      "A cursor is either a @(see zipper), which is at an element, or one of
       the two ends. A tree with @($n$) elements therefore has @($n+2$)
       cursors, running from before the first element to past the last.")
    (xdoc::p
      "The two ends are supplied here rather than found inside the tree. A
       zipper cannot serve as an end, because the empty subtrees which sit in
       the gaps of the in-order sequence number @($n+1$), so the empty tree
       has only one of them and could not tell its two ends apart. Carrying
       the tree alongside the tag keeps the ends distinct in every case, and
       keeps a cursor self-contained: it knows which tree it is a position
       in, whether or not it is at an element."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-p (x)
  (declare (xargs :type-prescription (booleanp (tree-cursor-p x))))
  :short "Recognizer for @(see cursor)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "The three cases cannot be confused: a zipper's focus is a nonempty tree,
      so the @(tsee car) of a zipper is a @(tsee consp), never a keyword."))
  (or (tree-zip-p x)
      (and (consp x)
           (or (eq (car x) :before-start)
               (eq (car x) :past-end))
           (treep (cdr x)))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-cursor-p-when-tree-zip-p
  (implies (tree-zip-p zip)
           (tree-cursor-p zip))
  :enable tree-cursor-p)

(defrule tree-cursor-p-compound-recognizer
  (implies (tree-cursor-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable (tree-cursor-p
           tree-zip-p))

;; A zipper is at an element, so its car is a tree node: a @(tsee consp), never
;; a tag. This is what keeps the three cases apart, and it does so by type
;; reasoning alone.

(defrule consp-of-car-when-tree-zip-p
  (implies (tree-zip-p zip)
           (consp (car zip)))
  :rule-classes (:rewrite :forward-chaining)
  :enable (tree-zip-p
           tree-empty-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-tree-cursor ()
  :returns (cursor tree-cursor-p
                   :hints (("Goal" :in-theory (enable tree-cursor-p))))
  :short "An irrelevant @(see cursor), used as the fixer's default."
  :long
  (xdoc::topstring
   (xdoc::p
     "Unlike a zipper, a cursor of the empty tree exists, so the default can
      be an honest one: the position before the start of the empty tree."))
  (cons :before-start nil))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-tree-cursor) (:e irr-tree-cursor)))

(defrule irr-tree-cursor-type-prescription
  (tree-cursor-p (irr-tree-cursor))
  :rule-classes ((:type-prescription :typed-term (irr-tree-cursor))))

;; The default is an end, not an element. Since its executable counterpart is
;; disabled, this has to be said rather than computed.

(defrule not-tree-zip-p-of-irr-tree-cursor
  (not (tree-zip-p (irr-tree-cursor)))
  :enable irr-tree-cursor)

(defrule car-of-irr-tree-cursor
  (equal (car (irr-tree-cursor))
         :before-start)
  :enable irr-tree-cursor)

(defrule cdr-of-irr-tree-cursor
  (equal (cdr (irr-tree-cursor))
         nil)
  :enable irr-tree-cursor)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-fix ((cursor tree-cursor-p))
  :returns (cursor$ tree-cursor-p)
  :short "Fixer for @(see cursor)s."
  (mbe :logic (if (tree-cursor-p cursor) cursor (irr-tree-cursor))
       :exec (the cons cursor))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-cursor-fix)))

(defrule tree-cursor-fix-type-prescription
  (tree-cursor-p (tree-cursor-fix cursor))
  :rule-classes ((:type-prescription :typed-term (tree-cursor-fix cursor))))

(defrule tree-cursor-fix-when-tree-cursor-p
  (implies (tree-cursor-p cursor)
           (equal (tree-cursor-fix cursor)
                  cursor))
  :enable tree-cursor-fix)

(defruled tree-cursor-fix-when-not-tree-cursor-p
  (implies (not (tree-cursor-p cursor))
           (equal (tree-cursor-fix cursor)
                  (irr-tree-cursor)))
  :enable tree-cursor-fix)

(defrule tree-cursor-fix-when-not-tree-cursor-p-cheap
  (implies (not (tree-cursor-p cursor))
           (equal (tree-cursor-fix cursor)
                  (irr-tree-cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-cursor-fix-when-not-tree-cursor-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-equiv
  ((x tree-cursor-p)
   (y tree-cursor-p))
  (declare (xargs :type-prescription (booleanp (tree-cursor-equiv x y))))
  :short "Equivalence up to @(tsee tree-cursor-fix)."
  (equal (tree-cursor-fix x)
         (tree-cursor-fix y))
  :inline t
  ///
  (defequiv tree-cursor-equiv
    :hints (("Goal" :in-theory (enable tree-cursor-equiv))))

  (defrule tree-cursor-fix-under-tree-cursor-equiv
    (tree-cursor-equiv (tree-cursor-fix cursor)
                       cursor)
    :enable tree-cursor-equiv)

  ;; With this in hand, every congruence below follows from the congruences of
  ;; the parts, with no definition unfolded.

  (defrule tree-cursor-fix-when-tree-cursor-equiv-congruence
    (implies (tree-cursor-equiv cursor0 cursor1)
             (equal (tree-cursor-fix cursor0)
                    (tree-cursor-fix cursor1)))
    :rule-classes :congruence
    :enable tree-cursor-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The three constructors. The zipper case needs none: a zipper is already a
;; cursor.

(define tree-cursor-before-start ((tree treep))
  :returns (cursor tree-cursor-p
                   :hints (("Goal" :in-theory (enable tree-cursor-p))))
  :short "The cursor before the first element of a tree."
  (cons :before-start (tree-fix tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-past-end ((tree treep))
  :returns (cursor tree-cursor-p
                   :hints (("Goal" :in-theory (enable tree-cursor-p))))
  :short "The cursor past the last element of a tree."
  (cons :past-end (tree-fix tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-cursor-before-start) (:t tree-cursor-past-end)))

(defrule tree-cursor-before-start-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-cursor-before-start tree0)
                  (tree-cursor-before-start tree1)))
  :rule-classes :congruence
  :enable tree-cursor-before-start)

(defrule tree-cursor-past-end-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-cursor-past-end tree0)
                  (tree-cursor-past-end tree1)))
  :rule-classes :congruence
  :enable tree-cursor-past-end)

;; The two ends are distinct for every tree, including the empty one. This is
;; the whole reason they are added here rather than found in the tree.

(defrule tree-cursor-before-start-not-equal-tree-cursor-past-end
  (not (equal (tree-cursor-before-start tree0)
              (tree-cursor-past-end tree1)))
  :enable (tree-cursor-before-start
           tree-cursor-past-end))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Each test goes through the fixer, so that all three respect @(tsee
;; tree-cursor-equiv). Under the guard the fixer is the identity, so the
;; executable form reads the tag directly.

(define tree-cursor-before-start-p ((cursor tree-cursor-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the cursor is before the first element."
  (mbe :logic (eq (car (tree-cursor-fix cursor)) :before-start)
       :exec (eq (car cursor) :before-start))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-past-end-p ((cursor tree-cursor-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the cursor is past the last element."
  (mbe :logic (eq (car (tree-cursor-fix cursor)) :past-end)
       :exec (eq (car cursor) :past-end))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-at-element-p ((cursor tree-cursor-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the cursor is at an element."
  (tree-zip-p (tree-cursor-fix cursor))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-cursor-before-start-p)
                    (:t tree-cursor-past-end-p)
                    (:t tree-cursor-at-element-p)))

(defrule tree-cursor-before-start-p-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor-before-start-p cursor0)
                  (tree-cursor-before-start-p cursor1)))
  :rule-classes :congruence
  :enable (tree-cursor-before-start-p
           tree-cursor-equiv))

(defrule tree-cursor-past-end-p-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor-past-end-p cursor0)
                  (tree-cursor-past-end-p cursor1)))
  :rule-classes :congruence
  :enable (tree-cursor-past-end-p
           tree-cursor-equiv))

(defrule tree-cursor-at-element-p-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor-at-element-p cursor0)
                  (tree-cursor-at-element-p cursor1)))
  :rule-classes :congruence
  :enable (tree-cursor-at-element-p
           tree-cursor-equiv))

;; The three cases are exclusive and exhaustive.

(defrule tree-cursor-at-element-p-when-tree-zip-p
  (implies (tree-zip-p zip)
           (tree-cursor-at-element-p zip))
  :enable tree-cursor-at-element-p)

(defrule not-tree-cursor-before-start-p-when-tree-cursor-at-element-p
  (implies (tree-cursor-at-element-p cursor)
           (not (tree-cursor-before-start-p cursor)))
  :enable (tree-cursor-at-element-p
           tree-cursor-before-start-p
           tree-cursor-fix
           tree-zip-p
           tree-empty-p
           irr-tree-cursor))

(defrule not-tree-cursor-past-end-p-when-tree-cursor-at-element-p
  (implies (tree-cursor-at-element-p cursor)
           (not (tree-cursor-past-end-p cursor)))
  :enable (tree-cursor-at-element-p
           tree-cursor-past-end-p
           tree-cursor-fix
           tree-zip-p
           tree-empty-p
           irr-tree-cursor))

(defrule not-tree-cursor-before-start-p-when-tree-cursor-past-end-p
  (implies (tree-cursor-past-end-p cursor)
           (not (tree-cursor-before-start-p cursor)))
  :enable (tree-cursor-past-end-p
           tree-cursor-before-start-p))

;; A zipper carries no tag, so it is neither end.

(defrule not-tree-cursor-before-start-p-when-tree-zip-p
  (implies (tree-zip-p zip)
           (not (tree-cursor-before-start-p zip)))
  :enable (tree-cursor-before-start-p
           tree-cursor-fix))

(defrule not-tree-cursor-past-end-p-when-tree-zip-p
  (implies (tree-zip-p zip)
           (not (tree-cursor-past-end-p zip)))
  :enable (tree-cursor-past-end-p
           tree-cursor-fix))

;; A zipper is never equal to an end, whichever tree the end carries. This is
;; the form the move proofs need, where one side is a constructed end and the
;; other is a zipper a move landed on.

(defrule not-equal-of-tree-zip-p-and-tree-cursor-before-start
  (implies (tree-zip-p zip)
           (not (equal zip (tree-cursor-before-start tree))))
  :enable (tree-cursor-before-start
           tree-zip-p
           treep))

(defrule not-equal-of-tree-zip-p-and-tree-cursor-past-end
  (implies (tree-zip-p zip)
           (not (equal zip (tree-cursor-past-end tree))))
  :enable (tree-cursor-past-end
           tree-zip-p
           treep))

;; And conversely, in the direction which lets a proof conclude that a cursor
;; landing on a zipper was not at an end to begin with.

(defrule not-tree-cursor-at-element-p-when-tree-cursor-before-start-p
  (implies (tree-cursor-before-start-p cursor)
           (not (tree-cursor-at-element-p cursor)))
  :enable (tree-cursor-at-element-p
           tree-cursor-before-start-p))

(defrule not-tree-cursor-at-element-p-when-tree-cursor-past-end-p
  (implies (tree-cursor-past-end-p cursor)
           (not (tree-cursor-at-element-p cursor)))
  :enable (tree-cursor-at-element-p
           tree-cursor-past-end-p))

;; No @(tsee tree-cursor-p) hypothesis is needed: anything which is not a
;; cursor fixes to @(tsee irr-tree-cursor), which is before the start, so
;; failing both tests already implies being a cursor.

(defrule tree-cursor-at-element-p-when-neither-end
  (implies (and (not (tree-cursor-before-start-p cursor))
                (not (tree-cursor-past-end-p cursor)))
           (tree-cursor-at-element-p cursor))
  :enable (tree-cursor-p
           tree-cursor-at-element-p
           tree-cursor-before-start-p
           tree-cursor-past-end-p
           tree-cursor-fix
           irr-tree-cursor))

;; The same fact phrased on @(tsee tree-zip-p), which is what the guards of the
;; zipper operations actually ask for.

(defrule tree-zip-p-when-neither-end
  (implies (and (not (tree-cursor-before-start-p cursor))
                (not (tree-cursor-past-end-p cursor)))
           (tree-zip-p cursor))
  :enable (tree-cursor-p
           tree-cursor-before-start-p
           tree-cursor-past-end-p
           tree-cursor-fix
           irr-tree-cursor))

;; What the predicates say about the constructors.

(defrule tree-cursor-before-start-p-of-tree-cursor-before-start
  (tree-cursor-before-start-p (tree-cursor-before-start tree))
  :enable (tree-cursor-before-start-p
           tree-cursor-before-start
           tree-cursor-fix
           tree-cursor-p))

(defrule tree-cursor-past-end-p-of-tree-cursor-past-end
  (tree-cursor-past-end-p (tree-cursor-past-end tree))
  :enable (tree-cursor-past-end-p
           tree-cursor-past-end
           tree-cursor-fix
           tree-cursor-p))

(defrule not-tree-cursor-past-end-p-of-tree-cursor-before-start
  (not (tree-cursor-past-end-p (tree-cursor-before-start tree)))
  :enable (tree-cursor-past-end-p
           tree-cursor-before-start
           tree-cursor-fix
           tree-cursor-p))

(defrule not-tree-cursor-before-start-p-of-tree-cursor-past-end
  (not (tree-cursor-before-start-p (tree-cursor-past-end tree)))
  :enable (tree-cursor-before-start-p
           tree-cursor-past-end
           tree-cursor-fix
           tree-cursor-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor->zip ((cursor tree-cursor-p))
  :guard (tree-cursor-at-element-p cursor)
  :returns (zip tree-zip-p)
  :short "Get the zipper of a cursor which is at an element."
  (mbe :logic (if (tree-zip-p (tree-cursor-fix cursor))
                  (tree-cursor-fix cursor)
                (irr-tree-zip))
       :exec cursor)
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-cursor-at-element-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-cursor->zip)))

(defrule tree-cursor->zip-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor->zip cursor0)
                  (tree-cursor->zip cursor1)))
  :rule-classes :congruence
  :enable (tree-cursor->zip
           tree-cursor-equiv))

(defrule tree-cursor->zip-when-tree-zip-p
  (implies (tree-zip-p zip)
           (equal (tree-cursor->zip zip)
                  zip))
  :enable tree-cursor->zip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; At either end, what the cursor carries is the tree.

(defrule treep-of-cdr-when-tree-cursor-p-and-not-at-element
  (implies (and (tree-cursor-p cursor)
                (not (tree-cursor-at-element-p cursor)))
           (treep (cdr cursor)))
  :enable (tree-cursor-p
           tree-cursor-at-element-p
           tree-cursor-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-plug ((cursor tree-cursor-p))
  :returns (tree treep)
  :short "Recover the tree a cursor is a position in."
  :long
  (xdoc::topstring
   (xdoc::p
     "At an element this is the zipper's own @(tsee tree-zip-plug); at either
      end it is the tree the cursor carries."))
  (if (tree-cursor-at-element-p cursor)
      (tree-zip-plug (tree-cursor->zip cursor))
    (tree-fix (cdr (tree-cursor-fix cursor))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-cursor-plug)))

(defrule tree-cursor-plug-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor-plug cursor0)
                  (tree-cursor-plug cursor1)))
  :rule-classes :congruence
  :expand ((tree-cursor-plug cursor0)
           (tree-cursor-plug cursor1)))

(defrule tree-cursor-plug-when-tree-zip-p
  (implies (tree-zip-p zip)
           (equal (tree-cursor-plug zip)
                  (tree-zip-plug zip)))
  :enable tree-cursor-plug)

;; The two cases of the definition, as rules, so that proofs about the moves
;; never have to open it.

(defrule tree-cursor-plug-when-tree-cursor-at-element-p
  (implies (tree-cursor-at-element-p cursor)
           (equal (tree-cursor-plug cursor)
                  (tree-zip-plug (tree-cursor->zip cursor))))
  :enable tree-cursor-plug)

(defruledl tree-cursor-plug-when-not-tree-cursor-at-element-p
  (implies (not (tree-cursor-at-element-p cursor))
           (equal (tree-cursor-plug cursor)
                  (tree-fix (cdr (tree-cursor-fix cursor)))))
  :enable tree-cursor-plug)

;; An end carries nothing but its tree, so it is recovered from that tree
;; alone. This is what makes the two ends unique, and so what the round trips
;; come down to once a move has landed on one.

(defruledl tree-cursor-fix-when-tree-cursor-before-start-p
  (implies (tree-cursor-before-start-p cursor)
           (equal (tree-cursor-fix cursor)
                  (tree-cursor-before-start (tree-cursor-plug cursor))))
  :enable (tree-cursor-before-start-p
           tree-cursor-before-start
           tree-cursor-at-element-p
           tree-cursor-plug
           tree-cursor-fix
           tree-cursor-p))

(defruledl tree-cursor-fix-when-tree-cursor-past-end-p
  (implies (tree-cursor-past-end-p cursor)
           (equal (tree-cursor-fix cursor)
                  (tree-cursor-past-end (tree-cursor-plug cursor))))
  :enable (tree-cursor-past-end-p
           tree-cursor-past-end
           tree-cursor-at-element-p
           tree-cursor-plug
           tree-cursor-fix
           tree-cursor-p))

;; The two rules just above rewrite a fixed cursor into a plugged one, and the
;; rule above them rewrites a plugged cursor back into a fixed one. Enabling
;; both directions at once loops. They are all disabled, but they are natural
;; companions and easy to reach for together, so say so rather than leaving a
;; trap.

(theory-invariant
  (incompatible (:rewrite tree-cursor-fix-when-tree-cursor-before-start-p)
                (:rewrite tree-cursor-plug-when-not-tree-cursor-at-element-p)))

(theory-invariant
  (incompatible (:rewrite tree-cursor-fix-when-tree-cursor-past-end-p)
                (:rewrite tree-cursor-plug-when-not-tree-cursor-at-element-p)))

(defrule tree-cursor-plug-of-tree-cursor-before-start
  (equal (tree-cursor-plug (tree-cursor-before-start tree))
         (tree-fix tree))
  :enable (tree-cursor-plug
           tree-cursor-at-element-p
           tree-cursor-before-start
           tree-cursor-fix
           tree-zip-p
           tree-empty-p
           tree-cursor-p))

(defrule tree-cursor-plug-of-tree-cursor-past-end
  (equal (tree-cursor-plug (tree-cursor-past-end tree))
         (tree-fix tree))
  :enable (tree-cursor-plug
           tree-cursor-at-element-p
           tree-cursor-past-end
           tree-cursor-fix
           tree-zip-p
           tree-empty-p
           tree-cursor-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-next ((cursor tree-cursor-p))
  :returns (cursor$ tree-cursor-p)
  :short "Move the cursor to the next position."
  :long
  (xdoc::topstring
   (xdoc::p
     "Past the end the move saturates. From before the start it steps to the
      first element, or straight to the other end when the tree is empty,
      since then there is no element to stop at. At an element it hands the
      step to @(tsee tree-zip-next), except at the last element, where it
      leaves the elements behind.")
   (xdoc::p
     "Time complexity: @($O(d)$) in the worst case, @($O(1)$) amortized over a
      traversal."))
  (cond ((tree-cursor-past-end-p cursor)
         (tree-cursor-fix cursor))
        ((tree-cursor-before-start-p cursor)
         (let ((tree (tree-cursor-plug cursor)))
           (if (tree-empty-p tree)
               (tree-cursor-past-end tree)
             (tree-zip-first tree))))
        (t
         (let ((zip (tree-cursor->zip cursor)))
           (if (tree-zip-at-last-p zip)
               (tree-cursor-past-end (tree-zip-plug zip))
             (tree-zip-next zip)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-cursor-at-element-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-cursor-prev ((cursor tree-cursor-p))
  :returns (cursor$ tree-cursor-p)
  :short "Move the cursor to the previous position."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee tree-cursor-next)."))
  (cond ((tree-cursor-before-start-p cursor)
         (tree-cursor-fix cursor))
        ((tree-cursor-past-end-p cursor)
         (let ((tree (tree-cursor-plug cursor)))
           (if (tree-empty-p tree)
               (tree-cursor-before-start tree)
             (tree-zip-last tree))))
        (t
         (let ((zip (tree-cursor->zip cursor)))
           (if (tree-zip-at-first-p zip)
               (tree-cursor-before-start (tree-zip-plug zip))
             (tree-zip-prev zip)))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-cursor-at-element-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-cursor-next) (:t tree-cursor-prev)))

(defrule tree-cursor-next-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor-next cursor0)
                  (tree-cursor-next cursor1)))
  :rule-classes :congruence
  :expand ((tree-cursor-next cursor0)
           (tree-cursor-next cursor1)))

(defrule tree-cursor-prev-when-tree-cursor-equiv-congruence
  (implies (tree-cursor-equiv cursor0 cursor1)
           (equal (tree-cursor-prev cursor0)
                  (tree-cursor-prev cursor1)))
  :rule-classes :congruence
  :expand ((tree-cursor-prev cursor0)
           (tree-cursor-prev cursor1)))

;; Emptiness of a plugged tree, in the two forms the move proofs need. Stated
;; here rather than enabling @(tsee tree-empty-p) in those proofs, which would
;; rewrite it out of the very rules that mention it.

(defrulel tree-cursor-plug-when-tree-empty-p-of-tree-cursor-plug
  (implies (tree-empty-p (tree-cursor-plug cursor))
           (equal (tree-cursor-plug cursor)
                  nil))
  :use (:instance tree-empty-p-when-treep (tree (tree-cursor-plug cursor))))

(defrulel not-tree-empty-p-of-tree-cursor-plug-when-consp
  (implies (consp (tree-cursor-plug cursor))
           (not (tree-empty-p (tree-cursor-plug cursor))))
  :use (:instance tree-empty-p-when-treep (tree (tree-cursor-plug cursor))))

;; Moving never changes the tree the cursor is a position in.

(defrule tree-cursor-plug-of-tree-cursor-next
  (equal (tree-cursor-plug (tree-cursor-next cursor))
         (tree-cursor-plug cursor))
  :enable (tree-cursor-next
           tree-cursor-at-element-p))

(defrule tree-cursor-plug-of-tree-cursor-prev
  (equal (tree-cursor-plug (tree-cursor-prev cursor))
         (tree-cursor-plug cursor))
  :enable (tree-cursor-prev
           tree-cursor-at-element-p))

;; The ends saturate.

(defrule tree-cursor-next-when-tree-cursor-past-end-p
  (implies (tree-cursor-past-end-p cursor)
           (equal (tree-cursor-next cursor)
                  (tree-cursor-fix cursor)))
  :enable tree-cursor-next)

(defrule tree-cursor-prev-when-tree-cursor-before-start-p
  (implies (tree-cursor-before-start-p cursor)
           (equal (tree-cursor-prev cursor)
                  (tree-cursor-fix cursor)))
  :enable tree-cursor-prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two moves are inverse everywhere they have somewhere to go. Unlike the
;; zipper laws these need no side conditions at all beyond the end being
;; stepped away from: every position an iterator can occupy is a cursor, so
;; there is nothing left to exclude.

(defrule tree-cursor-prev-of-tree-cursor-next
  (implies (not (tree-cursor-past-end-p cursor))
           (equal (tree-cursor-prev (tree-cursor-next cursor))
                  (tree-cursor-fix cursor)))
  :enable (tree-cursor-next
           tree-cursor-prev
           tree-cursor-at-element-p
           tree-cursor-fix-when-tree-cursor-before-start-p
           tree-cursor-fix-when-tree-cursor-past-end-p))

(defrule tree-cursor-next-of-tree-cursor-prev
  (implies (not (tree-cursor-before-start-p cursor))
           (equal (tree-cursor-next (tree-cursor-prev cursor))
                  (tree-cursor-fix cursor)))
  :enable (tree-cursor-next
           tree-cursor-prev
           tree-cursor-at-element-p
           tree-cursor-fix-when-tree-cursor-before-start-p
           tree-cursor-fix-when-tree-cursor-past-end-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A move is the identity exactly at the end it saturates against. Reaching a
;; fixed point means being done, not being stuck, which is what lets a
;; traversal test for completion by comparing against the previous cursor.
;;
;; The three cases are separate: at an element the zipper law applies; from an
;; end, a step either lands on an element or crosses to the other end, and both
;; differ from where it started, the latter because the two ends carry
;; different tags.

(defrule tree-cursor-next-identity-iff-tree-cursor-past-end-p
  (equal (equal (tree-cursor-next cursor) (tree-cursor-fix cursor))
         (tree-cursor-past-end-p cursor))
  :use (:instance tree-zip-next-identity-iff-tree-zip-at-last-p (zip cursor))
  :disable tree-zip-next-identity-iff-tree-zip-at-last-p
  :enable (tree-cursor-next
           tree-cursor->zip
           tree-cursor-at-element-p
           tree-cursor-fix-when-tree-cursor-before-start-p
           tree-cursor-fix-when-tree-cursor-past-end-p))

(defrule tree-cursor-prev-identity-iff-tree-cursor-before-start-p
  (equal (equal (tree-cursor-prev cursor) (tree-cursor-fix cursor))
         (tree-cursor-before-start-p cursor))
  :use (:instance tree-zip-prev-identity-iff-tree-zip-at-first-p (zip cursor))
  :disable tree-zip-prev-identity-iff-tree-zip-at-first-p
  :enable (tree-cursor-prev
           tree-cursor->zip
           tree-cursor-at-element-p
           tree-cursor-fix-when-tree-cursor-before-start-p
           tree-cursor-fix-when-tree-cursor-past-end-p))
