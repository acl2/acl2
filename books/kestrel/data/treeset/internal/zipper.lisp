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
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "count-defs")
(include-book "in-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "count"))
(local (include-book "in-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ zipper
  :parents (implementation)
  :short "A cursor into a @(see tree)."
  :long
  (xdoc::topstring
    (xdoc::p
      "A zipper is a subtree in focus, paired with a path recording the
       descent from the root to that focus. The path holds everything the
       focus does not, so the whole tree can be recovered from a zipper, and a
       zipper can be moved without rebuilding the tree from scratch.")
    (xdoc::p
      "The focus may be empty. Since a tree with @($n$) nodes has @($n+1$)
       empty subtrees, and those sit exactly in the @($n+1$) gaps of the
       in-order sequence, an empty focus denotes a position between (or
       outside) elements rather than at one."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame-p (x)
  (declare (xargs :type-prescription (booleanp (tree-zip-frame-p x))))
  :short "Recognizer for zipper path frames."
  :long
  (xdoc::topstring
   (xdoc::p
     "A frame records one step of the descent from the root to the focus. It
      holds the element of the node descended through, the child not descended
      into, and a flag distinguishing the two cases: @('from-left') is true
      when the focus lies in the left child, in which case the sibling is that
      node's right subtree, and vice versa.")
   (xdoc::p
     "The flag is required to be a @(tsee booleanp) so that frames, and hence
      zippers, are unique."))
  (and (consp x)
       (booleanp (car x))
       (consp (cdr x))
       (tree-element-p (cadr x))
       (treep (cddr x))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-frame-p-compound-recognizer
  (implies (tree-zip-frame-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable tree-zip-frame-p)

(defrule consp-of-cdr-when-tree-zip-frame-p-forward-chaining
  (implies (tree-zip-frame-p x)
           (consp (cdr x)))
  :rule-classes :forward-chaining
  :enable tree-zip-frame-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-tree-zip-frame ()
  :returns (frame tree-zip-frame-p
                  :hints (("Goal" :in-theory (enable tree-zip-frame-p))))
  (cons nil (cons (irr-tree-element) nil)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-tree-zip-frame) (:e irr-tree-zip-frame)))

(defrule irr-tree-zip-frame-type-prescription
  (tree-zip-frame-p (irr-tree-zip-frame))
  :rule-classes ((:type-prescription :typed-term (irr-tree-zip-frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame-fix ((frame tree-zip-frame-p))
  :returns (frame$ tree-zip-frame-p)
  :short "Fixer for @(see tree-zip-frame-p)s."
  (mbe :logic (if (tree-zip-frame-p frame) frame (irr-tree-zip-frame))
       :exec (the cons frame))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-frame-fix)))

(defrule tree-zip-frame-fix-type-prescription
  (tree-zip-frame-p (tree-zip-frame-fix frame))
  :rule-classes ((:type-prescription :typed-term (tree-zip-frame-fix frame))))

(defrule tree-zip-frame-fix-when-tree-zip-frame-p
  (implies (tree-zip-frame-p frame)
           (equal (tree-zip-frame-fix frame)
                  frame))
  :enable tree-zip-frame-fix)

(defruled tree-zip-frame-fix-when-not-tree-zip-frame-p
  (implies (not (tree-zip-frame-p frame))
           (equal (tree-zip-frame-fix frame)
                  (irr-tree-zip-frame)))
  :enable tree-zip-frame-fix)

(defrule tree-zip-frame-fix-when-not-tree-zip-frame-p-cheap
  (implies (not (tree-zip-frame-p frame))
           (equal (tree-zip-frame-fix frame)
                  (irr-tree-zip-frame)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-zip-frame-fix-when-not-tree-zip-frame-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame-equiv
  ((x tree-zip-frame-p)
   (y tree-zip-frame-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Equivalence up to @(tsee tree-zip-frame-fix)."
  (equal (tree-zip-frame-fix x)
         (tree-zip-frame-fix y))
  :inline t

  ///

  (defequiv tree-zip-frame-equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-frame-equiv)))

(defrule tree-zip-frame-fix-when-tree-zip-frame-equiv-congruence
  (implies (tree-zip-frame-equiv frame0 frame1)
           (equal (tree-zip-frame-fix frame0)
                  (tree-zip-frame-fix frame1)))
  :rule-classes :congruence
  :enable tree-zip-frame-equiv)

(defrule tree-zip-frame-fix-under-tree-zip-frame-equiv
  (tree-zip-frame-equiv (tree-zip-frame-fix frame)
                        frame)
  :enable tree-zip-frame-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame->from-left ((frame tree-zip-frame-p))
  :returns (from-left booleanp
                      :hints (("Goal" :in-theory (enable tree-zip-frame-p
                                                         tree-zip-frame-fix
                                                         irr-tree-zip-frame))))
  :short "Check whether the focus lies in the left child of the frame's node."
  (car (tree-zip-frame-fix frame))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-frame->from-left-when-tree-zip-frame-equiv-congruence
  (implies (tree-zip-frame-equiv frame0 frame1)
           (equal (tree-zip-frame->from-left frame0)
                  (tree-zip-frame->from-left frame1)))
  :rule-classes :congruence
  :enable (tree-zip-frame->from-left
           tree-zip-frame-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame->elem ((frame tree-zip-frame-p))
  :returns (elem tree-element-p
                 :hints (("Goal" :in-theory (enable tree-zip-frame-p
                                                    tree-zip-frame-fix
                                                    irr-tree-zip-frame))))
  :short "Get the element of the frame's node."
  (cadr (tree-zip-frame-fix frame))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-frame-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-frame->elem-when-tree-zip-frame-equiv-congruence
  (implies (tree-zip-frame-equiv frame0 frame1)
           (equal (tree-zip-frame->elem frame0)
                  (tree-zip-frame->elem frame1)))
  :rule-classes :congruence
  :enable (tree-zip-frame->elem
           tree-zip-frame-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame->sibling ((frame tree-zip-frame-p))
  :returns (sibling treep
                    :hints (("Goal" :in-theory (enable tree-zip-frame-p
                                                       tree-zip-frame-fix
                                                       irr-tree-zip-frame))))
  :short "Get the child of the frame's node not descended into."
  (cddr (tree-zip-frame-fix frame))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-frame-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-frame->sibling-when-tree-zip-frame-equiv-congruence
  (implies (tree-zip-frame-equiv frame0 frame1)
           (equal (tree-zip-frame->sibling frame0)
                  (tree-zip-frame->sibling frame1)))
  :rule-classes :congruence
  :enable (tree-zip-frame->sibling
           tree-zip-frame-equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame
  ((from-left booleanp)
   (elem tree-element-p)
   (sibling treep))
  :returns (frame tree-zip-frame-p
                  :hints (("Goal" :in-theory (enable tree-zip-frame-p))))
  :short "Constructor for @(see tree-zip-frame-p)s."
  (cons (if from-left t nil)
        (cons (tree-element-fix elem)
              (tree-fix sibling)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-frame)))

(defrule tree-zip-frame-type-prescription
  (tree-zip-frame-p (tree-zip-frame from-left elem sibling))
  :rule-classes ((:type-prescription
                   :typed-term (tree-zip-frame from-left elem sibling))))

(defrule tree-zip-frame-when-tree-element-equiv-of-arg2-congruence
  (implies (tree-element-equiv elem0 elem1)
           (equal (tree-zip-frame from-left elem0 sibling)
                  (tree-zip-frame from-left elem1 sibling)))
  :rule-classes :congruence
  :enable tree-zip-frame)

(defrule tree-zip-frame-when-tree-equiv-of-arg3-congruence
  (implies (tree-equiv sibling0 sibling1)
           (equal (tree-zip-frame from-left elem sibling0)
                  (tree-zip-frame from-left elem sibling1)))
  :rule-classes :congruence
  :enable tree-zip-frame)

(defrule tree-zip-frame->from-left-of-tree-zip-frame
  (equal (tree-zip-frame->from-left (tree-zip-frame from-left elem sibling))
         (and from-left t))
  :enable (tree-zip-frame
           tree-zip-frame->from-left
           tree-zip-frame-fix
           tree-zip-frame-p))

(defrule tree-zip-frame->elem-of-tree-zip-frame
  (equal (tree-zip-frame->elem (tree-zip-frame from-left elem sibling))
         (tree-element-fix elem))
  :enable (tree-zip-frame
           tree-zip-frame->elem
           tree-zip-frame-fix
           tree-zip-frame-p))

(defrule tree-zip-frame->sibling-of-tree-zip-frame
  (equal (tree-zip-frame->sibling (tree-zip-frame from-left elem sibling))
         (tree-fix sibling))
  :enable (tree-zip-frame
           tree-zip-frame->sibling
           tree-zip-frame-fix
           tree-zip-frame-p))

(defrule tree-zip-frame-elim
  (implies (tree-zip-frame-p frame)
           (equal (tree-zip-frame (tree-zip-frame->from-left frame)
                                  (tree-zip-frame->elem frame)
                                  (tree-zip-frame->sibling frame))
                  frame))
  :rule-classes :elim
  :enable (tree-zip-frame
           tree-zip-frame->from-left
           tree-zip-frame->elem
           tree-zip-frame->sibling
           tree-zip-frame-fix
           tree-zip-frame-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame-listp (x)
  (declare (xargs :type-prescription (booleanp (tree-zip-frame-listp x))))
  :short "Recognizer for lists of @(see tree-zip-frame-p)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "A path is such a list, ordered from the frame nearest the focus to the
      frame of the root."))
  (if (consp x)
      (and (tree-zip-frame-p (car x))
           (tree-zip-frame-listp (cdr x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;

(defruled true-listp-when-tree-zip-frame-listp
  (implies (tree-zip-frame-listp x)
           (true-listp x))
  :induct t
  :enable tree-zip-frame-listp)

(defrule tree-zip-frame-listp-compound-recognizer
  (implies (tree-zip-frame-listp x)
           (true-listp x))
  :rule-classes :compound-recognizer
  :by true-listp-when-tree-zip-frame-listp)

(defrule tree-zip-frame-p-of-car-when-tree-zip-frame-listp
  (implies (and (tree-zip-frame-listp path)
                (consp path))
           (tree-zip-frame-p (car path)))
  :enable tree-zip-frame-listp)

(defrule tree-zip-frame-listp-of-cdr
  (implies (tree-zip-frame-listp path)
           (tree-zip-frame-listp (cdr path)))
  :enable tree-zip-frame-listp)

(defrule tree-zip-frame-listp-of-cons
  (equal (tree-zip-frame-listp (cons frame path))
         (and (tree-zip-frame-p frame)
              (tree-zip-frame-listp path)))
  :enable tree-zip-frame-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame-list-fix ((path tree-zip-frame-listp))
  :returns (path$ tree-zip-frame-listp)
  :short "Fixer for @(see tree-zip-frame-listp)s."
  (mbe :logic (if (tree-zip-frame-listp path) path nil)
       :exec (the list path))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-frame-list-fix-when-tree-zip-frame-listp
  (implies (tree-zip-frame-listp path)
           (equal (tree-zip-frame-list-fix path)
                  path))
  :enable tree-zip-frame-list-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-count-lefts ((path tree-zip-frame-listp))
  :returns (count natp :rule-classes :type-prescription)
  :short "Count the frames of a path whose focus lies in the left child."
  :long
  (xdoc::topstring
   (xdoc::p
     "These are exactly the frames whose node follows the focus in order. A
      zipper caches this count so that it can tell in constant time whether
      anything remains to its right."))
  (if (endp path)
      0
    (+ (if (tree-zip-frame->from-left (car path)) 1 0)
       (tree-zip-count-lefts (cdr path)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-count-rights ((path tree-zip-frame-listp))
  :returns (count natp :rule-classes :type-prescription)
  :short "Count the frames of a path whose focus lies in the right child."
  :long
  (xdoc::topstring
   (xdoc::p
     "These are exactly the frames whose node precedes the focus in order. A
      zipper caches this count so that it can tell in constant time whether
      anything remains to its left."))
  (if (endp path)
      0
    (+ (if (tree-zip-frame->from-left (car path)) 0 1)
       (tree-zip-count-rights (cdr path)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-count-lefts) (:t tree-zip-count-rights)))

(defrule tree-zip-count-lefts-of-cons
  (equal (tree-zip-count-lefts (cons frame path))
         (+ (if (tree-zip-frame->from-left frame) 1 0)
            (tree-zip-count-lefts path)))
  :enable tree-zip-count-lefts)

(defrule tree-zip-count-rights-of-cons
  (equal (tree-zip-count-rights (cons frame path))
         (+ (if (tree-zip-frame->from-left frame) 0 1)
            (tree-zip-count-rights path)))
  :enable tree-zip-count-rights)

(defrule tree-zip-count-lefts-when-not-consp-cheap
  (implies (not (consp path))
           (equal (tree-zip-count-lefts path)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-zip-count-lefts)

(defrule tree-zip-count-rights-when-not-consp-cheap
  (implies (not (consp path))
           (equal (tree-zip-count-rights path)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-zip-count-rights)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-p (x)
  (declare (xargs :type-prescription (booleanp (tree-zip-p x))))
  :short "Recognizer for @(see zipper)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "A zipper pairs a focus with the path from the root down to it, along with
      the two frame counts of that path. The counts are redundant, but caching
      them is what makes the boundary checks constant time. Since they are
      determined by the path, zippers remain unique.")
   (xdoc::p
     "The focus is never empty: a zipper is always at an element. A tree with
      @($n$) nodes has @($n+1$) empty subtrees, one per gap of the in-order
      sequence, but only the two outermost of those are positions an iterator
      would ever occupy, and admitting all @($n+1$) would mean admitting
      @($n-1$) values that are not positions at all. The two ends are supplied
      instead by a layer above this one, which can also tell them apart on the
      empty tree, where there is only one gap to be found.")
   (xdoc::p
     "This recognizer is structural only. Whether the tree recovered from a
      zipper satisfies the @(see treeset) invariants is a separate question."))
  (and (consp x)
       (consp (cdr x))
       (consp (cddr x))
       (treep (car x))
       (not (tree-empty-p (car x)))
       (tree-zip-frame-listp (cadr x))
       (equal (caddr x) (tree-zip-count-lefts (cadr x)))
       (equal (cdddr x) (tree-zip-count-rights (cadr x)))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-p-compound-recognizer
  (implies (tree-zip-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable tree-zip-p)

(defrule consp-of-cdr-when-tree-zip-p-forward-chaining
  (implies (tree-zip-p x)
           (consp (cdr x)))
  :rule-classes :forward-chaining
  :enable tree-zip-p)

(defrule consp-of-cddr-when-tree-zip-p-forward-chaining
  (implies (tree-zip-p x)
           (consp (cddr x)))
  :rule-classes :forward-chaining
  :enable tree-zip-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-tree-zip ()
  :returns (zip tree-zip-p
                :hints (("Goal" :in-theory (enable tree-zip-p))))
  :short "An irrelevant @(see zipper), used as the fixer's default."
  :long
  (xdoc::topstring
   (xdoc::p
     "The empty tree has no zipper at all, so the default cannot be built from
      it. This is the zipper of the one-node tree holding an irrelevant
      element, focused at the root."))
  (cons (tree-node (irr-tree-element) nil nil)
        (cons nil (cons 0 0))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t irr-tree-zip) (:e irr-tree-zip)))

(defrule irr-tree-zip-type-prescription
  (tree-zip-p (irr-tree-zip))
  :rule-classes ((:type-prescription :typed-term (irr-tree-zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-fix ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Fixer for @(see zipper)s."
  (mbe :logic (if (tree-zip-p zip) zip (irr-tree-zip))
       :exec (the cons zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-fix)))

(defrule tree-zip-fix-type-prescription
  (tree-zip-p (tree-zip-fix zip))
  :rule-classes ((:type-prescription :typed-term (tree-zip-fix zip))))

(defrule tree-zip-fix-when-tree-zip-p
  (implies (tree-zip-p zip)
           (equal (tree-zip-fix zip)
                  zip))
  :enable tree-zip-fix)

(defruled tree-zip-fix-when-not-tree-zip-p
  (implies (not (tree-zip-p zip))
           (equal (tree-zip-fix zip)
                  (irr-tree-zip)))
  :enable tree-zip-fix)

(defrule tree-zip-fix-when-not-tree-zip-p-cheap
  (implies (not (tree-zip-p zip))
           (equal (tree-zip-fix zip)
                  (irr-tree-zip)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by tree-zip-fix-when-not-tree-zip-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-equiv
  ((x tree-zip-p)
   (y tree-zip-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Equivalence up to @(tsee tree-zip-fix)."
  (equal (tree-zip-fix x)
         (tree-zip-fix y))
  :inline t

  ///

  (defequiv tree-zip-equiv))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-equiv)))

(defrule tree-zip-fix-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-fix zip0)
                  (tree-zip-fix zip1)))
  :rule-classes :congruence
  :enable tree-zip-equiv)

(defrule tree-zip-fix-under-tree-zip-equiv
  (tree-zip-equiv (tree-zip-fix zip)
                  zip)
  :enable tree-zip-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip->focus ((zip tree-zip-p))
  :returns (focus treep
                  :hints (("Goal" :in-theory (enable tree-zip-p
                                                     tree-zip-fix
                                                     irr-tree-zip))))
  :short "Get the subtree in focus."
  (car (tree-zip-fix zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip->focus-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip->focus zip0)
                  (tree-zip->focus zip1)))
  :rule-classes :congruence
  :enable (tree-zip->focus
           tree-zip-equiv))

;; A zipper is always at an element. This holds of any object, since the fixer
;; sends a non-zipper to one which is also at an element, so it discharges the
;; hypothesis on the constructor's type with nothing to backchain through.

(defrule not-tree-empty-p-of-tree-zip->focus
  (not (tree-empty-p (tree-zip->focus zip)))
  :enable (tree-zip->focus
           tree-zip-fix
           tree-zip-p
           irr-tree-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip->path ((zip tree-zip-p))
  :returns (path tree-zip-frame-listp
                 :hints (("Goal" :in-theory (enable tree-zip-p
                                                    tree-zip-fix
                                                    irr-tree-zip))))
  :short "Get the path from the root down to the focus."
  (cadr (tree-zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip->path-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip->path zip0)
                  (tree-zip->path zip1)))
  :rule-classes :congruence
  :enable (tree-zip->path
           tree-zip-equiv))

;; The frame-list compound recognizer cannot fire on a compound term, so the
;; iterated ascents, whose base case tests @(tsee endp) of a path, need this.

(defrule true-listp-of-tree-zip->path
  (true-listp (tree-zip->path zip))
  :rule-classes :type-prescription
  :enable true-listp-when-tree-zip-frame-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip->nlefts ((zip tree-zip-p))
  :returns (nlefts natp
                   :rule-classes :type-prescription
                   :hints (("Goal" :in-theory (enable tree-zip-p
                                                      tree-zip-fix
                                                      irr-tree-zip))))
  :short "Get the number of frames whose node follows the focus in order."
  (caddr (tree-zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip->nlefts-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip->nlefts zip0)
                  (tree-zip->nlefts zip1)))
  :rule-classes :congruence
  :enable (tree-zip->nlefts
           tree-zip-equiv))

;; The cached count always agrees with the path, even for ill-formed input,
;; since the fixer supplies the empty zipper. We normalize the cache away, so
;; that reasoning only ever sees the path.
(defrule tree-zip->nlefts-becomes-tree-zip-count-lefts
  (equal (tree-zip->nlefts zip)
         (tree-zip-count-lefts (tree-zip->path zip)))
  :enable (tree-zip->nlefts
           tree-zip->path
           tree-zip-fix
           tree-zip-p
           irr-tree-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip->nrights ((zip tree-zip-p))
  :returns (nrights natp
                    :rule-classes :type-prescription
                    :hints (("Goal" :in-theory (enable tree-zip-p
                                                       tree-zip-fix
                                                       irr-tree-zip))))
  :short "Get the number of frames whose node precedes the focus in order."
  (cdddr (tree-zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip->nrights-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip->nrights zip0)
                  (tree-zip->nrights zip1)))
  :rule-classes :congruence
  :enable (tree-zip->nrights
           tree-zip-equiv))

(defrule tree-zip->nrights-becomes-tree-zip-count-rights
  (equal (tree-zip->nrights zip)
         (tree-zip-count-rights (tree-zip->path zip)))
  :enable (tree-zip->nrights
           tree-zip->path
           tree-zip-fix
           tree-zip-p
           irr-tree-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip
  ((focus treep)
   (path tree-zip-frame-listp)
   (nlefts natp)
   (nrights natp))
  :guard (and (not (tree-empty-p focus))
              (equal nlefts (tree-zip-count-lefts path))
              (equal nrights (tree-zip-count-rights path)))
  :returns (zip tree-zip-p
                :hints (("Goal" :in-theory (enable tree-zip-p))))
  :short "Constructor for @(see zipper)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, the counts are ignored: they are determined by the path.
      Passing them in only avoids recomputing them, which is the whole point of
      caching them.")
   (xdoc::p
     "An empty focus is fixed away. The accessor rules need a nonempty focus
      either way, since an unfixed empty focus would not build a zipper and the
      accessors would fix it right back; fixing here at least keeps the type
      unconditional for every zipper-producing function downstream."))
  (let ((path (tree-zip-frame-list-fix path))
        (focus (mbe :logic (if (tree-empty-p focus)
                               (tree-node (irr-tree-element) nil nil)
                             (tree-fix focus))
                    :exec focus)))
    (cons focus
          (cons path
                (cons (mbe :logic (tree-zip-count-lefts path)
                           :exec nlefts)
                      (mbe :logic (tree-zip-count-rights path)
                           :exec nrights)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip)))

(defrule tree-zip-type-prescription
  (tree-zip-p (tree-zip focus path nlefts nrights))
  :rule-classes ((:type-prescription
                   :typed-term (tree-zip focus path nlefts nrights))))

(defrule tree-zip-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv focus0 focus1)
           (equal (tree-zip focus0 path nlefts nrights)
                  (tree-zip focus1 path nlefts nrights)))
  :rule-classes :congruence
  :enable tree-zip)

;; Logically, the counts are ignored. We choose to arbitrarily normalize them
;; to nil.
(defruled tree-zip-arg3-becomes-nil
  (equal (tree-zip focus path nlefts nrights)
         (tree-zip focus path nil nrights))
  :enable tree-zip)

(defrule tree-zip-when-arg3-not-nil-syntaxp
  (implies (syntaxp (not (equal nlefts ''nil)))
           (equal (tree-zip focus path nlefts nrights)
                  (tree-zip focus path nil nrights)))
  :by tree-zip-arg3-becomes-nil)

(defruled tree-zip-arg4-becomes-nil
  (equal (tree-zip focus path nlefts nrights)
         (tree-zip focus path nlefts nil))
  :enable tree-zip)

(defrule tree-zip-when-arg4-not-nil-syntaxp
  (implies (syntaxp (not (equal nrights ''nil)))
           (equal (tree-zip focus path nlefts nrights)
                  (tree-zip focus path nlefts nil)))
  :by tree-zip-arg4-becomes-nil)

(defrule tree-zip->focus-of-tree-zip
  (implies (not (tree-empty-p focus))
           (equal (tree-zip->focus (tree-zip focus path nlefts nrights))
                  (tree-fix focus)))
  :enable (tree-zip
           tree-zip->focus
           tree-zip-fix
           tree-zip-p))

(defrule tree-zip->path-of-tree-zip
  (equal (tree-zip->path (tree-zip focus path nlefts nrights))
         (tree-zip-frame-list-fix path))
  :enable (tree-zip
           tree-zip->path
           tree-zip-fix
           tree-zip-p))

;; These follow from the normalization of the cached counts into counts of the
;; path, so they need no help beyond the rule for the path itself.
(defrule tree-zip->nlefts-of-tree-zip
  (equal (tree-zip->nlefts (tree-zip focus path nlefts nrights))
         (tree-zip-count-lefts (tree-zip-frame-list-fix path))))

(defrule tree-zip->nrights-of-tree-zip
  (equal (tree-zip->nrights (tree-zip focus path nlefts nrights))
         (tree-zip-count-rights (tree-zip-frame-list-fix path))))

(defrule tree-zip-elim
  (implies (tree-zip-p zip)
           (equal (tree-zip (tree-zip->focus zip)
                            (tree-zip->path zip)
                            (tree-zip->nlefts zip)
                            (tree-zip->nrights zip))
                  zip))
  :rule-classes :elim
  :enable (tree-zip
           tree-zip->focus
           tree-zip->path
           tree-zip->nlefts
           tree-zip->nrights
           tree-zip-fix
           tree-zip-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-frame-plug
  ((frame tree-zip-frame-p)
   (tree treep))
  :returns (tree$ treep)
  :short "Rebuild the node of a frame, with the given tree in its hole."
  (if (tree-zip-frame->from-left frame)
      (tree-node (tree-zip-frame->elem frame)
                 tree
                 (tree-zip-frame->sibling frame))
    (tree-node (tree-zip-frame->elem frame)
               (tree-zip-frame->sibling frame)
               tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-frame-plug-when-tree-zip-frame-equiv-of-arg1-congruence
  (implies (tree-zip-frame-equiv frame0 frame1)
           (equal (tree-zip-frame-plug frame0 tree)
                  (tree-zip-frame-plug frame1 tree)))
  :rule-classes :congruence
  :enable tree-zip-frame-plug)

(defrule tree-zip-frame-plug-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-zip-frame-plug frame tree0)
                  (tree-zip-frame-plug frame tree1)))
  :rule-classes :congruence
  :enable tree-zip-frame-plug)

(defrule tree-empty-p-of-tree-zip-frame-plug
  (not (tree-empty-p (tree-zip-frame-plug frame tree)))
  :enable tree-zip-frame-plug)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-path-plug
  ((path tree-zip-frame-listp)
   (tree treep))
  :returns (tree$ treep)
  :short "Rebuild a tree by plugging it into a path, innermost frame first."
  (if (endp path)
      (tree-fix tree)
    (tree-zip-path-plug (cdr path)
                        (tree-zip-frame-plug (car path) tree))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-path-plug)))

(defrule tree-zip-path-plug-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (tree-zip-path-plug path tree0)
                  (tree-zip-path-plug path tree1)))
  :rule-classes :congruence
  :induct t
  :enable tree-zip-path-plug)

(defrule tree-zip-path-plug-when-not-consp-cheap
  (implies (not (consp path))
           (equal (tree-zip-path-plug path tree)
                  (tree-fix tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-zip-path-plug)

(defrule tree-zip-path-plug-of-cons
  (equal (tree-zip-path-plug (cons frame path) tree)
         (tree-zip-path-plug path (tree-zip-frame-plug frame tree)))
  :enable tree-zip-path-plug)

(defrule tree-empty-p-of-tree-zip-path-plug
  (equal (tree-empty-p (tree-zip-path-plug path tree))
         (and (not (consp path))
              (tree-empty-p tree)))
  :induct t
  :enable tree-zip-path-plug)

;; The tree recovered from a zipper carries the invariants of every subtree
;; along the way, so the focus inherits them with no zipper-local restatement
;; of the binary search tree or heap properties.

(defrule bstp-of-arg2-when-bstp-of-tree-zip-path-plug
  (implies (bstp (tree-zip-path-plug path tree))
           (bstp tree))
  :induct t
  :enable (tree-zip-path-plug
           tree-zip-frame-plug))

(defrule heapp-of-arg2-when-heapp-of-tree-zip-path-plug
  (implies (heapp (tree-zip-path-plug path tree))
           (heapp tree))
  :induct t
  :enable (tree-zip-path-plug
           tree-zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-plug ((zip tree-zip-p))
  :returns (tree treep)
  :short "Recover the whole tree from a zipper."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus."))
  (tree-zip-path-plug (tree-zip->path zip)
                      (tree-zip->focus zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-plug)))

(defrule tree-zip-plug-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-plug zip0)
                  (tree-zip-plug zip1)))
  :rule-classes :congruence
  :enable tree-zip-plug)

(defrule tree-zip-plug-of-tree-zip
  (implies (not (tree-empty-p focus))
           (equal (tree-zip-plug (tree-zip focus path nlefts nrights))
                  (tree-zip-path-plug (tree-zip-frame-list-fix path)
                                      (tree-fix focus))))
  :enable tree-zip-plug)

;; A zipper is at an element, so the tree it is a cursor into holds at least
;; that element.

(defrule not-tree-empty-p-of-tree-zip-plug
  (not (tree-empty-p (tree-zip-plug zip)))
  :enable tree-zip-plug)

(defrule tree-zip-plug-of-irr-tree-zip
  (equal (tree-zip-plug (irr-tree-zip))
         (tree-node (irr-tree-element) nil nil))
  :enable (tree-zip-plug
           irr-tree-zip
           tree-zip->path
           tree-zip->focus
           tree-zip-fix
           tree-zip-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rewrite forms of the elim rules, which as @(':elim') rules do not apply to
;; the compound terms the movement proofs produce. The frame case is split on
;; the flag, since the reconstructed frame carries a literal t or nil there.

(defrulel tree-node-of-tree->head-and-tree->left-and-tree->right
  (implies (not (tree-empty-p tree))
           (equal (tree-node (tree->head tree)
                             (tree->left tree)
                             (tree->right tree))
                  tree))
  :by tree-node-elim)

(defrulel tree-zip-of-tree-zip-accessors
  (equal (tree-zip (tree-zip->focus zip) (tree-zip->path zip) nil nil)
         (tree-zip-fix zip))
  :enable (tree-zip
           tree-zip->focus
           tree-zip->path
           tree-zip->nlefts
           tree-zip->nrights
           tree-zip-fix
           tree-zip-p
           irr-tree-zip))

(defrulel tree-zip-frame-of-t-and-accessors-when-from-left
  (implies (and (tree-zip-frame-p frame)
                (tree-zip-frame->from-left frame))
           (equal (tree-zip-frame t
                                  (tree-zip-frame->elem frame)
                                  (tree-zip-frame->sibling frame))
                  frame))
  :enable (tree-zip-frame
           tree-zip-frame->from-left
           tree-zip-frame->elem
           tree-zip-frame->sibling
           tree-zip-frame-fix
           tree-zip-frame-p))

(defrulel tree-zip-frame-of-nil-and-accessors-when-not-from-left
  (implies (and (tree-zip-frame-p frame)
                (not (tree-zip-frame->from-left frame)))
           (equal (tree-zip-frame nil
                                  (tree-zip-frame->elem frame)
                                  (tree-zip-frame->sibling frame))
                  frame))
  :enable (tree-zip-frame
           tree-zip-frame->from-left
           tree-zip-frame->elem
           tree-zip-frame->sibling
           tree-zip-frame-fix
           tree-zip-frame-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The single steps. Every other move iterates one of these, so that each move
;; is defined, and reasoned about, at the level of whole zippers rather than
;; their parts. Moving a zipper never changes the tree it is a cursor into,
;; which is what the plug rules below record.

(define tree-zip-descend-left ((zip tree-zip-p))
  :guard (not (tree-empty-p (tree->left (tree-zip->focus zip))))
  :returns (zip$ tree-zip-p)
  :short "Move the focus to the left child, pushing a frame."
  (let ((focus (tree-zip->focus zip)))
    (tree-zip (tree->left focus)
              (cons (tree-zip-frame t (tree->head focus) (tree->right focus))
                    (tree-zip->path zip))
              (+ 1 (tree-zip->nlefts zip))
              (tree-zip->nrights zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-descend-left)))
(defrule tree-zip-descend-left-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-descend-left zip0)
                  (tree-zip-descend-left zip1)))
  :rule-classes :congruence
  :enable tree-zip-descend-left)


(defrule tree-zip-plug-of-tree-zip-descend-left
  (implies (not (tree-empty-p (tree->left (tree-zip->focus zip))))
           (equal (tree-zip-plug (tree-zip-descend-left zip))
                  (tree-zip-plug zip)))
  :enable (tree-zip-descend-left
           tree-zip-plug
           tree-zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-descend-right ((zip tree-zip-p))
  :guard (not (tree-empty-p (tree->right (tree-zip->focus zip))))
  :returns (zip$ tree-zip-p)
  :short "Move the focus to the right child, pushing a frame."
  (let ((focus (tree-zip->focus zip)))
    (tree-zip (tree->right focus)
              (cons (tree-zip-frame nil (tree->head focus) (tree->left focus))
                    (tree-zip->path zip))
              (tree-zip->nlefts zip)
              (+ 1 (tree-zip->nrights zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-descend-right)))
(defrule tree-zip-descend-right-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-descend-right zip0)
                  (tree-zip-descend-right zip1)))
  :rule-classes :congruence
  :enable tree-zip-descend-right)


(defrule tree-zip-plug-of-tree-zip-descend-right
  (implies (not (tree-empty-p (tree->right (tree-zip->focus zip))))
           (equal (tree-zip-plug (tree-zip-descend-right zip))
                  (tree-zip-plug zip)))
  :enable (tree-zip-descend-right
           tree-zip-plug
           tree-zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What the single-step descents do to a zipper's parts. These come before
;; the iterated moves, whose measures are stated on the focus.

(defrule tree-zip->focus-of-tree-zip-descend-left
  (implies (not (tree-empty-p (tree->left (tree-zip->focus zip))))
           (equal (tree-zip->focus (tree-zip-descend-left zip))
                  (tree->left (tree-zip->focus zip))))
  :enable tree-zip-descend-left)

(defrule tree-zip->focus-of-tree-zip-descend-right
  (implies (not (tree-empty-p (tree->right (tree-zip->focus zip))))
           (equal (tree-zip->focus (tree-zip-descend-right zip))
                  (tree->right (tree-zip->focus zip))))
  :enable tree-zip-descend-right)

(defrule tree-zip->path-of-tree-zip-descend-left
  (equal (tree-zip->path (tree-zip-descend-left zip))
         (cons (tree-zip-frame t
                               (tree->head (tree-zip->focus zip))
                               (tree->right (tree-zip->focus zip)))
               (tree-zip->path zip)))
  :enable tree-zip-descend-left)

(defrule tree-zip->path-of-tree-zip-descend-right
  (equal (tree-zip->path (tree-zip-descend-right zip))
         (cons (tree-zip-frame nil
                               (tree->head (tree-zip->focus zip))
                               (tree->left (tree-zip->focus zip)))
               (tree-zip->path zip)))
  :enable tree-zip-descend-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-ascend-one ((zip tree-zip-p))
  :guard (consp (tree-zip->path zip))
  :returns (zip$ tree-zip-p)
  :short "Move the focus up to its parent, popping a frame."
  :long
  (xdoc::topstring
   (xdoc::p
     "The popped frame says which side the focus hung on, and so which of the
      two counts loses one."))
  (let ((frame (car (tree-zip->path zip))))
    (tree-zip (tree-zip-frame-plug frame (tree-zip->focus zip))
              (cdr (tree-zip->path zip))
              (if (tree-zip-frame->from-left frame)
                  (- (tree-zip->nlefts zip) 1)
                (tree-zip->nlefts zip))
              (if (tree-zip-frame->from-left frame)
                  (tree-zip->nrights zip)
                (- (tree-zip->nrights zip) 1))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-count-lefts
                                           tree-zip-count-rights))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-ascend-one)))
(defrule tree-zip-ascend-one-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-ascend-one zip0)
                  (tree-zip-ascend-one zip1)))
  :rule-classes :congruence
  :enable tree-zip-ascend-one)


(defrule tree-zip-plug-of-tree-zip-ascend-one
  (implies (consp (tree-zip->path zip))
           (equal (tree-zip-plug (tree-zip-ascend-one zip))
                  (tree-zip-plug zip)))
  :expand ((tree-zip-path-plug (tree-zip->path zip) (tree-zip->focus zip)))
  :enable (tree-zip-ascend-one
           tree-zip-plug))

(defrule tree-zip->path-of-tree-zip-ascend-one
  (implies (consp (tree-zip->path zip))
           (equal (tree-zip->path (tree-zip-ascend-one zip))
                  (cdr (tree-zip->path zip))))
  :enable tree-zip-ascend-one)

(defrule tree-zip->focus-of-tree-zip-ascend-one
  (implies (consp (tree-zip->path zip))
           (equal (tree-zip->focus (tree-zip-ascend-one zip))
                  (tree-zip-frame-plug (car (tree-zip->path zip))
                                       (tree-zip->focus zip))))
  :enable tree-zip-ascend-one)

;; A single-step ascent undoes a single-step descent. Every cancellation law
;; between the iterated moves comes back to one of these two.

(defrule tree-zip-ascend-one-of-tree-zip-descend-left
  (implies (not (tree-empty-p (tree->left (tree-zip->focus zip))))
           (equal (tree-zip-ascend-one (tree-zip-descend-left zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-ascend-one
           tree-zip-descend-left
           tree-zip-frame-plug))

(defrule tree-zip-ascend-one-of-tree-zip-descend-right
  (implies (not (tree-empty-p (tree->right (tree-zip->focus zip))))
           (equal (tree-zip-ascend-one (tree-zip-descend-right zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-ascend-one
           tree-zip-descend-right
           tree-zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-descend-leftmost ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Move the focus to the leftmost node within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended."))
  (if (tree-empty-p (tree->left (tree-zip->focus zip)))
      (tree-zip-fix zip)
    (tree-zip-descend-leftmost (tree-zip-descend-left zip)))
  :measure (acl2-count (tree-zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-descend-leftmost)))
(defrule tree-zip-descend-leftmost-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-descend-leftmost zip0)
                  (tree-zip-descend-leftmost zip1)))
  :rule-classes :congruence
  :expand ((tree-zip-descend-leftmost zip0)
           (tree-zip-descend-leftmost zip1))
  :enable tree-zip-descend-left)


(defrule tree-zip-plug-of-tree-zip-descend-leftmost
  (equal (tree-zip-plug (tree-zip-descend-leftmost zip))
         (tree-zip-plug zip))
  :induct t
  :enable tree-zip-descend-leftmost)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-descend-rightmost ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Move the focus to the rightmost node within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended."))
  (if (tree-empty-p (tree->right (tree-zip->focus zip)))
      (tree-zip-fix zip)
    (tree-zip-descend-rightmost (tree-zip-descend-right zip)))
  :measure (acl2-count (tree-zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-descend-rightmost)))
(defrule tree-zip-descend-rightmost-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-descend-rightmost zip0)
                  (tree-zip-descend-rightmost zip1)))
  :rule-classes :congruence
  :expand ((tree-zip-descend-rightmost zip0)
           (tree-zip-descend-rightmost zip1))
  :enable tree-zip-descend-right)


(defrule tree-zip-plug-of-tree-zip-descend-rightmost
  (equal (tree-zip-plug (tree-zip-descend-rightmost zip))
         (tree-zip-plug zip))
  :induct t
  :enable tree-zip-descend-rightmost)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-ascend-to-left-frame ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Move the focus up to the nearest ancestor that follows it."
  :long
  (xdoc::topstring
   (xdoc::p
     "That ancestor is the node of the nearest frame the focus hangs to the
      left of, and it is the in-order successor of everything below it on that
      side. When there is no such frame the focus has no successor above it,
      and we ascend all the way to the root.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth ascended."))
  (if (endp (tree-zip->path zip))
      (tree-zip-fix zip)
    (if (tree-zip-frame->from-left (car (tree-zip->path zip)))
        (tree-zip-ascend-one zip)
      (tree-zip-ascend-to-left-frame (tree-zip-ascend-one zip))))
  :measure (len (tree-zip->path zip))
  :guard-hints (("Goal" :in-theory (enable true-listp-when-tree-zip-frame-listp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-ascend-to-left-frame)))
(defrule tree-zip-ascend-to-left-frame-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-ascend-to-left-frame zip0)
                  (tree-zip-ascend-to-left-frame zip1)))
  :rule-classes :congruence
  :expand ((tree-zip-ascend-to-left-frame zip0)
           (tree-zip-ascend-to-left-frame zip1))
  :enable tree-zip-ascend-one)


(defrule tree-zip-plug-of-tree-zip-ascend-to-left-frame
  (equal (tree-zip-plug (tree-zip-ascend-to-left-frame zip))
         (tree-zip-plug zip))
  :induct t
  :enable tree-zip-ascend-to-left-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-ascend-to-right-frame ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Move the focus up to the nearest ancestor that precedes it."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee tree-zip-ascend-to-left-frame)."))
  (if (endp (tree-zip->path zip))
      (tree-zip-fix zip)
    (if (tree-zip-frame->from-left (car (tree-zip->path zip)))
        (tree-zip-ascend-to-right-frame (tree-zip-ascend-one zip))
      (tree-zip-ascend-one zip)))
  :measure (len (tree-zip->path zip))
  :guard-hints (("Goal" :in-theory (enable true-listp-when-tree-zip-frame-listp))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-ascend-to-right-frame)))
(defrule tree-zip-ascend-to-right-frame-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-ascend-to-right-frame zip0)
                  (tree-zip-ascend-to-right-frame zip1)))
  :rule-classes :congruence
  :expand ((tree-zip-ascend-to-right-frame zip0)
           (tree-zip-ascend-to-right-frame zip1))
  :enable tree-zip-ascend-one)


(defrule tree-zip-plug-of-tree-zip-ascend-to-right-frame
  (equal (tree-zip-plug (tree-zip-ascend-to-right-frame zip))
         (tree-zip-plug zip))
  :induct t
  :enable tree-zip-ascend-to-right-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The boundary checks. Each is constant time: the focus and the cached counts
;; are all immediately at hand. A zipper is at the first element exactly when
;; nothing lies to its left, which is to say its focus has no left child and no
;; ancestor precedes it.

(define tree-zip-at-first-p ((zip tree-zip-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is focused on the first element."
  (and (tree-empty-p (tree->left (tree-zip->focus zip)))
       (equal (tree-zip->nrights zip) 0))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-at-last-p ((zip tree-zip-p))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is focused on the last element."
  (and (tree-empty-p (tree->right (tree-zip->focus zip)))
       (equal (tree-zip->nlefts zip) 0))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-at-first-p)
                    (:t tree-zip-at-last-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-next ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Move the focus to the next element in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "When the focus has a right subtree, the successor is the leftmost node of
      it. Otherwise the successor is the nearest ancestor that follows the
      focus. At the last element there is neither, and the move saturates; the
      layer which supplies the two ends is the one that turns that into a
      position past the end.")
   (xdoc::p
     "Time complexity: @($O(d)$) in the worst case, but @($O(1)$) amortized
      over a traversal, since each edge of the tree is crossed twice."))
  (if (tree-zip-at-last-p zip)
      (tree-zip-fix zip)
    (if (tree-empty-p (tree->right (tree-zip->focus zip)))
        (tree-zip-ascend-to-left-frame zip)
      (tree-zip-descend-leftmost (tree-zip-descend-right zip))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-at-last-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-next)))

(defrule tree-zip-plug-of-tree-zip-next
  (equal (tree-zip-plug (tree-zip-next zip))
         (tree-zip-plug zip))
  :enable (tree-zip-next
           tree-zip-at-last-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-prev ((zip tree-zip-p))
  :returns (zip$ tree-zip-p)
  :short "Move the focus to the previous element in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee tree-zip-next)."))
  (if (tree-zip-at-first-p zip)
      (tree-zip-fix zip)
    (if (tree-empty-p (tree->left (tree-zip->focus zip)))
        (tree-zip-ascend-to-right-frame zip)
      (tree-zip-descend-rightmost (tree-zip-descend-left zip))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable tree-zip-at-first-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-prev)))

(defrule tree-zip-plug-of-tree-zip-prev
  (equal (tree-zip-plug (tree-zip-prev zip))
         (tree-zip-plug zip))
  :enable (tree-zip-prev
           tree-zip-at-first-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Where a descent lands, and what it leaves untouched.

(defrule tree-zip-descend-leftmost-when-tree-empty-p-of-left-of-focus
  (implies (tree-empty-p (tree->left (tree-zip->focus zip)))
           (equal (tree-zip-descend-leftmost zip)
                  (tree-zip-fix zip)))
  :enable tree-zip-descend-leftmost)

(defrule tree-zip-descend-rightmost-when-tree-empty-p-of-right-of-focus
  (implies (tree-empty-p (tree->right (tree-zip->focus zip)))
           (equal (tree-zip-descend-rightmost zip)
                  (tree-zip-fix zip)))
  :enable tree-zip-descend-rightmost)

(defrule tree-empty-p-of-tree->left-of-focus-of-tree-zip-descend-leftmost
  (tree-empty-p
    (tree->left (tree-zip->focus (tree-zip-descend-leftmost zip))))
  :induct t
  :enable tree-zip-descend-leftmost)

(defrule tree-empty-p-of-tree->right-of-focus-of-tree-zip-descend-rightmost
  (tree-empty-p
    (tree->right (tree-zip->focus (tree-zip-descend-rightmost zip))))
  :induct t
  :enable tree-zip-descend-rightmost)

;; A leftmost descent pushes only left frames, so it leaves the other count
;; alone, and vice versa.

(defrule tree-zip-count-rights-of-path-of-tree-zip-descend-leftmost
  (equal (tree-zip-count-rights
           (tree-zip->path (tree-zip-descend-leftmost zip)))
         (tree-zip-count-rights (tree-zip->path zip)))
  :induct t
  :enable tree-zip-descend-leftmost)

(defrule tree-zip-count-lefts-of-path-of-tree-zip-descend-rightmost
  (equal (tree-zip-count-lefts
           (tree-zip->path (tree-zip-descend-rightmost zip)))
         (tree-zip-count-lefts (tree-zip->path zip)))
  :induct t
  :enable tree-zip-descend-rightmost)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The boundaries: at either end the move saturates.

(defrule tree-zip-next-when-tree-zip-at-last-p
  (implies (tree-zip-at-last-p zip)
           (equal (tree-zip-next zip)
                  (tree-zip-fix zip)))
  :enable tree-zip-next)

(defrule tree-zip-prev-when-tree-zip-at-first-p
  (implies (tree-zip-at-first-p zip)
           (equal (tree-zip-prev zip)
                  (tree-zip-fix zip)))
  :enable tree-zip-prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A single-step descent and a single-step ascent are inverse. Both directions
;; are needed: the ascent cancels a descent just taken, and the descent
;; retraces an ascent whose frame hung on the matching side.

(defruledl tree-zip-descend-left-of-tree-zip-ascend-one-when-from-left
  (implies (and (consp (tree-zip->path zip))
                (tree-zip-frame->from-left (car (tree-zip->path zip))))
           (equal (tree-zip-descend-left (tree-zip-ascend-one zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-ascend-one
           tree-zip-descend-left
           tree-zip-frame-plug))

(defruledl tree-zip-descend-right-of-tree-zip-ascend-one-when-not-from-left
  (implies (and (consp (tree-zip->path zip))
                (not (tree-zip-frame->from-left (car (tree-zip->path zip)))))
           (equal (tree-zip-descend-right (tree-zip-ascend-one zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-ascend-one
           tree-zip-descend-right
           tree-zip-frame-plug))

;; Popping a frame the focus hung to the right of does not move the rightmost
;; node below, and symmetrically.

(defruledl tree-zip-descend-rightmost-of-tree-zip-ascend-one-when-not-from-left
  (implies (and (consp (tree-zip->path zip))
                (not (tree-zip-frame->from-left (car (tree-zip->path zip)))))
           (equal (tree-zip-descend-rightmost (tree-zip-ascend-one zip))
                  (tree-zip-descend-rightmost zip)))
  :expand ((tree-zip-descend-rightmost (tree-zip-ascend-one zip)))
  :enable (tree-zip-frame-plug
           tree-zip-descend-right-of-tree-zip-ascend-one-when-not-from-left))

(defruledl tree-zip-descend-leftmost-of-tree-zip-ascend-one-when-from-left
  (implies (and (consp (tree-zip->path zip))
                (tree-zip-frame->from-left (car (tree-zip->path zip))))
           (equal (tree-zip-descend-leftmost (tree-zip-ascend-one zip))
                  (tree-zip-descend-leftmost zip)))
  :expand ((tree-zip-descend-leftmost (tree-zip-ascend-one zip)))
  :enable (tree-zip-frame-plug
           tree-zip-descend-left-of-tree-zip-ascend-one-when-from-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Descending and then ascending past what was pushed cancels out: a leftmost
;; descent pushes only left frames, and an ascent to a right frame pops left
;; frames on its way, so the descent leaves no trace.

(defruledl tree-zip-ascend-to-right-frame-of-tree-zip-descend-leftmost
  (equal (tree-zip-ascend-to-right-frame (tree-zip-descend-leftmost zip))
         (tree-zip-ascend-to-right-frame zip))
  :induct (tree-zip-descend-leftmost zip)
  :enable (tree-zip-descend-leftmost
           tree-zip-ascend-to-right-frame))

(defruledl tree-zip-ascend-to-left-frame-of-tree-zip-descend-rightmost
  (equal (tree-zip-ascend-to-left-frame (tree-zip-descend-rightmost zip))
         (tree-zip-ascend-to-left-frame zip))
  :induct (tree-zip-descend-rightmost zip)
  :enable (tree-zip-descend-rightmost
           tree-zip-ascend-to-left-frame))

;; A single-step descent is undone by the matching searching ascent, since the
;; frame it just pushed is the very frame that ascent stops at.

(defruledl tree-zip-ascend-to-right-frame-of-tree-zip-descend-right
  (implies (not (tree-empty-p (tree->right (tree-zip->focus zip))))
           (equal (tree-zip-ascend-to-right-frame (tree-zip-descend-right zip))
                  (tree-zip-fix zip)))
  :enable tree-zip-ascend-to-right-frame)

(defruledl tree-zip-ascend-to-left-frame-of-tree-zip-descend-left
  (implies (not (tree-empty-p (tree->left (tree-zip->focus zip))))
           (equal (tree-zip-ascend-to-left-frame (tree-zip-descend-left zip))
                  (tree-zip-fix zip)))
  :enable tree-zip-ascend-to-left-frame)

;; And in the other direction: ascending to a frame and then descending back
;; down lands where a descent from the original position would have.

(defruledl tree-zip-descend-rightmost-of-descend-left-of-ascend-to-left-frame
  (implies (not (equal (tree-zip-count-lefts (tree-zip->path zip)) 0))
           (equal (tree-zip-descend-rightmost
                    (tree-zip-descend-left (tree-zip-ascend-to-left-frame zip)))
                  (tree-zip-descend-rightmost zip)))
  :induct (tree-zip-ascend-to-left-frame zip)
  :enable (tree-zip-ascend-to-left-frame
           tree-zip-count-lefts
           tree-zip-descend-left-of-tree-zip-ascend-one-when-from-left
           tree-zip-descend-rightmost-of-tree-zip-ascend-one-when-not-from-left))

(defruledl tree-zip-descend-leftmost-of-descend-right-of-ascend-to-right-frame
  (implies (not (equal (tree-zip-count-rights (tree-zip->path zip)) 0))
           (equal (tree-zip-descend-leftmost
                    (tree-zip-descend-right (tree-zip-ascend-to-right-frame zip)))
                  (tree-zip-descend-leftmost zip)))
  :induct (tree-zip-ascend-to-right-frame zip)
  :enable (tree-zip-ascend-to-right-frame
           tree-zip-count-rights
           tree-zip-descend-right-of-tree-zip-ascend-one-when-not-from-left
           tree-zip-descend-leftmost-of-tree-zip-ascend-one-when-from-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An ascent that finds its frame lands on a node with a child on the side it
;; came from, which is what lets the reverse move descend back.

(defruledl not-tree-empty-p-of-left-of-focus-of-ascend-to-left-frame
  (implies (not (equal (tree-zip-count-lefts (tree-zip->path zip)) 0))
           (not (tree-empty-p
                  (tree->left
                    (tree-zip->focus (tree-zip-ascend-to-left-frame zip))))))
  :induct (tree-zip-ascend-to-left-frame zip)
  :enable (tree-zip-ascend-to-left-frame
           tree-zip-count-lefts
           tree-zip-frame-plug))

(defruledl not-tree-empty-p-of-right-of-focus-of-ascend-to-right-frame
  (implies (not (equal (tree-zip-count-rights (tree-zip->path zip)) 0))
           (not (tree-empty-p
                  (tree->right
                    (tree-zip->focus (tree-zip-ascend-to-right-frame zip))))))
  :induct (tree-zip-ascend-to-right-frame zip)
  :enable (tree-zip-ascend-to-right-frame
           tree-zip-count-rights
           tree-zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two moves are inverse everywhere they have somewhere to go. This is
;; where uniqueness earns its keep: the recovered zipper is not merely
;; equivalent to the original, it is @(tsee equal) to it. Since every zipper is
;; at an element, the only exclusions are the two ends, where the move
;; saturates and has nothing to invert.

(defrule tree-zip-prev-of-tree-zip-next
  (implies (not (tree-zip-at-last-p zip))
           (equal (tree-zip-prev (tree-zip-next zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-next
           tree-zip-prev
           tree-zip-at-last-p
           tree-zip-at-first-p
           tree-zip-descend-rightmost-of-descend-left-of-ascend-to-left-frame
           tree-zip-ascend-to-right-frame-of-tree-zip-descend-leftmost
           tree-zip-ascend-to-right-frame-of-tree-zip-descend-right
           not-tree-empty-p-of-left-of-focus-of-ascend-to-left-frame))

(defrule tree-zip-next-of-tree-zip-prev
  (implies (not (tree-zip-at-first-p zip))
           (equal (tree-zip-next (tree-zip-prev zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-next
           tree-zip-prev
           tree-zip-at-last-p
           tree-zip-at-first-p
           tree-zip-descend-leftmost-of-descend-right-of-ascend-to-right-frame
           tree-zip-ascend-to-left-frame-of-tree-zip-descend-rightmost
           tree-zip-ascend-to-left-frame-of-tree-zip-descend-left
           not-tree-empty-p-of-right-of-focus-of-ascend-to-right-frame))

;; A move leaves something behind it, so it cannot land at the far end it came
;; from. The two branches argue differently: a descent pushes a right frame, so
;; the count of those is nonzero afterwards; an ascent lands on a node whose
;; child on the side it came from is nonempty. A layer supplying the two ends
;; needs this to know that stepping inward never overshoots.

(defrule not-tree-zip-at-first-p-of-tree-zip-next
  (implies (not (tree-zip-at-last-p zip))
           (not (tree-zip-at-first-p (tree-zip-next zip))))
  :enable (tree-zip-next
           tree-zip-at-last-p
           tree-zip-at-first-p
           not-tree-empty-p-of-left-of-focus-of-ascend-to-left-frame))

(defrule not-tree-zip-at-last-p-of-tree-zip-prev
  (implies (not (tree-zip-at-first-p zip))
           (not (tree-zip-at-last-p (tree-zip-prev zip))))
  :enable (tree-zip-prev
           tree-zip-at-last-p
           tree-zip-at-first-p
           not-tree-empty-p-of-right-of-focus-of-ascend-to-right-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What the single-step moves do to a zipper's parts. The path rules are the
;; useful ones: the counts follow from them, and unlike rules about the cached
;; counts they survive the normalization of those counts into counts of a path.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-root ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (zip tree-zip-p)
  :short "The zipper focused on a whole tree, with an empty path."
  (tree-zip tree nil 0 0)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-root)))

(defrule tree-zip-plug-of-tree-zip-root
  (implies (not (tree-empty-p tree))
           (equal (tree-zip-plug (tree-zip-root tree))
                  (tree-fix tree)))
  :enable tree-zip-root)

(defrule tree-zip->focus-of-tree-zip-root
  (implies (not (tree-empty-p tree))
           (equal (tree-zip->focus (tree-zip-root tree))
                  (tree-fix tree)))
  :enable tree-zip-root)

(defrule tree-zip->path-of-tree-zip-root
  (equal (tree-zip->path (tree-zip-root tree))
         nil)
  :enable tree-zip-root)

(defrule tree-zip->nlefts-of-tree-zip-root
  (equal (tree-zip->nlefts (tree-zip-root tree))
         0)
  :enable tree-zip-root)

(defrule tree-zip->nrights-of-tree-zip-root
  (equal (tree-zip->nrights (tree-zip-root tree))
         0)
  :enable tree-zip-root)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-first ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (zip tree-zip-p)
  :short "The zipper focused on the first element of a tree."
  (tree-zip-descend-leftmost (tree-zip-root tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-last ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (zip tree-zip-p)
  :short "The zipper focused on the last element of a tree."
  (tree-zip-descend-rightmost (tree-zip-root tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-first) (:t tree-zip-last)))

(defrule tree-zip-plug-of-tree-zip-first
  (implies (not (tree-empty-p tree))
           (equal (tree-zip-plug (tree-zip-first tree))
                  (tree-fix tree)))
  :enable tree-zip-first)

(defrule tree-zip-plug-of-tree-zip-last
  (implies (not (tree-empty-p tree))
           (equal (tree-zip-plug (tree-zip-last tree))
                  (tree-fix tree)))
  :enable tree-zip-last)

(defrule tree-zip-at-first-p-of-tree-zip-first
  (implies (not (tree-empty-p tree))
           (tree-zip-at-first-p (tree-zip-first tree)))
  :enable (tree-zip-first
           tree-zip-at-first-p))

(defrule tree-zip-at-last-p-of-tree-zip-last
  (implies (not (tree-empty-p tree))
           (tree-zip-at-last-p (tree-zip-last tree)))
  :enable (tree-zip-last
           tree-zip-at-last-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two ends of a tree are unique: a zipper at the last element is the very
;; zipper @(tsee tree-zip-last) builds, and likewise at the first. A layer
;; supplying the ends needs this to step back inward and land where it started.
;;
;; The argument is that when nothing above the focus follows it, ascending in
;; search of a left frame never finds one and so climbs to the root, and that
;; climb does not move the rightmost node below.

(defrulel tree-zip->path-when-not-consp
  (implies (not (consp (tree-zip->path zip)))
           (equal (tree-zip->path zip)
                  nil))
  :use (:instance true-listp-of-tree-zip->path))

(defrulel tree-zip-of-focus-and-nil-when-path-not-consp
  (implies (not (consp (tree-zip->path zip)))
           (equal (tree-zip (tree-zip->focus zip) nil nil nil)
                  (tree-zip-fix zip)))
  :use tree-zip-of-tree-zip-accessors
  :disable tree-zip-of-tree-zip-accessors)

(defruledl tree-zip-ascend-to-left-frame-when-no-left-frames
  (implies (equal (tree-zip-count-lefts (tree-zip->path zip)) 0)
           (equal (tree-zip-ascend-to-left-frame zip)
                  (tree-zip-root (tree-zip-plug zip))))
  :induct (tree-zip-ascend-to-left-frame zip)
  :expand ((tree-zip-count-lefts (tree-zip->path zip)))
  :enable (tree-zip-ascend-to-left-frame
           tree-zip-root
           tree-zip-plug))

(defruledl tree-zip-ascend-to-right-frame-when-no-right-frames
  (implies (equal (tree-zip-count-rights (tree-zip->path zip)) 0)
           (equal (tree-zip-ascend-to-right-frame zip)
                  (tree-zip-root (tree-zip-plug zip))))
  :induct (tree-zip-ascend-to-right-frame zip)
  :expand ((tree-zip-count-rights (tree-zip->path zip)))
  :enable (tree-zip-ascend-to-right-frame
           tree-zip-root
           tree-zip-plug))

(defruledl tree-zip-descend-rightmost-of-ascend-to-left-frame-when-no-left-frames
  (implies (equal (tree-zip-count-lefts (tree-zip->path zip)) 0)
           (equal (tree-zip-descend-rightmost (tree-zip-ascend-to-left-frame zip))
                  (tree-zip-descend-rightmost zip)))
  :induct (tree-zip-ascend-to-left-frame zip)
  :expand ((tree-zip-count-lefts (tree-zip->path zip)))
  :enable (tree-zip-ascend-to-left-frame
           tree-zip-descend-rightmost-of-tree-zip-ascend-one-when-not-from-left))

(defruledl tree-zip-descend-leftmost-of-ascend-to-right-frame-when-no-right-frames
  (implies (equal (tree-zip-count-rights (tree-zip->path zip)) 0)
           (equal (tree-zip-descend-leftmost (tree-zip-ascend-to-right-frame zip))
                  (tree-zip-descend-leftmost zip)))
  :induct (tree-zip-ascend-to-right-frame zip)
  :expand ((tree-zip-count-rights (tree-zip->path zip)))
  :enable (tree-zip-ascend-to-right-frame
           tree-zip-descend-leftmost-of-tree-zip-ascend-one-when-from-left))

(defrule tree-zip-last-of-tree-zip-plug-when-tree-zip-at-last-p
  (implies (tree-zip-at-last-p zip)
           (equal (tree-zip-last (tree-zip-plug zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-last
           tree-zip-at-last-p)
  :use (tree-zip-ascend-to-left-frame-when-no-left-frames
        tree-zip-descend-rightmost-of-ascend-to-left-frame-when-no-left-frames))

(defrule tree-zip-first-of-tree-zip-plug-when-tree-zip-at-first-p
  (implies (tree-zip-at-first-p zip)
           (equal (tree-zip-first (tree-zip-plug zip))
                  (tree-zip-fix zip)))
  :enable (tree-zip-first
           tree-zip-at-first-p)
  :use (tree-zip-ascend-to-right-frame-when-no-right-frames
        tree-zip-descend-leftmost-of-ascend-to-right-frame-when-no-right-frames))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-value ((zip tree-zip-p))
  :short "The value at the focus."
  (tree-element->val (tree->head (tree-zip->focus zip)))
  :inline t)

;; The focus of a zipper occupies a contiguous run of the in-order sequence of
;; the whole tree, and what flanks that run is fixed by the path alone. The two
;; functions below name those flanks, cutting the sequence in three.

(define tree-zip-path-before ((path tree-zip-frame-listp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which precede the focus subtree, in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "A frame contributes its node and its sibling subtree exactly when the
      focus lies in the right child, since only then does that node precede the
      focus. Frames further out contribute further to the left."))
  (if (endp path)
      nil
    (append (tree-zip-path-before (cdr path))
            (if (tree-zip-frame->from-left (car path))
                nil
              (append (tree-in-order (tree-zip-frame->sibling (car path)))
                      (list (tree-element->val
                              (tree-zip-frame->elem (car path)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-path-after ((path tree-zip-frame-listp))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which follow the focus subtree, in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror of @(tsee tree-zip-path-before): a frame contributes exactly
      when the focus lies in the left child."))
  (if (endp path)
      nil
    (append (if (tree-zip-frame->from-left (car path))
                (cons (tree-element->val (tree-zip-frame->elem (car path)))
                      (tree-in-order (tree-zip-frame->sibling (car path))))
              nil)
            (tree-zip-path-after (cdr path)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-path-before) (:t tree-zip-path-after)))

(defrule tree-zip-path-before-when-not-consp-cheap
  (implies (not (consp path))
           (equal (tree-zip-path-before path)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-zip-path-before)

(defrule tree-zip-path-after-when-not-consp-cheap
  (implies (not (consp path))
           (equal (tree-zip-path-after path)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable tree-zip-path-after)

(defrule tree-zip-path-before-of-cons
  (equal (tree-zip-path-before (cons frame path))
         (append (tree-zip-path-before path)
                 (if (tree-zip-frame->from-left frame)
                     nil
                   (append (tree-in-order (tree-zip-frame->sibling frame))
                           (list (tree-element->val
                                   (tree-zip-frame->elem frame)))))))
  :enable tree-zip-path-before)

(defrule tree-zip-path-after-of-cons
  (equal (tree-zip-path-after (cons frame path))
         (append (if (tree-zip-frame->from-left frame)
                     (cons (tree-element->val (tree-zip-frame->elem frame))
                           (tree-in-order (tree-zip-frame->sibling frame)))
                   nil)
                 (tree-zip-path-after path)))
  :enable tree-zip-path-after)

;; A path with no left frames has nothing to the right of the focus, and
;; symmetrically. This is what the cached counts are testing.

(defrule tree-zip-path-after-when-tree-zip-count-lefts-zero
  (implies (equal (tree-zip-count-lefts path) 0)
           (equal (tree-zip-path-after path)
                  nil))
  :induct t
  :enable (tree-zip-path-after
           tree-zip-count-lefts))

(defrule tree-zip-path-before-when-tree-zip-count-rights-zero
  (implies (equal (tree-zip-count-rights path) 0)
           (equal (tree-zip-path-before path)
                  nil))
  :induct t
  :enable (tree-zip-path-before
           tree-zip-count-rights))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-order-of-tree-zip-path-plug
  (equal (tree-in-order (tree-zip-path-plug path tree))
         (append (tree-zip-path-before path)
                 (tree-in-order tree)
                 (tree-zip-path-after path)))
  :induct (tree-zip-path-plug path tree)
  :enable (tree-zip-path-plug
           tree-zip-path-before
           tree-zip-path-after
           tree-zip-frame-plug
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The path accounts for everything outside the focus subtree. Within it, the
;; focus's own left subtree precedes the cursor and its right subtree follows,
;; so the two combine to split the sequence at the cursor rather than at the
;; subtree. When the focus is empty only the path contributes.

(define tree-zip-before ((zip tree-zip-p))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which precede the cursor, in order."
  (append (tree-zip-path-before (tree-zip->path zip))
          (tree-in-order (tree->left (tree-zip->focus zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-zip-after ((zip tree-zip-p))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which follow the cursor, in order."
  (append (tree-in-order (tree->right (tree-zip->focus zip)))
          (tree-zip-path-after (tree-zip->path zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t tree-zip-before) (:t tree-zip-after)))

(defrule tree-zip-before-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-before zip0)
                  (tree-zip-before zip1)))
  :rule-classes :congruence
  :enable tree-zip-before)

(defrule tree-zip-after-when-tree-zip-equiv-congruence
  (implies (tree-zip-equiv zip0 zip1)
           (equal (tree-zip-after zip0)
                  (tree-zip-after zip1)))
  :rule-classes :congruence
  :enable tree-zip-after)

;;;;;;;;;;;;;;;;;;;;

;; The in-order sequence of the whole tree, cut at the focus subtree. This is
;; the form which rewrites unconditionally, and every law below is read off of
;; it.

(defrule tree-in-order-of-tree-zip-plug
  (equal (tree-in-order (tree-zip-plug zip))
         (append (tree-zip-path-before (tree-zip->path zip))
                 (tree-in-order (tree-zip->focus zip))
                 (tree-zip-path-after (tree-zip->path zip))))
  :enable tree-zip-plug)

;; The same sequence, cut at the cursor instead: since a zipper is always at an
;; element, the cut always splits the sequence around one value.

(defruled tree-in-order-of-tree-zip-plug-split-at-cursor
  (equal (tree-in-order (tree-zip-plug zip))
         (append (tree-zip-before zip)
                 (cons (tree-zip-value zip)
                       (tree-zip-after zip))))
  :enable (tree-zip-before
           tree-zip-after
           tree-zip-value
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;

;; Cardinality, read off of the same two decompositions by taking lengths.

(defrule tree-nodes-count-of-tree-zip-plug
  (equal (tree-nodes-count (tree-zip-plug zip))
         (+ (len (tree-zip-path-before (tree-zip->path zip)))
            (tree-nodes-count (tree-zip->focus zip))
            (len (tree-zip-path-after (tree-zip->path zip)))))
  :use ((:instance len-of-tree-in-order (tree (tree-zip-plug zip)))
        (:instance len-of-tree-in-order (tree (tree-zip->focus zip))))
  :disable len-of-tree-in-order)

(defruled tree-nodes-count-of-tree-zip-plug-split-at-cursor
  (equal (tree-nodes-count (tree-zip-plug zip))
         (+ (len (tree-zip-before zip))
            1
            (len (tree-zip-after zip))))
  :use (:instance len-of-tree-in-order (tree (tree-zip-plug zip)))
  :enable tree-in-order-of-tree-zip-plug-split-at-cursor
  :disable len-of-tree-in-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The iteration is in order: a step moves exactly one value across the cut,
;; from the front of what follows to the back of what precedes. Everything
;; about position is a consequence of this, which is why no separate index is
;; needed to say that a traversal proceeds in order.
;;
;; The two branches of the move argue differently. A descent to the right and
;; then leftmost lands where the path alone decides, and the frame that descent
;; pushed contributes the focus's left subtree and its value. An ascent instead
;; preserves everything before or within the focus subtree, all the way up to
;; the frame it stops at.

(defruledl tree-zip-before-of-tree-zip-descend-leftmost
  (equal (tree-zip-before (tree-zip-descend-leftmost zip))
         (tree-zip-path-before (tree-zip->path zip)))
  :induct (tree-zip-descend-leftmost zip)
  :enable (tree-zip-descend-leftmost
           tree-zip-before))

(defruledl tree-zip-path-before-of-path-of-tree-zip-descend-right
  (equal (tree-zip-path-before (tree-zip->path (tree-zip-descend-right zip)))
         (append (tree-zip-before zip)
                 (list (tree-zip-value zip))))
  :enable (tree-zip-before
           tree-zip-value))

(defruledl tree-zip-before-of-tree-zip-ascend-to-left-frame
  (implies (not (equal (tree-zip-count-lefts (tree-zip->path zip)) 0))
           (equal (tree-zip-before (tree-zip-ascend-to-left-frame zip))
                  (append (tree-zip-path-before (tree-zip->path zip))
                          (tree-in-order (tree-zip->focus zip)))))
  :induct (tree-zip-ascend-to-left-frame zip)
  :expand ((tree-zip-count-lefts (tree-zip->path zip))
           (tree-zip-path-before (tree-zip->path zip)))
  :enable (tree-zip-ascend-to-left-frame
           tree-zip-ascend-one
           tree-zip-before
           tree-zip-frame-plug
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-zip-before-of-tree-zip-next
  (implies (not (tree-zip-at-last-p zip))
           (equal (tree-zip-before (tree-zip-next zip))
                  (append (tree-zip-before zip)
                          (list (tree-zip-value zip)))))
  :expand ((tree-in-order (tree-zip->focus zip)))
  :enable (tree-zip-next
           tree-zip-at-last-p
           tree-zip-before
           tree-zip-value
           tree-zip-before-of-tree-zip-descend-leftmost
           tree-zip-path-before-of-path-of-tree-zip-descend-right
           tree-zip-before-of-tree-zip-ascend-to-left-frame))

;; What follows the cursor loses its first value, which is the one the move
;; lands on. Both fall out of the law above by cancelling the common prefix in
;; the two decompositions.

(defrule tree-zip-after-of-tree-zip-next
  (implies (not (tree-zip-at-last-p zip))
           (equal (tree-zip-after (tree-zip-next zip))
                  (cdr (tree-zip-after zip))))
  :use ((:instance tree-in-order-of-tree-zip-plug-split-at-cursor)
        (:instance tree-in-order-of-tree-zip-plug-split-at-cursor
                   (zip (tree-zip-next zip))))
  :enable tree-zip-before-of-tree-zip-next)

(defrule tree-zip-value-of-tree-zip-next
  (implies (not (tree-zip-at-last-p zip))
           (equal (tree-zip-value (tree-zip-next zip))
                  (car (tree-zip-after zip))))
  :use ((:instance tree-in-order-of-tree-zip-plug-split-at-cursor)
        (:instance tree-in-order-of-tree-zip-plug-split-at-cursor
                   (zip (tree-zip-next zip))))
  :enable tree-zip-before-of-tree-zip-next)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Having nothing before you is being at the first element, and having nothing
;; after you is being at the last. A frame the focus hangs to the right of
;; contributes at least its own node, so a path which contributes nothing has
;; no such frame.

(defruledl tree-zip-count-rights-when-not-consp-of-tree-zip-path-before
  (implies (not (consp (tree-zip-path-before path)))
           (equal (tree-zip-count-rights path) 0))
  :induct t
  :enable (tree-zip-path-before
           tree-zip-count-rights))

(defruledl tree-zip-count-lefts-when-not-consp-of-tree-zip-path-after
  (implies (not (consp (tree-zip-path-after path)))
           (equal (tree-zip-count-lefts path) 0))
  :induct t
  :enable (tree-zip-path-after
           tree-zip-count-lefts))

(defrule tree-zip-before-when-tree-zip-at-first-p
  (implies (tree-zip-at-first-p zip)
           (equal (tree-zip-before zip)
                  nil))
  :enable (tree-zip-at-first-p
           tree-zip-before))

(defrule tree-zip-after-when-tree-zip-at-last-p
  (implies (tree-zip-at-last-p zip)
           (equal (tree-zip-after zip)
                  nil))
  :enable (tree-zip-at-last-p
           tree-zip-after))

(defrule tree-zip-at-first-p-when-not-consp-of-tree-zip-before
  (implies (not (consp (tree-zip-before zip)))
           (tree-zip-at-first-p zip))
  :enable (tree-zip-at-first-p
           tree-zip-before
           tree-zip-count-rights-when-not-consp-of-tree-zip-path-before))

(defrule tree-zip-at-last-p-when-not-consp-of-tree-zip-after
  (implies (not (consp (tree-zip-after zip)))
           (tree-zip-at-last-p zip))
  :enable (tree-zip-at-last-p
           tree-zip-after
           tree-zip-count-lefts-when-not-consp-of-tree-zip-path-after))

(defrule not-tree-zip-at-first-p-when-consp-of-tree-zip-before
  (implies (consp (tree-zip-before zip))
           (not (tree-zip-at-first-p zip)))
  :use tree-zip-before-when-tree-zip-at-first-p
  :disable tree-zip-before-when-tree-zip-at-first-p)

(defrule not-tree-zip-at-last-p-when-consp-of-tree-zip-after
  (implies (consp (tree-zip-after zip))
           (not (tree-zip-at-last-p zip)))
  :use tree-zip-after-when-tree-zip-at-last-p
  :disable tree-zip-after-when-tree-zip-at-last-p)

;; The two ends as tests on the sequences alone. Left disabled, since either
;; direction on its own is the cheaper rule; this form is for proofs which know
;; two zippers have the same sequence and need them to be at an end together.

(defruled tree-zip-at-first-p-becomes-not-consp-of-tree-zip-before
  (equal (tree-zip-at-first-p zip)
         (not (consp (tree-zip-before zip))))
  :cases ((consp (tree-zip-before zip))))

(defruled tree-zip-at-last-p-becomes-not-consp-of-tree-zip-after
  (equal (tree-zip-at-last-p zip)
         (not (consp (tree-zip-after zip))))
  :cases ((consp (tree-zip-after zip))))

;; The mirror of the ordering law, read backwards.

(defrule tree-zip-before-of-tree-zip-prev
  (implies (not (tree-zip-at-first-p zip))
           (equal (tree-zip-before zip)
                  (append (tree-zip-before (tree-zip-prev zip))
                          (list (tree-zip-value (tree-zip-prev zip))))))
  :use (:instance tree-zip-before-of-tree-zip-next
                  (zip (tree-zip-prev zip)))
  :disable tree-zip-before-of-tree-zip-next)

;;;;;;;;;;;;;;;;;;;;

;; UNIQUENESS. A zipper is determined by the tree it is a cursor into together
;; with what follows the cursor in that tree. Note that no @(tsee bstp)
;; hypothesis is needed: this is structural, and holds of any tree.
;;
;; The proof walks both zippers forward in step. Each step drops one value from
;; what follows, so the two stay in agreement, and the walk ends at the last
;; element, where @(tsee tree-zip-last) already pins the zipper down. Undoing
;; the walk with @(tsee tree-zip-prev) carries the equality back to the start.

(local
 (defun tree-zip-position-induction (zip1 zip2)
   (declare (xargs :measure (len (tree-zip-after zip1))))
   (if (tree-zip-at-last-p zip1)
       (list zip1 zip2)
     (tree-zip-position-induction (tree-zip-next zip1)
                                  (tree-zip-next zip2)))))

(defthm tree-zip-uniqueness-when-tree-zip-after-equal
  (implies (and (equal (tree-zip-plug zip1) (tree-zip-plug zip2))
                (equal (tree-zip-after zip1) (tree-zip-after zip2)))
           (equal (tree-zip-fix zip1) (tree-zip-fix zip2)))
  :rule-classes nil
  :hints (("Goal" :induct (tree-zip-position-induction zip1 zip2))
          ("Subgoal *1/2"
           :use ((:instance tree-zip-after-of-tree-zip-next (zip zip2))
                 (:instance tree-zip-prev-of-tree-zip-next (zip zip1))
                 (:instance tree-zip-prev-of-tree-zip-next (zip zip2))))
          ("Subgoal *1/1"
           :use ((:instance tree-zip-last-of-tree-zip-plug-when-tree-zip-at-last-p
                            (zip zip1))
                 (:instance tree-zip-last-of-tree-zip-plug-when-tree-zip-at-last-p
                            (zip zip2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A move is the identity exactly at the end it saturates against, and nowhere
;; else. This is what says a traversal makes progress: reaching a fixed point
;; means being done, rather than merely being stuck.
;;
;; It reads straight off the ordering laws. If a step left the zipper alone it
;; would leave what follows the cursor alone too, but a step drops one value
;; from that, and no list is its own @(tsee cdr).

(defruledl not-equal-of-cdr-when-consp
  (implies (consp x)
           (not (equal x (cdr x))))
  :use (:instance acl2::len-of-cdr (acl2::x x))
  :disable acl2::len-of-cdr)

(defruledl not-equal-of-append-of-singleton
  (not (equal x (append x (list y))))
  :use (:instance acl2::len-of-append (acl2::x x) (acl2::y (list y)))
  :disable acl2::len-of-append)

(defrule tree-zip-next-identity-iff-tree-zip-at-last-p
  (equal (equal (tree-zip-next zip) (tree-zip-fix zip))
         (tree-zip-at-last-p zip))
  :use (:instance tree-zip-after-of-tree-zip-next)
  :disable tree-zip-after-of-tree-zip-next
  :cases ((consp (tree-zip-after zip)))
  :enable not-equal-of-cdr-when-consp)

(defrule tree-zip-prev-identity-iff-tree-zip-at-first-p
  (equal (equal (tree-zip-prev zip) (tree-zip-fix zip))
         (tree-zip-at-first-p zip))
  :use (:instance tree-zip-before-of-tree-zip-prev)
  :disable tree-zip-before-of-tree-zip-prev
  :cases ((consp (tree-zip-before zip)))
  :enable not-equal-of-append-of-singleton)
