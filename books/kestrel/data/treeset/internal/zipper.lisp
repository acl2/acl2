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
(include-book "in-defs")
(include-book "in-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/utilities/oset" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "tree"))
(local (include-book "bst"))
(local (include-book "heap"))
(local (include-book "count"))
(local (include-book "in"))
(local (include-book "in-order"))
(local (include-book "subset"))

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
      "The focus is never empty, so a zipper is always at an element: a tree
       with @($n$) nodes has exactly @($n$) zippers, and the empty tree has
       none. The positions before the first element and after the last are not
       zippers; they are supplied by @(see tree-iterator).")
    (xdoc::p
      "Costs below are given as @($O(d)$), where @($d$) is a depth within the
       tree. That is the honest bound here, since a zipper is over an arbitrary
       @(see tree) and nothing at this level constrains its shape. Over a
       @(see treeset), which is practically balanced, @($d$) is
       @($O(\\log(n))$)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-p (x)
  (declare (xargs :type-prescription (booleanp (zip-frame-p x))))
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

(defrule zip-frame-p-compound-recognizer
  (implies (zip-frame-p x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable zip-frame-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-zip-frame ()
  (declare (xargs :type-prescription :none))
  :returns (frame zip-frame-p
                  :hints (("Goal" :in-theory (enable zip-frame-p))))
  :short "An irrelevant path frame, used as the fixer's default."
  (cons nil (cons (irr-tree-element) nil)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e irr-zip-frame)))

(defrule irr-zip-frame-type-prescription
  (zip-frame-p (irr-zip-frame))
  :rule-classes ((:type-prescription :typed-term (irr-zip-frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-fix ((frame zip-frame-p))
  (declare (xargs :type-prescription :none))
  :returns (frame$ zip-frame-p)
  :short "Fixer for @(see zip-frame-p)s."
  (mbe :logic (if (zip-frame-p frame)
                  frame
                (irr-zip-frame))
       :exec (the cons frame))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame-fix-type-prescription
  (zip-frame-p (zip-frame-fix frame))
  :rule-classes ((:type-prescription :typed-term (zip-frame-fix frame))))

(defrule zip-frame-fix-when-zip-frame-p
  (implies (zip-frame-p frame)
           (equal (zip-frame-fix frame)
                  frame))
  :enable zip-frame-fix)

(defruled zip-frame-fix-when-not-zip-frame-p
  (implies (not (zip-frame-p frame))
           (equal (zip-frame-fix frame)
                  (irr-zip-frame)))
  :enable zip-frame-fix)

(defrule zip-frame-fix-when-not-zip-frame-p-cheap
  (implies (not (zip-frame-p frame))
           (equal (zip-frame-fix frame)
                  (irr-zip-frame)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by zip-frame-fix-when-not-zip-frame-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-equiv
  ((x zip-frame-p)
   (y zip-frame-p))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Equivalence up to @(tsee zip-frame-fix)."
  (equal (zip-frame-fix x)
         (zip-frame-fix y))
  :inline t

  ///

  (defequiv zip-frame-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame-fix-when-zip-frame-equiv-congruence
  (implies (zip-frame-equiv frame0 frame1)
           (equal (zip-frame-fix frame0)
                  (zip-frame-fix frame1)))
  :rule-classes :congruence
  :enable zip-frame-equiv)

(defrule zip-frame-fix-under-zip-frame-equiv
  (zip-frame-equiv (zip-frame-fix frame)
                   frame)
  :enable zip-frame-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame->from-left ((frame zip-frame-p))
  :returns (from-left booleanp
                      :hints (("Goal" :in-theory (enable zip-frame-p
                                                         zip-frame-fix
                                                         irr-zip-frame))))
  :short "Check whether the focus lies in the left child of the frame's node."
  (car (zip-frame-fix frame))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame->from-left-when-zip-frame-equiv-congruence
  (implies (zip-frame-equiv frame0 frame1)
           (equal (zip-frame->from-left frame0)
                  (zip-frame->from-left frame1)))
  :rule-classes :congruence
  :enable (zip-frame->from-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame->elem ((frame zip-frame-p))
  :returns (elem tree-element-p
                 :hints (("Goal" :in-theory (enable zip-frame-p
                                                    zip-frame-fix
                                                    irr-zip-frame))))
  :short "Get the element of the frame's node."
  (cadr (zip-frame-fix frame))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zip-frame-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame->elem-when-zip-frame-equiv-congruence
  (implies (zip-frame-equiv frame0 frame1)
           (equal (zip-frame->elem frame0)
                  (zip-frame->elem frame1)))
  :rule-classes :congruence
  :enable (zip-frame->elem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame->sibling ((frame zip-frame-p))
  :returns (sibling treep
                    :hints (("Goal" :in-theory (enable zip-frame-p
                                                       zip-frame-fix
                                                       irr-zip-frame))))
  :short "Get the child of the frame's node not descended into."
  (cddr (zip-frame-fix frame))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zip-frame-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame->sibling-when-zip-frame-equiv-congruence
  (implies (zip-frame-equiv frame0 frame1)
           (equal (zip-frame->sibling frame0)
                  (zip-frame->sibling frame1)))
  :rule-classes :congruence
  :enable (zip-frame->sibling))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame
  ((from-left booleanp)
   (elem tree-element-p)
   (sibling treep))
  (declare (xargs :type-prescription :none))
  :returns (frame zip-frame-p
                  :hints (("Goal" :in-theory (enable zip-frame-p))))
  :short "Constructor for @(see zip-frame-p)s."
  (cons (if from-left t nil)
        (cons (tree-element-fix elem)
              (tree-fix sibling)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame-type-prescription
  (zip-frame-p (zip-frame from-left elem sibling))
  :rule-classes ((:type-prescription
                   :typed-term (zip-frame from-left elem sibling))))

(defrule zip-frame-when-tree-element-equiv-of-arg2-congruence
  (implies (tree-element-equiv elem0 elem1)
           (equal (zip-frame from-left elem0 sibling)
                  (zip-frame from-left elem1 sibling)))
  :rule-classes :congruence
  :enable zip-frame)

(defrule zip-frame-when-tree-equiv-of-arg3-congruence
  (implies (tree-equiv sibling0 sibling1)
           (equal (zip-frame from-left elem sibling0)
                  (zip-frame from-left elem sibling1)))
  :rule-classes :congruence
  :enable zip-frame)

(defrule zip-frame->from-left-of-zip-frame
  (equal (zip-frame->from-left (zip-frame from-left elem sibling))
         (and from-left t))
  :enable (zip-frame
           zip-frame->from-left
           zip-frame-p))

(defrule zip-frame->elem-of-zip-frame
  (equal (zip-frame->elem (zip-frame from-left elem sibling))
         (tree-element-fix elem))
  :enable (zip-frame
           zip-frame->elem
           zip-frame-p))

(defrule zip-frame->sibling-of-zip-frame
  (equal (zip-frame->sibling (zip-frame from-left elem sibling))
         (tree-fix sibling))
  :enable (zip-frame
           zip-frame->sibling
           zip-frame-p))

(defrule zip-frame-elim
  (implies (zip-frame-p frame)
           (equal (zip-frame (zip-frame->from-left frame)
                             (zip-frame->elem frame)
                             (zip-frame->sibling frame))
                  frame))
  :rule-classes :elim
  :enable (zip-frame
           zip-frame->from-left
           zip-frame->elem
           zip-frame->sibling
           zip-frame-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-listp (x)
  (declare (xargs :type-prescription (booleanp (zip-frame-listp x))))
  :short "Recognizer for lists of @(see zip-frame-p)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "A path is such a list, ordered from the frame nearest the focus to the
      frame of the root."))
  (if (consp x)
      (and (zip-frame-p (car x))
           (zip-frame-listp (cdr x)))
    (null x)))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame-listp-compound-recognizer
  (if (zip-frame-listp x)
      (true-listp x)
    x)
  :rule-classes :compound-recognizer
  :induct t
  :enable zip-frame-listp)

(defrule zip-frame-p-of-car-when-zip-frame-listp
  (implies (zip-frame-listp path)
           (equal (zip-frame-p (car path))
                  (consp path)))
  :enable zip-frame-listp)

(defrule zip-frame-listp-of-cdr
  (implies (zip-frame-listp path)
           (zip-frame-listp (cdr path)))
  :enable zip-frame-listp)

(defrule zip-frame-listp-of-cons
  (equal (zip-frame-listp (cons frame path))
         (and (zip-frame-p frame)
              (zip-frame-listp path)))
  :enable zip-frame-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-list-fix ((path zip-frame-listp))
  :returns (path$ zip-frame-listp)
  :short "Fixer for @(see zip-frame-listp)s."
  (mbe :logic (if (zip-frame-listp path) path nil)
       :exec (the list path))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-frame-list-fix)))

(defrule zip-frame-list-fix-when-zip-frame-listp
  (implies (zip-frame-listp path)
           (equal (zip-frame-list-fix path)
                  path))
  :enable zip-frame-list-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-count-lefts ((path zip-frame-listp))
  (declare (xargs :type-prescription :none))
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
    (+ (if (zip-frame->from-left (car path)) 1 0)
       (zip-count-lefts (cdr path))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-count-rights ((path zip-frame-listp))
  (declare (xargs :type-prescription :none))
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
    (+ (if (zip-frame->from-left (car path)) 0 1)
       (zip-count-rights (cdr path))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-count-lefts-of-cons
  (equal (zip-count-lefts (cons frame path))
         (+ (if (zip-frame->from-left frame) 1 0)
            (zip-count-lefts path)))
  :enable zip-count-lefts)

(defrule zip-count-rights-of-cons
  (equal (zip-count-rights (cons frame path))
         (+ (if (zip-frame->from-left frame) 0 1)
            (zip-count-rights path)))
  :enable zip-count-rights)

(defrule zip-count-lefts-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-count-lefts path)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-count-lefts)

(defrule zip-count-rights-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-count-rights path)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-count-rights)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zipp (x)
  (declare (xargs :type-prescription (booleanp (zipp x))))
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
       (zip-frame-listp (cadr x))
       (equal (caddr x) (zip-count-lefts (cadr x)))
       (equal (cdddr x) (zip-count-rights (cadr x)))))

;;;;;;;;;;;;;;;;;;;;

(defrule zipp-compound-recognizer
  (implies (zipp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable zipp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-zip ()
  (declare (xargs :type-prescription :none))
  :returns (zip zipp
                :hints (("Goal" :in-theory (enable zipp))))
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

(in-theory (disable (:e irr-zip)))

(defrule irr-zip-type-prescription
  (zipp (irr-zip))
  :rule-classes ((:type-prescription :typed-term (irr-zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-fix ((zip zipp))
  (declare (xargs :type-prescription :none))
  :returns (zip$ zipp)
  :short "Fixer for @(see zipper)s."
  (mbe :logic (if (zipp zip)
                  zip
                (irr-zip))
       :exec (the cons zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-fix-type-prescription
  (zipp (zip-fix zip))
  :rule-classes ((:type-prescription :typed-term (zip-fix zip))))

(defrule zip-fix-when-zipp
  (implies (zipp zip)
           (equal (zip-fix zip)
                  zip))
  :enable zip-fix)

(defruled zip-fix-when-not-zipp
  (implies (not (zipp zip))
           (equal (zip-fix zip)
                  (irr-zip)))
  :enable zip-fix)

(defrule zip-fix-when-not-zipp-cheap
  (implies (not (zipp zip))
           (equal (zip-fix zip)
                  (irr-zip)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by zip-fix-when-not-zipp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-equiv
  ((x zipp)
   (y zipp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Equivalence up to @(tsee zip-fix)."
  (equal (zip-fix x)
         (zip-fix y))
  :inline t
  ///

  (defequiv zip-equiv))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-fix-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-fix zip0)
                  (zip-fix zip1)))
  :rule-classes :congruence
  :enable zip-equiv)

(defrule zip-fix-under-zip-equiv
  (zip-equiv (zip-fix zip)
             zip)
  :enable zip-equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip->focus ((zip zipp))
  :returns (focus treep
                  :hints (("Goal" :in-theory (enable zipp
                                                     zip-fix
                                                     irr-zip))))
  :short "Get the subtree in focus."
  (car (zip-fix zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip->focus-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip->focus zip0)
                  (zip->focus zip1)))
  :rule-classes :congruence
  :enable (zip->focus))

;; A zipper is always at an element. This holds of any object, since the fixer
;; sends a non-zipper to one which is also at an element, so it discharges the
;; hypothesis on the constructor's type with nothing to backchain through.

(defrule not-tree-empty-p-of-zip->focus
  (not (tree-empty-p (zip->focus zip)))
  :enable (zip->focus
           zip-fix
           zipp
           irr-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip->path ((zip zipp))
  :returns (path zip-frame-listp
                 :hints (("Goal" :in-theory (enable zipp
                                                    zip-fix
                                                    irr-zip))))
  :short "Get the path from the root down to the focus."
  (cadr (zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zipp))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip->path-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip->path zip0)
                  (zip->path zip1)))
  :rule-classes :congruence
  :enable (zip->path))

;; The frame-list compound recognizer cannot fire on a compound term, so the
;; iterated ascents, whose base case tests @(tsee endp) of a path, need this.

(defrule true-listp-of-zip->path
  (true-listp (zip->path zip))
  :rule-classes :type-prescription
  :use zip-frame-listp-of-zip->path
  :disable zip-frame-listp-of-zip->path)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip->nlefts ((zip zipp))
  :returns (nlefts natp
                   :rule-classes :type-prescription
                   :hints (("Goal" :in-theory (enable zipp
                                                      zip-fix
                                                      irr-zip))))
  :short "Get the number of frames whose node follows the focus in order."
  (caddr (zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zipp))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip->nlefts-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip->nlefts zip0)
                  (zip->nlefts zip1)))
  :rule-classes :congruence
  :enable (zip->nlefts))

;; The cached count always agrees with the path, even for ill-formed input,
;; since the fixer supplies the empty zipper. We normalize the cache away, so
;; that reasoning only ever sees the path.
(defrule zip->nlefts-becomes-zip-count-lefts
  (equal (zip->nlefts zip)
         (zip-count-lefts (zip->path zip)))
  :enable (zip->nlefts
           zip->path
           zip-fix
           zipp
           irr-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip->nrights ((zip zipp))
  :returns (nrights natp
                    :rule-classes :type-prescription
                    :hints (("Goal" :in-theory (enable zipp
                                                       zip-fix
                                                       irr-zip))))
  :short "Get the number of frames whose node precedes the focus in order."
  (cdddr (zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zipp))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip->nrights-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip->nrights zip0)
                  (zip->nrights zip1)))
  :rule-classes :congruence
  :enable (zip->nrights))

(defrule zip->nrights-becomes-zip-count-rights
  (equal (zip->nrights zip)
         (zip-count-rights (zip->path zip)))
  :enable (zip->nrights
           zip->path
           zip-fix
           zipp
           irr-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip
  ((focus treep)
   (path zip-frame-listp)
   (nlefts natp)
   (nrights natp))
  (declare (xargs :type-prescription :none))
  :guard (and (not (tree-empty-p focus))
              (equal nlefts (zip-count-lefts path))
              (equal nrights (zip-count-rights path)))
  :returns (zip zipp
                :hints (("Goal" :in-theory (enable zipp))))
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
  (let ((path (zip-frame-list-fix path))
        (focus (mbe :logic (if (tree-empty-p focus)
                               (tree-node (irr-tree-element) nil nil)
                             (tree-fix focus))
                    :exec focus)))
    (cons focus
          (cons path
                (cons (mbe :logic (zip-count-lefts path)
                           :exec nlefts)
                      (mbe :logic (zip-count-rights path)
                           :exec nrights)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-type-prescription
  (zipp (zip focus path nlefts nrights))
  :rule-classes ((:type-prescription
                   :typed-term (zip focus path nlefts nrights))))

(defrule zip-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv focus0 focus1)
           (equal (zip focus0 path nlefts nrights)
                  (zip focus1 path nlefts nrights)))
  :rule-classes :congruence
  :enable zip)

;; Logically, the counts are ignored. We choose to arbitrarily normalize them
;; to nil.
(defruled zip-arg3-becomes-nil
  (equal (zip focus path nlefts nrights)
         (zip focus path nil nrights))
  :enable zip)

(defrule zip-when-arg3-not-nil-syntaxp
  (implies (syntaxp (not (equal nlefts ''nil)))
           (equal (zip focus path nlefts nrights)
                  (zip focus path nil nrights)))
  :by zip-arg3-becomes-nil)

(defruled zip-arg4-becomes-nil
  (equal (zip focus path nlefts nrights)
         (zip focus path nlefts nil))
  :enable zip)

(defrule zip-when-arg4-not-nil-syntaxp
  (implies (syntaxp (not (equal nrights ''nil)))
           (equal (zip focus path nlefts nrights)
                  (zip focus path nlefts nil)))
  :by zip-arg4-becomes-nil)

(defrule zip->focus-of-zip
  (implies (not (tree-empty-p focus))
           (equal (zip->focus (zip focus path nlefts nrights))
                  (tree-fix focus)))
  :enable (zip
           zip->focus
           zipp))

(defrule zip->path-of-zip
  (equal (zip->path (zip focus path nlefts nrights))
         (zip-frame-list-fix path))
  :enable (zip
           zip->path
           zipp))

;; These follow from the normalization of the cached counts into counts of the
;; path, so they need no help beyond the rule for the path itself.
(defrule zip->nlefts-of-zip
  (equal (zip->nlefts (zip focus path nlefts nrights))
         (zip-count-lefts (zip-frame-list-fix path))))

(defrule zip->nrights-of-zip
  (equal (zip->nrights (zip focus path nlefts nrights))
         (zip-count-rights (zip-frame-list-fix path))))

(defrule zip-elim
  (implies (zipp zip)
           (equal (zip (zip->focus zip)
                       (zip->path zip)
                       (zip->nlefts zip)
                       (zip->nrights zip))
                  zip))
  :rule-classes :elim
  :enable (zip
           zip->focus
           zip->path
           zipp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-plug
  ((frame zip-frame-p)
   (tree treep))
  :returns (tree$ treep)
  :short "Rebuild the node of a frame, with the given tree in its hole."
  (if (zip-frame->from-left frame)
      (tree-node (zip-frame->elem frame)
                 tree
                 (zip-frame->sibling frame))
    (tree-node (zip-frame->elem frame)
               (zip-frame->sibling frame)
               tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-frame-plug-when-zip-frame-equiv-of-arg1-congruence
  (implies (zip-frame-equiv frame0 frame1)
           (equal (zip-frame-plug frame0 tree)
                  (zip-frame-plug frame1 tree)))
  :rule-classes :congruence
  :enable zip-frame-plug)

(defrule zip-frame-plug-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-frame-plug frame tree0)
                  (zip-frame-plug frame tree1)))
  :rule-classes :congruence
  :enable zip-frame-plug)

(defrule tree-empty-p-of-zip-frame-plug
  (not (tree-empty-p (zip-frame-plug frame tree)))
  :enable zip-frame-plug)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-plug
  ((path zip-frame-listp)
   (tree treep))
  :returns (tree$ treep)
  :short "Rebuild a tree by plugging it into a path, innermost frame first."
  (if (endp path)
      (tree-fix tree)
    (zip-path-plug (cdr path)
                   (zip-frame-plug (car path) tree))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-path-plug)))

(defrule zip-path-plug-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-path-plug path tree0)
                  (zip-path-plug path tree1)))
  :rule-classes :congruence
  :induct t
  :enable zip-path-plug)

(defrule zip-path-plug-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-path-plug path tree)
                  (tree-fix tree)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-plug)

(defrule zip-path-plug-of-cons
  (equal (zip-path-plug (cons frame path) tree)
         (zip-path-plug path (zip-frame-plug frame tree)))
  :enable zip-path-plug)

(defrule tree-empty-p-of-zip-path-plug
  (equal (tree-empty-p (zip-path-plug path tree))
         (and (not (consp path))
              (tree-empty-p tree)))
  :induct t
  :enable zip-path-plug)

;; The tree recovered from a zipper carries the invariants of every subtree
;; along the way, so the focus inherits them with no zipper-local restatement
;; of the binary search tree or heap properties.

(defrule bstp-of-arg2-when-bstp-of-zip-path-plug
  (implies (bstp (zip-path-plug path tree))
           (bstp tree))
  :induct t
  :enable (zip-path-plug
           zip-frame-plug))

(defrule heapp-of-arg2-when-heapp-of-zip-path-plug
  (implies (heapp (zip-path-plug path tree))
           (heapp tree))
  :induct t
  :enable (zip-path-plug
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-plug ((zip zipp))
  :returns (tree treep)
  :short "Recover the whole tree from a zipper."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus, and
      so @($O(\\log(n))$) over a @(see treeset)."))
  (zip-path-plug (zip->path zip)
                 (zip->focus zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-plug)))

(defrule zip-plug-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-plug zip0)
                  (zip-plug zip1)))
  :rule-classes :congruence
  :enable zip-plug)

(defrule zip-plug-of-zip
  (implies (not (tree-empty-p focus))
           (equal (zip-plug (zip focus path nlefts nrights))
                  (zip-path-plug (zip-frame-list-fix path)
                                 (tree-fix focus))))
  :enable zip-plug)

;; A zipper is at an element, so the tree it is a cursor into holds at least
;; that element.

(defrule not-tree-empty-p-of-zip-plug
  (not (tree-empty-p (zip-plug zip)))
  :enable zip-plug)

(defrule zip-plug-of-irr-zip
  (equal (zip-plug (irr-zip))
         (tree-node (irr-tree-element) nil nil))
  :enable (zip-plug
           irr-zip
           zip-fix
           zip->path
           zip->focus))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rewrite forms of the elim rules, which as @(':elim') rules do not apply to
;; the compound terms the movement proofs produce. The frame case is split on
;; the flag, since the reconstructed frame carries a literal t or nil there.
;;
;; These sit together here, just ahead of the movement layer that needs them,
;; rather than each beside the rule it mirrors: those are in three separate
;; places -- zip-frame-elim and zip-elim above, and tree-node-elim in another
;; book entirely -- so there is no single place to be next to. They are local
;; scaffolding for the proofs that follow, not part of the interface.

(defrulel tree-node-of-tree->head-and-tree->left-and-tree->right
  (implies (not (tree-empty-p tree))
           (equal (tree-node (tree->head tree)
                             (tree->left tree)
                             (tree->right tree))
                  tree))
  :by tree-node-elim)

(defrulel zip-of-zip-accessors
  (equal (zip (zip->focus zip) (zip->path zip) nil nil)
         (zip-fix zip))
  :enable (zip
           zip->focus
           zip->path
           zip-fix
           zipp
           irr-zip))

(defrulel zip-frame-of-t-and-accessors-when-from-left
  (implies (and (zip-frame-p frame)
                (zip-frame->from-left frame))
           (equal (zip-frame t
                             (zip-frame->elem frame)
                             (zip-frame->sibling frame))
                  frame))
  :enable (zip-frame
           zip-frame->elem
           zip-frame->sibling
           zip-frame-p))

(defrulel zip-frame-of-nil-and-accessors-when-not-from-left
  (implies (and (zip-frame-p frame)
                (not (zip-frame->from-left frame)))
           (equal (zip-frame nil
                             (zip-frame->elem frame)
                             (zip-frame->sibling frame))
                  frame))
  :enable (zip-frame
           zip-frame->elem
           zip-frame->sibling
           zip-frame-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The single steps. Every other move iterates one of these, so that each move
;; is defined, and reasoned about, at the level of whole zippers rather than
;; their parts. Moving a zipper never changes the tree it is a cursor into,
;; which is what the plug rules below record.

(define zip-descend-left ((zip zipp))
  :guard (not (tree-empty-p (tree->left (zip->focus zip))))
  :returns (zip$ zipp)
  :short "Move the focus to the left child, pushing a frame."
  (let ((focus (zip->focus zip)))
    (zip (tree->left focus)
         (cons (zip-frame t (tree->head focus) (tree->right focus))
               (zip->path zip))
         (+ 1 (the unsigned-byte (zip->nlefts zip)))
         (zip->nrights zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-descend-left)))

(defrule zip-descend-left-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-left zip0)
                  (zip-descend-left zip1)))
  :rule-classes :congruence
  :enable zip-descend-left)

(defrule zip-plug-of-zip-descend-left
  (implies (not (tree-empty-p (tree->left (zip->focus zip))))
           (equal (zip-plug (zip-descend-left zip))
                  (zip-plug zip)))
  :enable (zip-descend-left
           zip-plug
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-right ((zip zipp))
  :guard (not (tree-empty-p (tree->right (zip->focus zip))))
  :returns (zip$ zipp)
  :short "Move the focus to the right child, pushing a frame."
  (let ((focus (zip->focus zip)))
    (zip (tree->right focus)
         (cons (zip-frame nil (tree->head focus) (tree->left focus))
               (zip->path zip))
         (zip->nlefts zip)
         (+ 1 (the unsigned-byte (zip->nrights zip)))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-descend-right)))

(defrule zip-descend-right-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-right zip0)
                  (zip-descend-right zip1)))
  :rule-classes :congruence
  :enable zip-descend-right)

(defrule zip-plug-of-zip-descend-right
  (implies (not (tree-empty-p (tree->right (zip->focus zip))))
           (equal (zip-plug (zip-descend-right zip))
                  (zip-plug zip)))
  :enable (zip-descend-right
           zip-plug
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What the single-step descents do to a zipper's parts. These come before
;; the iterated moves, whose measures are stated on the focus.

(defrule zip->focus-of-zip-descend-left
  (implies (not (tree-empty-p (tree->left (zip->focus zip))))
           (equal (zip->focus (zip-descend-left zip))
                  (tree->left (zip->focus zip))))
  :enable zip-descend-left)

(defrule zip->focus-of-zip-descend-right
  (implies (not (tree-empty-p (tree->right (zip->focus zip))))
           (equal (zip->focus (zip-descend-right zip))
                  (tree->right (zip->focus zip))))
  :enable zip-descend-right)

(defrule zip->path-of-zip-descend-left
  (equal (zip->path (zip-descend-left zip))
         (cons (zip-frame t
                          (tree->head (zip->focus zip))
                          (tree->right (zip->focus zip)))
               (zip->path zip)))
  :enable zip-descend-left)

(defrule zip->path-of-zip-descend-right
  (equal (zip->path (zip-descend-right zip))
         (cons (zip-frame nil
                          (tree->head (zip->focus zip))
                          (tree->left (zip->focus zip)))
               (zip->path zip)))
  :enable zip-descend-right)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-ascend-one ((zip zipp))
  :guard (consp (zip->path zip))
  :returns (zip$ zipp)
  :short "Move the focus up to its parent, popping a frame."
  :long
  (xdoc::topstring
   (xdoc::p
     "The popped frame says which side the focus hung on, and so which of the
      two counts loses one."))
  (let ((frame (car (zip->path zip))))
    (zip (zip-frame-plug frame (zip->focus zip))
         (cdr (zip->path zip))
         (if (zip-frame->from-left frame)
             (- (the (integer 1 *) (zip->nlefts zip)) 1)
           (zip->nlefts zip))
         (if (zip-frame->from-left frame)
             (zip->nrights zip)
           (- (the (integer 1 *) (zip->nrights zip)) 1))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zip-count-lefts
                                           zip-count-rights))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-ascend-one)))

(defrule zip-ascend-one-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-ascend-one zip0)
                  (zip-ascend-one zip1)))
  :rule-classes :congruence
  :enable zip-ascend-one)

(defrule zip-plug-of-zip-ascend-one
  (implies (consp (zip->path zip))
           (equal (zip-plug (zip-ascend-one zip))
                  (zip-plug zip)))
  :expand ((zip-path-plug (zip->path zip) (zip->focus zip)))
  :enable (zip-ascend-one
           zip-plug))

(defrule zip->path-of-zip-ascend-one
  (implies (consp (zip->path zip))
           (equal (zip->path (zip-ascend-one zip))
                  (cdr (zip->path zip))))
  :enable zip-ascend-one)

(defrule zip->focus-of-zip-ascend-one
  (implies (consp (zip->path zip))
           (equal (zip->focus (zip-ascend-one zip))
                  (zip-frame-plug (car (zip->path zip))
                                  (zip->focus zip))))
  :enable zip-ascend-one)

;; A single-step ascent undoes a single-step descent. Every cancellation law
;; between the iterated moves comes back to one of these two.

(defrule zip-ascend-one-of-zip-descend-left
  (implies (not (tree-empty-p (tree->left (zip->focus zip))))
           (equal (zip-ascend-one (zip-descend-left zip))
                  (zip-fix zip)))
  :enable (zip-ascend-one
           zip-frame-plug))

(defrule zip-ascend-one-of-zip-descend-right
  (implies (not (tree-empty-p (tree->right (zip->focus zip))))
           (equal (zip-ascend-one (zip-descend-right zip))
                  (zip-fix zip)))
  :enable (zip-ascend-one
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-leftmost ((zip zipp))
  :returns (zip$ zipp)
  :short "Move the focus to the leftmost node within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended, and so
      @($O(\\log(n))$) over a @(see treeset)."))
  (if (tree-empty-p (tree->left (zip->focus zip)))
      (zip-fix zip)
    (zip-descend-leftmost (zip-descend-left zip)))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-descend-leftmost)))

(defrule zip-descend-leftmost-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-leftmost zip0)
                  (zip-descend-leftmost zip1)))
  :rule-classes :congruence
  :expand ((zip-descend-leftmost zip0)
           (zip-descend-leftmost zip1)))

(defrule zip-plug-of-zip-descend-leftmost
  (equal (zip-plug (zip-descend-leftmost zip))
         (zip-plug zip))
  :induct t
  :enable zip-descend-leftmost)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-rightmost ((zip zipp))
  :returns (zip$ zipp)
  :short "Move the focus to the rightmost node within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended, and so
      @($O(\\log(n))$) over a @(see treeset)."))
  (if (tree-empty-p (tree->right (zip->focus zip)))
      (zip-fix zip)
    (zip-descend-rightmost (zip-descend-right zip)))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-descend-rightmost)))

(defrule zip-descend-rightmost-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-rightmost zip0)
                  (zip-descend-rightmost zip1)))
  :rule-classes :congruence
  :expand ((zip-descend-rightmost zip0)
           (zip-descend-rightmost zip1)))

(defrule zip-plug-of-zip-descend-rightmost
  (equal (zip-plug (zip-descend-rightmost zip))
         (zip-plug zip))
  :induct t
  :enable zip-descend-rightmost)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-ascend-to-left-frame ((zip zipp))
  :returns (zip$ zipp)
  :short "Move the focus up to the nearest ancestor that follows it."
  :long
  (xdoc::topstring
   (xdoc::p
     "That ancestor is the node of the nearest frame the focus hangs to the
      left of, and it is the in-order successor of everything below it on that
      side. When there is no such frame the focus has no successor above it,
      and we ascend all the way to the root.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth ascended, and so
      @($O(\\log(n))$) over a @(see treeset)."))
  (cond ((endp (zip->path zip))
         (zip-fix zip))
        ((zip-frame->from-left (car (zip->path zip)))
         (zip-ascend-one zip))
        (t
         (zip-ascend-to-left-frame (zip-ascend-one zip))))
  :measure (len (zip->path zip)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-ascend-to-left-frame)))

(defrule zip-ascend-to-left-frame-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-ascend-to-left-frame zip0)
                  (zip-ascend-to-left-frame zip1)))
  :rule-classes :congruence
  :expand ((zip-ascend-to-left-frame zip0)
           (zip-ascend-to-left-frame zip1)))

(defrule zip-plug-of-zip-ascend-to-left-frame
  (equal (zip-plug (zip-ascend-to-left-frame zip))
         (zip-plug zip))
  :induct t
  :enable zip-ascend-to-left-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-ascend-to-right-frame ((zip zipp))
  :returns (zip$ zipp)
  :short "Move the focus up to the nearest ancestor that precedes it."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-ascend-to-left-frame)."))
  (cond ((endp (zip->path zip))
         (zip-fix zip))
        ((zip-frame->from-left (car (zip->path zip)))
         (zip-ascend-to-right-frame (zip-ascend-one zip)))
        (t
         (zip-ascend-one zip)))
  :measure (len (zip->path zip)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-ascend-to-right-frame)))

(defrule zip-ascend-to-right-frame-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-ascend-to-right-frame zip0)
                  (zip-ascend-to-right-frame zip1)))
  :rule-classes :congruence
  :expand ((zip-ascend-to-right-frame zip0)
           (zip-ascend-to-right-frame zip1)))

(defrule zip-plug-of-zip-ascend-to-right-frame
  (equal (zip-plug (zip-ascend-to-right-frame zip))
         (zip-plug zip))
  :induct t
  :enable zip-ascend-to-right-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The boundary checks. Each is constant time: the focus and the cached counts
;; are all immediately at hand. A zipper is at the first element exactly when
;; nothing lies to its left, which is to say its focus has no left child and no
;; ancestor precedes it.

(define zip-at-first-p ((zip zipp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is focused on the first element."
  (and (tree-empty-p (tree->left (zip->focus zip)))
       (equal (zip->nrights zip) 0))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-at-last-p ((zip zipp))
  (declare (xargs :type-prescription :none))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is focused on the last element."
  (and (tree-empty-p (tree->right (zip->focus zip)))
       (equal (zip->nlefts zip) 0))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-at-first-p-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-at-first-p zip0)
                  (zip-at-first-p zip1)))
  :rule-classes :congruence
  :enable zip-at-first-p)

(defrule zip-at-last-p-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-at-last-p zip0)
                  (zip-at-last-p zip1)))
  :rule-classes :congruence
  :enable zip-at-last-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-next ((zip zipp))
  :guard (not (zip-at-last-p zip))
  :returns (zip$ zipp)
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
     "Time complexity: @($O(d)$) in the worst case -- @($O(\\log(n))$) over a
      @(see treeset) -- but @($O(1)$) amortized over a traversal, since each
      edge of the tree is crossed twice."))
  ;; Logically the move saturates at the last element, which is what @(tsee
  ;; zip-next-identity-iff-zip-at-last-p) reports. The guard rules that case
  ;; out of execution, so the executable form need not test for it.
  (mbe :logic (cond ((zip-at-last-p zip)
                     (zip-fix zip))
                    ((tree-empty-p (tree->right (zip->focus zip)))
                     (zip-ascend-to-left-frame zip))
                    (t
                     (zip-descend-leftmost (zip-descend-right zip))))
       :exec (if (tree-empty-p (tree->right (zip->focus zip)))
                 (zip-ascend-to-left-frame zip)
               (zip-descend-leftmost (zip-descend-right zip))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zip-at-last-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-next)))

(defrule zip-next-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-next zip0)
                  (zip-next zip1)))
  :rule-classes :congruence
  :enable zip-next)

(defrule zip-plug-of-zip-next
  (equal (zip-plug (zip-next zip))
         (zip-plug zip))
  :enable (zip-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-prev ((zip zipp))
  :guard (not (zip-at-first-p zip))
  :returns (zip$ zipp)
  :short "Move the focus to the previous element in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-next)."))
  ;; The mirror of @(tsee zip-next), guard and all.
  (mbe :logic (cond ((zip-at-first-p zip)
                     (zip-fix zip))
                    ((tree-empty-p (tree->left (zip->focus zip)))
                     (zip-ascend-to-right-frame zip))
                    (t
                     (zip-descend-rightmost (zip-descend-left zip))))
       :exec (if (tree-empty-p (tree->left (zip->focus zip)))
                 (zip-ascend-to-right-frame zip)
               (zip-descend-rightmost (zip-descend-left zip))))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zip-at-first-p))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-prev)))

(defrule zip-prev-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-prev zip0)
                  (zip-prev zip1)))
  :rule-classes :congruence
  :enable zip-prev)

(defrule zip-plug-of-zip-prev
  (equal (zip-plug (zip-prev zip))
         (zip-plug zip))
  :enable (zip-prev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Where a descent lands, and what it leaves untouched.

(defrule zip-descend-leftmost-when-tree-empty-p-of-left-of-focus
  (implies (tree-empty-p (tree->left (zip->focus zip)))
           (equal (zip-descend-leftmost zip)
                  (zip-fix zip)))
  :enable zip-descend-leftmost)

(defrule zip-descend-rightmost-when-tree-empty-p-of-right-of-focus
  (implies (tree-empty-p (tree->right (zip->focus zip)))
           (equal (zip-descend-rightmost zip)
                  (zip-fix zip)))
  :enable zip-descend-rightmost)

(defrule tree-empty-p-of-tree->left-of-focus-of-zip-descend-leftmost
  (tree-empty-p
    (tree->left (zip->focus (zip-descend-leftmost zip))))
  :induct t
  :enable zip-descend-leftmost)

(defrule tree-empty-p-of-tree->right-of-focus-of-zip-descend-rightmost
  (tree-empty-p
    (tree->right (zip->focus (zip-descend-rightmost zip))))
  :induct t
  :enable zip-descend-rightmost)

;; A leftmost descent pushes only left frames, so it leaves the other count
;; alone, and vice versa.

(defrule zip-count-rights-of-path-of-zip-descend-leftmost
  (equal (zip-count-rights
           (zip->path (zip-descend-leftmost zip)))
         (zip-count-rights (zip->path zip)))
  :induct t
  :enable zip-descend-leftmost)

(defrule zip-count-lefts-of-path-of-zip-descend-rightmost
  (equal (zip-count-lefts
           (zip->path (zip-descend-rightmost zip)))
         (zip-count-lefts (zip->path zip)))
  :induct t
  :enable zip-descend-rightmost)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The boundaries: at either end the move saturates.

(defrule zip-next-when-zip-at-last-p
  (implies (zip-at-last-p zip)
           (equal (zip-next zip)
                  (zip-fix zip)))
  :enable zip-next)

(defrule zip-prev-when-zip-at-first-p
  (implies (zip-at-first-p zip)
           (equal (zip-prev zip)
                  (zip-fix zip)))
  :enable zip-prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A single-step descent and a single-step ascent are inverse. Both directions
;; are needed: the ascent cancels a descent just taken, and the descent
;; retraces an ascent whose frame hung on the matching side.

(defruledl zip-descend-left-of-zip-ascend-one-when-from-left
  (implies (and (consp (zip->path zip))
                (zip-frame->from-left (car (zip->path zip))))
           (equal (zip-descend-left (zip-ascend-one zip))
                  (zip-fix zip)))
  :enable (zip-descend-left
           zip-frame-plug))

(defruledl zip-descend-right-of-zip-ascend-one-when-not-from-left
  (implies (and (consp (zip->path zip))
                (not (zip-frame->from-left (car (zip->path zip)))))
           (equal (zip-descend-right (zip-ascend-one zip))
                  (zip-fix zip)))
  :enable (zip-descend-right
           zip-frame-plug))

;; Popping a frame the focus hung to the right of does not move the rightmost
;; node below, and symmetrically.

(defruledl zip-descend-rightmost-of-zip-ascend-one-when-not-from-left
  (implies (and (consp (zip->path zip))
                (not (zip-frame->from-left (car (zip->path zip)))))
           (equal (zip-descend-rightmost (zip-ascend-one zip))
                  (zip-descend-rightmost zip)))
  :expand ((zip-descend-rightmost (zip-ascend-one zip)))
  :enable (zip-frame-plug
           zip-descend-right-of-zip-ascend-one-when-not-from-left))

(defruledl zip-descend-leftmost-of-zip-ascend-one-when-from-left
  (implies (and (consp (zip->path zip))
                (zip-frame->from-left (car (zip->path zip))))
           (equal (zip-descend-leftmost (zip-ascend-one zip))
                  (zip-descend-leftmost zip)))
  :expand ((zip-descend-leftmost (zip-ascend-one zip)))
  :enable (zip-frame-plug
           zip-descend-left-of-zip-ascend-one-when-from-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Descending and then ascending past what was pushed cancels out: a leftmost
;; descent pushes only left frames, and an ascent to a right frame pops left
;; frames on its way, so the descent leaves no trace.

(defruledl zip-ascend-to-right-frame-of-zip-descend-leftmost
  (equal (zip-ascend-to-right-frame (zip-descend-leftmost zip))
         (zip-ascend-to-right-frame zip))
  :induct (zip-descend-leftmost zip)
  :enable (zip-descend-leftmost
           zip-ascend-to-right-frame))

(defruledl zip-ascend-to-left-frame-of-zip-descend-rightmost
  (equal (zip-ascend-to-left-frame (zip-descend-rightmost zip))
         (zip-ascend-to-left-frame zip))
  :induct (zip-descend-rightmost zip)
  :enable (zip-descend-rightmost
           zip-ascend-to-left-frame))

;; A single-step descent is undone by the matching searching ascent, since the
;; frame it just pushed is the very frame that ascent stops at.

(defruledl zip-ascend-to-right-frame-of-zip-descend-right
  (implies (not (tree-empty-p (tree->right (zip->focus zip))))
           (equal (zip-ascend-to-right-frame (zip-descend-right zip))
                  (zip-fix zip)))
  :enable zip-ascend-to-right-frame)

(defruledl zip-ascend-to-left-frame-of-zip-descend-left
  (implies (not (tree-empty-p (tree->left (zip->focus zip))))
           (equal (zip-ascend-to-left-frame (zip-descend-left zip))
                  (zip-fix zip)))
  :enable zip-ascend-to-left-frame)

;; And in the other direction: ascending to a frame and then descending back
;; down lands where a descent from the original position would have.

(defruledl zip-descend-rightmost-of-descend-left-of-ascend-to-left-frame
  (implies (not (equal (zip-count-lefts (zip->path zip)) 0))
           (equal (zip-descend-rightmost
                    (zip-descend-left (zip-ascend-to-left-frame zip)))
                  (zip-descend-rightmost zip)))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-count-lefts
           zip-descend-left-of-zip-ascend-one-when-from-left
           zip-descend-rightmost-of-zip-ascend-one-when-not-from-left))

(defruledl zip-descend-leftmost-of-descend-right-of-ascend-to-right-frame
  (implies (not (equal (zip-count-rights (zip->path zip)) 0))
           (equal (zip-descend-leftmost
                    (zip-descend-right (zip-ascend-to-right-frame zip)))
                  (zip-descend-leftmost zip)))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-count-rights
           zip-descend-right-of-zip-ascend-one-when-not-from-left
           zip-descend-leftmost-of-zip-ascend-one-when-from-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An ascent that finds its frame lands on a node with a child on the side it
;; came from, which is what lets the reverse move descend back.

(defruledl not-tree-empty-p-of-left-of-focus-of-ascend-to-left-frame
  (implies (not (equal (zip-count-lefts (zip->path zip)) 0))
           (not (tree-empty-p
                  (tree->left
                    (zip->focus (zip-ascend-to-left-frame zip))))))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-count-lefts
           zip-frame-plug))

(defruledl not-tree-empty-p-of-right-of-focus-of-ascend-to-right-frame
  (implies (not (equal (zip-count-rights (zip->path zip)) 0))
           (not (tree-empty-p
                  (tree->right
                    (zip->focus (zip-ascend-to-right-frame zip))))))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-count-rights
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two moves are inverse everywhere they have somewhere to go. This is
;; where uniqueness earns its keep: the recovered zipper is not merely
;; equivalent to the original, it is @(tsee equal) to it. Since every zipper is
;; at an element, the only exclusions are the two ends, where the move
;; saturates and has nothing to invert.

(defrule zip-prev-of-zip-next
  (implies (not (zip-at-last-p zip))
           (equal (zip-prev (zip-next zip))
                  (zip-fix zip)))
  :enable (zip-next
           zip-prev
           zip-at-last-p
           zip-at-first-p
           zip-descend-rightmost-of-descend-left-of-ascend-to-left-frame
           zip-ascend-to-right-frame-of-zip-descend-leftmost
           zip-ascend-to-right-frame-of-zip-descend-right
           not-tree-empty-p-of-left-of-focus-of-ascend-to-left-frame))

(defrule zip-next-of-zip-prev
  (implies (not (zip-at-first-p zip))
           (equal (zip-next (zip-prev zip))
                  (zip-fix zip)))
  :enable (zip-next
           zip-prev
           zip-at-last-p
           zip-at-first-p
           zip-descend-leftmost-of-descend-right-of-ascend-to-right-frame
           zip-ascend-to-left-frame-of-zip-descend-rightmost
           zip-ascend-to-left-frame-of-zip-descend-left
           not-tree-empty-p-of-right-of-focus-of-ascend-to-right-frame))

;; A move leaves something behind it, so it cannot land at the far end it came
;; from. The two branches argue differently: a descent pushes a right frame, so
;; the count of those is nonzero afterwards; an ascent lands on a node whose
;; child on the side it came from is nonempty. A layer supplying the two ends
;; needs this to know that stepping inward never overshoots.

(defrule not-zip-at-first-p-of-zip-next
  (implies (not (zip-at-last-p zip))
           (not (zip-at-first-p (zip-next zip))))
  :enable (zip-next
           zip-at-last-p
           zip-at-first-p
           not-tree-empty-p-of-left-of-focus-of-ascend-to-left-frame))

(defrule not-zip-at-last-p-of-zip-prev
  (implies (not (zip-at-first-p zip))
           (not (zip-at-last-p (zip-prev zip))))
  :enable (zip-prev
           zip-at-last-p
           zip-at-first-p
           not-tree-empty-p-of-right-of-focus-of-ascend-to-right-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-root ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (zip zipp)
  :short "The zipper focused on a whole tree, with an empty path."
  (zip tree nil 0 0)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-root)))

(defrule zip-root-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-root tree0)
                  (zip-root tree1)))
  :rule-classes :congruence
  :enable zip-root)

(defrule zip-plug-of-zip-root
  (implies (not (tree-empty-p tree))
           (equal (zip-plug (zip-root tree))
                  (tree-fix tree)))
  :enable zip-root)

(defrule zip->focus-of-zip-root
  (implies (not (tree-empty-p tree))
           (equal (zip->focus (zip-root tree))
                  (tree-fix tree)))
  :enable zip-root)

(defrule zip->path-of-zip-root
  (equal (zip->path (zip-root tree))
         nil)
  :enable zip-root)

(defrule zip->nlefts-of-zip-root
  (equal (zip->nlefts (zip-root tree))
         0))

(defrule zip->nrights-of-zip-root
  (equal (zip->nrights (zip-root tree))
         0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-first ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (zip zipp)
  :short "The zipper focused on the first element of a tree."
  (zip-descend-leftmost (zip-root tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-last ((tree treep))
  :guard (not (tree-empty-p tree))
  :returns (zip zipp)
  :short "The zipper focused on the last element of a tree."
  (zip-descend-rightmost (zip-root tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-first) (:t zip-last)))

(defrule zip-first-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-first tree0)
                  (zip-first tree1)))
  :rule-classes :congruence
  :enable zip-first)

(defrule zip-last-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-last tree0)
                  (zip-last tree1)))
  :rule-classes :congruence
  :enable zip-last)

(defrule zip-plug-of-zip-first
  (implies (not (tree-empty-p tree))
           (equal (zip-plug (zip-first tree))
                  (tree-fix tree)))
  :enable zip-first)

(defrule zip-plug-of-zip-last
  (implies (not (tree-empty-p tree))
           (equal (zip-plug (zip-last tree))
                  (tree-fix tree)))
  :enable zip-last)

(defrule zip-at-first-p-of-zip-first
  (implies (not (tree-empty-p tree))
           (zip-at-first-p (zip-first tree)))
  :enable (zip-first
           zip-at-first-p))

(defrule zip-at-last-p-of-zip-last
  (implies (not (tree-empty-p tree))
           (zip-at-last-p (zip-last tree)))
  :enable (zip-last
           zip-at-last-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two ends of a tree are unique: a zipper at the last element is the very
;; zipper @(tsee zip-last) builds, and likewise at the first. A layer
;; supplying the ends needs this to step back inward and land where it started.
;;
;; The argument is that when nothing above the focus follows it, ascending in
;; search of a left frame never finds one and so climbs to the root, and that
;; climb does not move the rightmost node below.

(defrulel zip->path-when-not-consp
  (implies (not (consp (zip->path zip)))
           (equal (zip->path zip)
                  nil)))

(defrulel zip-of-focus-and-nil-when-path-not-consp
  (implies (not (consp (zip->path zip)))
           (equal (zip (zip->focus zip) nil nil nil)
                  (zip-fix zip)))
  :use zip-of-zip-accessors
  :disable zip-of-zip-accessors)

(defruledl zip-ascend-to-left-frame-when-no-left-frames
  (implies (equal (zip-count-lefts (zip->path zip)) 0)
           (equal (zip-ascend-to-left-frame zip)
                  (zip-root (zip-plug zip))))
  :induct (zip-ascend-to-left-frame zip)
  :expand ((zip-count-lefts (zip->path zip)))
  :enable (zip-ascend-to-left-frame
           zip-root
           zip-plug))

(defruledl zip-ascend-to-right-frame-when-no-right-frames
  (implies (equal (zip-count-rights (zip->path zip)) 0)
           (equal (zip-ascend-to-right-frame zip)
                  (zip-root (zip-plug zip))))
  :induct (zip-ascend-to-right-frame zip)
  :expand ((zip-count-rights (zip->path zip)))
  :enable (zip-ascend-to-right-frame
           zip-root
           zip-plug))

(defruledl zip-descend-rightmost-of-ascend-to-left-frame-when-no-left-frames
  (implies (equal (zip-count-lefts (zip->path zip)) 0)
           (equal (zip-descend-rightmost (zip-ascend-to-left-frame zip))
                  (zip-descend-rightmost zip)))
  :induct (zip-ascend-to-left-frame zip)
  :expand ((zip-count-lefts (zip->path zip)))
  :enable (zip-ascend-to-left-frame
           zip-descend-rightmost-of-zip-ascend-one-when-not-from-left))

(defruledl zip-descend-leftmost-of-ascend-to-right-frame-when-no-right-frames
  (implies (equal (zip-count-rights (zip->path zip)) 0)
           (equal (zip-descend-leftmost (zip-ascend-to-right-frame zip))
                  (zip-descend-leftmost zip)))
  :induct (zip-ascend-to-right-frame zip)
  :expand ((zip-count-rights (zip->path zip)))
  :enable (zip-ascend-to-right-frame
           zip-descend-leftmost-of-zip-ascend-one-when-from-left))

(defrule zip-last-of-zip-plug-when-zip-at-last-p
  (implies (zip-at-last-p zip)
           (equal (zip-last (zip-plug zip))
                  (zip-fix zip)))
  :enable (zip-last
           zip-at-last-p)
  :use (zip-ascend-to-left-frame-when-no-left-frames
        zip-descend-rightmost-of-ascend-to-left-frame-when-no-left-frames))

(defrule zip-first-of-zip-plug-when-zip-at-first-p
  (implies (zip-at-first-p zip)
           (equal (zip-first (zip-plug zip))
                  (zip-fix zip)))
  :enable (zip-first
           zip-at-first-p)
  :use (zip-ascend-to-right-frame-when-no-right-frames
        zip-descend-leftmost-of-ascend-to-right-frame-when-no-right-frames))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-value ((zip zipp))
  :short "The value at the focus."
  (tree-element->val (tree->head (zip->focus zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-value-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-value zip0)
                  (zip-value zip1)))
  :rule-classes :congruence
  :enable zip-value)

;; The focus of a zipper occupies a contiguous run of the in-order sequence of
;; the whole tree, and what flanks that run is fixed by the path alone. The two
;; functions below name those flanks, cutting the sequence in three.
;;
;; The tree fold below is the one primitive; the list and oset flanks are
;; views of it, read off with @(tsee tree-in-order) and @(tsee tree-oset).

;; The sides as trees, built directly. A frame whose focus hangs as the right
;; child holds an element and a sibling subtree which precede the focus, and
;; they arrive ordered and heap-dominated: the element is an ancestor of
;; everything gathered so far, so a plain node placed over the sibling and the
;; accumulator is already a valid treap. No comparison or rotation is needed;
;; this is a split which keeps one half, along a path already traversed.

(define zip-path-tree-before ((path zip-frame-listp)
                              (acc treep))
  :returns (tree treep)
  :short "The elements which precede the focus subtree, as a tree atop an
          accumulator."
  (if (endp path)
      (tree-fix acc)
    (zip-path-tree-before
      (cdr path)
      (if (zip-frame->from-left (car path))
          acc
        (tree-node (zip-frame->elem (car path))
                   (zip-frame->sibling (car path))
                   acc))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-tree-after ((path zip-frame-listp)
                             (acc treep))
  :returns (tree treep)
  :short "The elements which follow the focus subtree, as a tree atop an
          accumulator."
  (if (endp path)
      (tree-fix acc)
    (zip-path-tree-after
      (cdr path)
      (if (zip-frame->from-left (car path))
          (tree-node (zip-frame->elem (car path))
                     acc
                     (zip-frame->sibling (car path)))
        acc)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-path-tree-before) (:t zip-path-tree-after)))

(defrule zip-path-tree-before-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (zip-path-tree-before path acc0)
                  (zip-path-tree-before path acc1)))
  :rule-classes :congruence
  :induct t
  :enable zip-path-tree-before)

(defrule zip-path-tree-after-when-tree-equiv-of-arg2-congruence
  (implies (tree-equiv acc0 acc1)
           (equal (zip-path-tree-after path acc0)
                  (zip-path-tree-after path acc1)))
  :rule-classes :congruence
  :induct t
  :enable zip-path-tree-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-tree-before ((zip zipp))
  :returns (tree treep)
  :short "The elements which precede the cursor, as a tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus, and
      so @($O(\\log(n))$) over a @(see treeset). One node is built per
      contributing frame; every subtree hangs off the original tree
      unchanged."))
  (zip-path-tree-before (zip->path zip)
                        (tree->left (zip->focus zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-tree-after ((zip zipp))
  :returns (tree treep)
  :short "The elements which follow the cursor, as a tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth of the focus, and
      so @($O(\\log(n))$) over a @(see treeset). One node is built per
      contributing frame; every subtree hangs off the original tree
      unchanged."))
  (zip-path-tree-after (zip->path zip)
                       (tree->right (zip->focus zip))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-tree-before) (:t zip-tree-after)))

(defrule zip-tree-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-tree-before zip0)
                  (zip-tree-before zip1)))
  :rule-classes :congruence
  :enable zip-tree-before)

(defrule zip-tree-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-tree-after zip0)
                  (zip-tree-after zip1)))
  :rule-classes :congruence
  :enable zip-tree-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The recursive list flanks survive only as local scaffolding: the exported
;; functions are views of the tree fold, and the lemmas which relate a fold to
;; its seed are proven against the recursion and then transferred.

(local
  (define zip-path-before-rec ((path zip-frame-listp))
    :returns (list true-listp :rule-classes :type-prescription)
    :verify-guards nil
    (if (endp path)
        nil
      (append (zip-path-before-rec (cdr path))
              (if (zip-frame->from-left (car path))
                  nil
                (append (tree-in-order (zip-frame->sibling (car path)))
                        (list (tree-element->val
                                (zip-frame->elem (car path))))))))))

(local
  (define zip-path-after-rec ((path zip-frame-listp))
    :returns (list true-listp :rule-classes :type-prescription)
    :verify-guards nil
    (if (endp path)
        nil
      (append (if (zip-frame->from-left (car path))
                  (cons (tree-element->val (zip-frame->elem (car path)))
                        (tree-in-order (zip-frame->sibling (car path))))
                nil)
              (zip-path-after-rec (cdr path))))))

(defruledl tree-in-order-of-zip-path-tree-before-rec
  (equal (tree-in-order (zip-path-tree-before path acc))
         (append (zip-path-before-rec path)
                 (tree-in-order acc)))
  :induct (zip-path-tree-before path acc)
  :enable (zip-path-tree-before
           zip-path-before-rec
           tree-in-order))

(defruledl tree-in-order-of-zip-path-tree-after-rec
  (equal (tree-in-order (zip-path-tree-after path acc))
         (append (tree-in-order acc)
                 (zip-path-after-rec path)))
  :induct (zip-path-tree-after path acc)
  :enable (zip-path-tree-after
           zip-path-after-rec
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-before ((path zip-frame-listp))
  (declare (xargs :type-prescription :none))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which precede the focus subtree, in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "A view of the tree fold: the in-order sequence of the side built over an
      empty seed."))
  (tree-in-order (zip-path-tree-before path nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-after ((path zip-frame-listp))
  (declare (xargs :type-prescription :none))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which follow the focus subtree, in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror of @(tsee zip-path-before)."))
  (tree-in-order (zip-path-tree-after path nil)))

;;;;;;;;;;;;;;;;;;;;

(defruledl zip-path-before-becomes-rec
  (equal (zip-path-before path)
         (zip-path-before-rec path))
  :enable (zip-path-before
           tree-in-order-of-zip-path-tree-before-rec))

(defruledl zip-path-after-becomes-rec
  (equal (zip-path-after path)
         (zip-path-after-rec path))
  :enable (zip-path-after
           tree-in-order-of-zip-path-tree-after-rec))

;; Reading a fold over any seed splits into the flank and the seed's own
;; sequence. These are the general forms; the definitions above are the
;; empty-seed instances.

(defrule tree-in-order-of-zip-path-tree-before
  (equal (tree-in-order (zip-path-tree-before path acc))
         (append (zip-path-before path)
                 (tree-in-order acc)))
  :enable (zip-path-before-becomes-rec
           tree-in-order-of-zip-path-tree-before-rec))

(defrule tree-in-order-of-zip-path-tree-after
  (equal (tree-in-order (zip-path-tree-after path acc))
         (append (tree-in-order acc)
                 (zip-path-after path)))
  :enable (zip-path-after-becomes-rec
           tree-in-order-of-zip-path-tree-after-rec))

;; Each general rule rewrites a read of the fold into the view, and the view's
;; definition unfolds back into a read of the fold. Enabling either
;; definition together with its rule loops, so proofs pick one.

(local
  (theory-invariant
    (incompatible! (:rewrite tree-in-order-of-zip-path-tree-before)
                   (:definition zip-path-before))))

(local
  (theory-invariant
    (incompatible! (:rewrite tree-in-order-of-zip-path-tree-after)
                   (:definition zip-path-after))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-path-before-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-path-before path)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable (zip-path-before-becomes-rec
           zip-path-before-rec))

(defrule zip-path-after-when-not-consp-cheap
  (implies (not (consp path))
           (equal (zip-path-after path)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable (zip-path-after-becomes-rec
           zip-path-after-rec))

(defrule zip-path-before-of-cons
  (equal (zip-path-before (cons frame path))
         (append (zip-path-before path)
                 (if (zip-frame->from-left frame)
                     nil
                   (append (tree-in-order (zip-frame->sibling frame))
                           (list (tree-element->val
                                   (zip-frame->elem frame)))))))
  :enable (zip-path-before-becomes-rec
           zip-path-before-rec))

(defrule zip-path-after-of-cons
  (equal (zip-path-after (cons frame path))
         (append (if (zip-frame->from-left frame)
                     (cons (tree-element->val (zip-frame->elem frame))
                           (tree-in-order (zip-frame->sibling frame)))
                   nil)
                 (zip-path-after path)))
  :enable (zip-path-after-becomes-rec
           zip-path-after-rec))

;; A path with no left frames has nothing to the right of the focus, and
;; symmetrically. This is what the cached counts are testing.

(defrule zip-path-after-when-zip-count-lefts-zero
  (implies (equal (zip-count-lefts path) 0)
           (equal (zip-path-after path)
                  nil))
  :induct (zip-path-after-rec path)
  :enable (zip-path-after-rec))

(defrule zip-path-before-when-zip-count-rights-zero
  (implies (equal (zip-count-rights path) 0)
           (equal (zip-path-before path)
                  nil))
  :induct (zip-path-before-rec path)
  :enable (zip-path-before-rec))

;;;;;;;;;;;;;;;;;;;;

(defrule tree-in-order-of-zip-path-plug
  (equal (tree-in-order (zip-path-plug path tree))
         (append (zip-path-before path)
                 (tree-in-order tree)
                 (zip-path-after path)))
  :induct (zip-path-plug path tree)
  :enable (zip-path-plug
           zip-path-before-rec
           zip-path-after-rec
           zip-frame-plug
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The path accounts for everything outside the focus subtree. Within it, the
;; focus's own left subtree precedes the cursor and its right subtree follows,
;; so the two combine to split the sequence at the cursor rather than at the
;; subtree.

(define zip-before ((zip zipp))
  (declare (xargs :type-prescription :none))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which precede the cursor, in order."
  (tree-in-order (zip-path-tree-before (zip->path zip)
                                       (tree->left (zip->focus zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-after ((zip zipp))
  (declare (xargs :type-prescription :none))
  :returns (list true-listp :rule-classes :type-prescription)
  :short "The values which follow the cursor, in order."
  (tree-in-order (zip-path-tree-after (zip->path zip)
                                      (tree->right (zip->focus zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-before zip0)
                  (zip-before zip1)))
  :rule-classes :congruence
  :enable zip-before)

(defrule zip-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-after zip0)
                  (zip-after zip1)))
  :rule-classes :congruence
  :enable zip-after)

;; A side tree is empty exactly when its sequence is, and counting it is
;; measuring its sequence.

(defrule tree-empty-p-of-zip-tree-before
  (equal (tree-empty-p (zip-tree-before zip))
         (not (consp (zip-before zip))))
  :enable (not
           zip-before
           zip-tree-before)
  :disable tree-in-order-of-zip-path-tree-before)

(defrule tree-empty-p-of-zip-tree-after
  (equal (tree-empty-p (zip-tree-after zip))
         (not (consp (zip-after zip))))
  :enable (not
           zip-after
           zip-tree-after)
  :disable tree-in-order-of-zip-path-tree-after)

(defrule tree-nodes-count-of-zip-tree-before
  (equal (tree-nodes-count (zip-tree-before zip))
         (len (zip-before zip)))
  :enable (zip-before
           zip-tree-before)
  :disable tree-in-order-of-zip-path-tree-before)

(defrule tree-nodes-count-of-zip-tree-after
  (equal (tree-nodes-count (zip-tree-after zip))
         (len (zip-after zip)))
  :enable (zip-after
           zip-tree-after)
  :disable tree-in-order-of-zip-path-tree-after)

;;;;;;;;;;;;;;;;;;;;

;; The in-order sequence of the whole tree, cut at the focus subtree. This is
;; the form which rewrites unconditionally, and every law below is read off of
;; it.

(defrule tree-in-order-of-zip-plug
  (equal (tree-in-order (zip-plug zip))
         (append (zip-path-before (zip->path zip))
                 (tree-in-order (zip->focus zip))
                 (zip-path-after (zip->path zip))))
  :enable zip-plug)

;; The same sequence, cut at the cursor instead: since a zipper is always at an
;; element, the cut always splits the sequence around one value.

(defruled tree-in-order-of-zip-plug-split-at-cursor
  (equal (tree-in-order (zip-plug zip))
         (append (zip-before zip)
                 (cons (zip-value zip)
                       (zip-after zip))))
  :enable (zip-before
           zip-after
           zip-value
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;

;; Cardinality, read off of the same two decompositions by taking lengths.

(defrule tree-nodes-count-of-zip-plug
  (equal (tree-nodes-count (zip-plug zip))
         (+ (len (zip-path-before (zip->path zip)))
            (tree-nodes-count (zip->focus zip))
            (len (zip-path-after (zip->path zip)))))
  :use ((:instance len-of-tree-in-order (tree (zip-plug zip)))
        (:instance len-of-tree-in-order (tree (zip->focus zip))))
  :disable len-of-tree-in-order)

(defruled tree-nodes-count-of-zip-plug-split-at-cursor
  (equal (tree-nodes-count (zip-plug zip))
         (+ (len (zip-before zip))
            1
            (len (zip-after zip))))
  :use (:instance len-of-tree-in-order (tree (zip-plug zip)))
  :enable tree-in-order-of-zip-plug-split-at-cursor
  :disable len-of-tree-in-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The two sides as osets, built with oset primitives. Unlike @(tsee
;; zip-before) and @(tsee zip-after), which read the two sides off as slices
;; of the in-order sequence and are only osets when the tree is a search tree,
;; these are @(tsee set::setp) structurally, for any zipper at all. Over a
;; search tree the two versions are the same object; see @(tsee
;; zip-oset-before-becomes-zip-before). The oset versions are the logical
;; form: statements phrased over them face the mature oset theory.

(define zip-path-oset-before ((path zip-frame-listp))
  :returns (oset set::setp)
  :short "The elements which precede the focus subtree, as an oset."
  (tree-oset (zip-path-tree-before path nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-oset-after ((path zip-frame-listp))
  :returns (oset set::setp)
  :short "The elements which follow the focus subtree, as an oset."
  (tree-oset (zip-path-tree-after path nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-oset-before ((zip zipp))
  :returns (oset set::setp)
  :short "The elements which precede the cursor, as an oset."
  (tree-oset (zip-path-tree-before (zip->path zip)
                                   (tree->left (zip->focus zip)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-oset-after ((zip zipp))
  :returns (oset set::setp)
  :short "The elements which follow the cursor, as an oset."
  (tree-oset (zip-path-tree-after (zip->path zip)
                                  (tree->right (zip->focus zip)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t zip-path-oset-before) (:t zip-path-oset-after)
                    (:t zip-oset-before) (:t zip-oset-after)))

(defrule zip-oset-before-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-oset-before zip0)
                  (zip-oset-before zip1)))
  :rule-classes :congruence
  :enable zip-oset-before)

(defrule zip-oset-after-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-oset-after zip0)
                  (zip-oset-after zip1)))
  :rule-classes :congruence
  :enable zip-oset-after)

;; Membership in each oset is membership in the corresponding sequence, with
;; no hypothesis: the fold inserts exactly the elements the sequence reads
;; off, whether or not the tree is ordered.

(defrule in-of-zip-path-oset-before
  (iff (set::in x (zip-path-oset-before path))
       (member-equal x (zip-path-before path)))
  :enable (zip-path-oset-before
           zip-path-before)
  :disable tree-in-order-of-zip-path-tree-before)

(defrule in-of-zip-path-oset-after
  (iff (set::in x (zip-path-oset-after path))
       (member-equal x (zip-path-after path)))
  :enable (zip-path-oset-after
           zip-path-after)
  :disable tree-in-order-of-zip-path-tree-after)

(defrule in-of-zip-oset-before
  (iff (set::in x (zip-oset-before zip))
       (member-equal x (zip-before zip)))
  :enable (zip-oset-before
           zip-before)
  :disable tree-in-order-of-zip-path-tree-before)

(defrule in-of-zip-oset-after
  (iff (set::in x (zip-oset-after zip))
       (member-equal x (zip-after zip)))
  :enable (zip-oset-after
           zip-after)
  :disable tree-in-order-of-zip-path-tree-after)

;; Each oset is empty exactly when its sequence is: a member of one is a
;; member of the other, and an oset with no members is nil.

(defrule emptyp-of-zip-oset-before
  (equal (set::emptyp (zip-oset-before zip))
         (not (consp (zip-before zip))))
  :use ((:instance in-of-zip-oset-before
                   (x (set::head (zip-oset-before zip))))
        (:instance in-of-zip-oset-before
                   (x (car (zip-before zip))))
        (:instance set::in-head
                   (set::x (zip-oset-before zip))))
  :disable (in-of-zip-oset-before
            set::in-head))

(defrule emptyp-of-zip-oset-after
  (equal (set::emptyp (zip-oset-after zip))
         (not (consp (zip-after zip))))
  :use ((:instance in-of-zip-oset-after
                   (x (set::head (zip-oset-after zip))))
        (:instance in-of-zip-oset-after
                   (x (car (zip-after zip))))
        (:instance set::in-head
                   (set::x (zip-oset-after zip))))
  :disable (in-of-zip-oset-after
            set::in-head))

;; Over a search tree the sequences are osets themselves: each is a
;; contiguous slice of the in-order sequence, which is then ordered and
;; duplicate-free.

(defrule osetp-of-zip-before-when-bstp
  (implies (bstp (zip-plug zip))
           (set::setp (zip-before zip)))
  :enable tree-in-order-of-zip-plug-split-at-cursor
  :use ((:instance osetp-of-tree-in-order-when-bstp (tree (zip-plug zip)))
        (:instance data::setp-of-prefix-when-osetp-of-append
                   (data::x (zip-before zip))
                   (data::y (cons (zip-value zip) (zip-after zip)))))
  :disable (osetp-of-tree-in-order-when-bstp))

(defrule osetp-of-zip-after-when-bstp
  (implies (bstp (zip-plug zip))
           (set::setp (zip-after zip)))
  :enable tree-in-order-of-zip-plug-split-at-cursor
  :use ((:instance osetp-of-tree-in-order-when-bstp (tree (zip-plug zip)))
        (:instance data::setp-of-suffix-when-osetp-of-append
                   (data::x (zip-before zip))
                   (data::y (cons (zip-value zip) (zip-after zip))))
        (:instance data::setp-of-cdr-when-osetp
                   (data::l (cons (zip-value zip) (zip-after zip)))))
  :disable (osetp-of-tree-in-order-when-bstp))

;; So over a search tree the two versions are not merely equivalent but the
;; same object: both are osets, and they have the same members. This is the
;; bridge a proof crosses to trade sequence facts for set facts.

(defruled zip-oset-before-becomes-zip-before
  (implies (bstp (zip-plug zip))
           (equal (zip-oset-before zip)
                  (zip-before zip)))
  :enable (set::in-to-member
           set::double-containment
           set::pick-a-point-subset-strategy))

(defruled zip-oset-after-becomes-zip-after
  (implies (bstp (zip-plug zip))
           (equal (zip-oset-after zip)
                  (zip-after zip)))
  :enable (set::in-to-member
           set::double-containment
           set::pick-a-point-subset-strategy))

;; The two osets as order filters of the whole set: over a search tree, what
;; lies on each side of the cursor is exactly the elements on that side of the
;; value in the @(tsee <<) order. This is what ties the geometry of a zipper
;; to the order of the set, and every ordering law downstream is a
;; consequence.

(defrule in-of-zip-oset-before-when-bstp
  (implies (bstp (zip-plug zip))
           (equal (set::in x (zip-oset-before zip))
                  (and (tree-in x (zip-plug zip))
                       (<< x (zip-value zip)))))
  :enable (tree-in-order-of-zip-plug-split-at-cursor
           data::<<-rules)
  :use ((:instance member-equal-of-tree-in-order-under-iff
                   (tree (zip-plug zip)))
        (:instance osetp-of-tree-in-order-when-bstp
                   (tree (zip-plug zip)))
        (:instance data::<<-across-append-when-osetp
                   (data::a (zip-before zip))
                   (data::b (cons (zip-value zip) (zip-after zip)))
                   (data::x x))
        (:instance data::<<-of-car-when-member-equal-of-cdr
                   (data::l (cons (zip-value zip) (zip-after zip)))
                   (data::x x))
        (:instance data::setp-of-suffix-when-osetp-of-append
                   (data::x (zip-before zip))
                   (data::y (cons (zip-value zip) (zip-after zip)))))
  :disable (member-equal-of-tree-in-order-under-iff
            osetp-of-tree-in-order-when-bstp))

(defrule in-of-zip-oset-after-when-bstp
  (implies (bstp (zip-plug zip))
           (equal (set::in x (zip-oset-after zip))
                  (and (tree-in x (zip-plug zip))
                       (<< (zip-value zip) x))))
  :enable (tree-in-order-of-zip-plug-split-at-cursor
           data::<<-rules)
  :use ((:instance member-equal-of-tree-in-order-under-iff
                   (tree (zip-plug zip)))
        (:instance osetp-of-tree-in-order-when-bstp
                   (tree (zip-plug zip)))
        (:instance data::<<-across-append-when-osetp
                   (data::a (zip-before zip))
                   (data::b (cons (zip-value zip) (zip-after zip)))
                   (data::x x))
        (:instance data::<<-of-car-when-member-equal-of-cdr
                   (data::l (cons (zip-value zip) (zip-after zip)))
                   (data::x x))
        (:instance data::setp-of-suffix-when-osetp-of-append
                   (data::x (zip-before zip))
                   (data::y (cons (zip-value zip) (zip-after zip)))))
  :disable (member-equal-of-tree-in-order-under-iff
            osetp-of-tree-in-order-when-bstp))

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

(defruledl zip-before-of-zip-descend-leftmost
  (equal (zip-before (zip-descend-leftmost zip))
         (zip-path-before (zip->path zip)))
  :induct (zip-descend-leftmost zip)
  :enable (zip-descend-leftmost
           zip-before))

(defruledl zip-path-before-of-path-of-zip-descend-right
  (equal (zip-path-before (zip->path (zip-descend-right zip)))
         (append (zip-before zip)
                 (list (zip-value zip))))
  :enable (zip-before
           zip-value))

(defruledl zip-before-of-zip-ascend-to-left-frame
  (implies (not (equal (zip-count-lefts (zip->path zip)) 0))
           (equal (zip-before (zip-ascend-to-left-frame zip))
                  (append (zip-path-before (zip->path zip))
                          (tree-in-order (zip->focus zip)))))
  :induct (zip-ascend-to-left-frame zip)
  :expand ((zip-count-lefts (zip->path zip))
           (zip-path-before-rec (zip->path zip)))
  :enable (zip-ascend-to-left-frame
           zip-before
           zip-path-before-becomes-rec
           zip-frame-plug
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-before-of-zip-next
  (implies (not (zip-at-last-p zip))
           (equal (zip-before (zip-next zip))
                  (append (zip-before zip)
                          (list (zip-value zip)))))
  :expand ((tree-in-order (zip->focus zip)))
  :enable (zip-next
           zip-at-last-p
           zip-before
           zip-value
           zip-before-of-zip-descend-leftmost
           zip-before-of-zip-ascend-to-left-frame))

;; What follows the cursor loses its first value, which is the one the move
;; lands on. Both fall out of the law above by cancelling the common prefix in
;; the two decompositions.

(defrule zip-after-of-zip-next
  (implies (not (zip-at-last-p zip))
           (equal (zip-after (zip-next zip))
                  (cdr (zip-after zip))))
  :use (tree-in-order-of-zip-plug-split-at-cursor
        (:instance tree-in-order-of-zip-plug-split-at-cursor
                   (zip (zip-next zip)))))

(defrule zip-value-of-zip-next
  (implies (not (zip-at-last-p zip))
           (equal (zip-value (zip-next zip))
                  (car (zip-after zip))))
  :use (tree-in-order-of-zip-plug-split-at-cursor
        (:instance tree-in-order-of-zip-plug-split-at-cursor
                   (zip (zip-next zip)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Having nothing before you is being at the first element, and having nothing
;; after you is being at the last. A frame the focus hangs to the right of
;; contributes at least its own node, so a path which contributes nothing has
;; no such frame.

(defruledl zip-count-rights-when-not-consp-of-zip-path-before
  (implies (not (consp (zip-path-before path)))
           (equal (zip-count-rights path) 0))
  :induct (zip-path-before-rec path)
  :enable (zip-path-before-rec))

(defruledl zip-count-lefts-when-not-consp-of-zip-path-after
  (implies (not (consp (zip-path-after path)))
           (equal (zip-count-lefts path) 0))
  :induct (zip-path-after-rec path)
  :enable (zip-path-after-rec))

(defrule zip-before-when-zip-at-first-p
  (implies (zip-at-first-p zip)
           (equal (zip-before zip)
                  nil))
  :enable (zip-at-first-p
           zip-before))

(defrule zip-after-when-zip-at-last-p
  (implies (zip-at-last-p zip)
           (equal (zip-after zip)
                  nil))
  :enable (zip-at-last-p
           zip-after))

(defrule zip-at-first-p-when-not-consp-of-zip-before
  (implies (not (consp (zip-before zip)))
           (zip-at-first-p zip))
  :enable (zip-at-first-p
           zip-before
           zip-count-rights-when-not-consp-of-zip-path-before))

(defrule zip-at-last-p-when-not-consp-of-zip-after
  (implies (not (consp (zip-after zip)))
           (zip-at-last-p zip))
  :enable (zip-at-last-p
           zip-after
           zip-count-lefts-when-not-consp-of-zip-path-after))

(defrule not-zip-at-first-p-when-consp-of-zip-before
  (implies (consp (zip-before zip))
           (not (zip-at-first-p zip)))
  :use zip-before-when-zip-at-first-p
  :disable zip-before-when-zip-at-first-p)

(defrule not-zip-at-last-p-when-consp-of-zip-after
  (implies (consp (zip-after zip))
           (not (zip-at-last-p zip)))
  :use zip-after-when-zip-at-last-p
  :disable zip-after-when-zip-at-last-p)

;; The same fact by forward chaining. The rewrite form above cannot relieve
;; this hypothesis for a rule whose conclusion is about @(tsee zip-after) of a
;; move: doing so would rewrite @(tsee zip-at-last-p) into a term mentioning
;; @(tsee zip-after), which the ancestors check blocks as possibly looping.
;; Forward chaining puts the fact in the context first, so no backchaining is
;; needed.

(defrule not-zip-at-last-p-when-consp-of-zip-after-forward-chaining
  (implies (consp (zip-after zip))
           (not (zip-at-last-p zip)))
  :rule-classes :forward-chaining)

;; The two ends as tests on the sequences alone. Left disabled, since either
;; direction on its own is the cheaper rule; this form is for proofs which know
;; two zippers have the same sequence and need them to be at an end together.

(defruled zip-at-first-p-becomes-not-consp-of-zip-before
  (equal (zip-at-first-p zip)
         (not (consp (zip-before zip))))
  :cases ((consp (zip-before zip))))

(defruled zip-at-last-p-becomes-not-consp-of-zip-after
  (equal (zip-at-last-p zip)
         (not (consp (zip-after zip))))
  :cases ((consp (zip-after zip))))

;; The mirror of the ordering law, read backwards.

(defrule zip-before-of-zip-prev
  (implies (not (zip-at-first-p zip))
           (equal (zip-before zip)
                  (append (zip-before (zip-prev zip))
                          (list (zip-value (zip-prev zip))))))
  :use (:instance zip-before-of-zip-next
                  (zip (zip-prev zip)))
  :disable zip-before-of-zip-next)

;; What follows a step back gains the value stepped away from, at its front.
;; Read off the round trip: what follows the previous position loses its head
;; to a forward step, and that head is the value that step lands on.

(defrule zip-after-of-zip-prev
  (implies (not (zip-at-first-p zip))
           (equal (zip-after (zip-prev zip))
                  (cons (zip-value zip)
                        (zip-after zip))))
  :use ((:instance zip-after-of-zip-next (zip (zip-prev zip)))
        (:instance zip-value-of-zip-next (zip (zip-prev zip)))
        (:instance zip-at-last-p-when-not-consp-of-zip-after
                   (zip (zip-prev zip))))
  :disable (zip-after-of-zip-next
            zip-value-of-zip-next
            zip-at-last-p-when-not-consp-of-zip-after
            acl2::cons-car-cdr))

;;;;;;;;;;;;;;;;;;;;

;; UNIQUENESS. A zipper is determined by the tree it is a cursor into together
;; with what follows the cursor in that tree. Note that no @(tsee bstp)
;; hypothesis is needed: this is structural, and holds of any tree.
;;
;; The proof walks both zippers forward in step. Each step drops one value from
;; what follows, so the two stay in agreement, and the walk ends at the last
;; element, where @(tsee zip-last) already pins the zipper down. Undoing
;; the walk with @(tsee zip-prev) carries the equality back to the start.

(local
 (defun zip-position-induction (zip1 zip2)
   (declare (xargs :measure (len (zip-after zip1))))
   (if (zip-at-last-p zip1)
       (list zip1 zip2)
     (zip-position-induction (zip-next zip1)
                             (zip-next zip2)))))

(defrule zip-uniqueness-when-zip-after-equal
  (implies (and (equal (zip-plug zip1) (zip-plug zip2))
                (equal (zip-after zip1) (zip-after zip2)))
           (equal (zip-fix zip1) (zip-fix zip2)))
  :rule-classes nil
  :hints (("Goal"
           :induct (zip-position-induction zip1 zip2)
           :in-theory (enable zip-at-last-p-becomes-not-consp-of-zip-after
                              zip-after-of-zip-next))
          ;; Both cases need the round trip named at a specific pair of
          ;; zippers, which no rewrite can supply: the base case has no
          ;; @(tsee zip-prev) term to match on, and the step case must undo a
          ;; move to recover the zippers from their successors. Keyed on
          ;; stability rather than on subgoal names, which shift.
          (and stable-under-simplificationp
               '(:use ((:instance zip-prev-of-zip-next (zip zip1))
                       (:instance zip-prev-of-zip-next (zip zip2))
                       (:instance zip-last-of-zip-plug-when-zip-at-last-p
                                  (zip zip1))
                       (:instance zip-last-of-zip-plug-when-zip-at-last-p
                                  (zip zip2)))
                 :in-theory (e/d (zip-at-last-p-becomes-not-consp-of-zip-after
                                  zip-after-of-zip-next)
                                 (zip-prev-of-zip-next
                                  zip-last-of-zip-plug-when-zip-at-last-p))))))

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
  :disable acl2::len-of-cdr)

(defruledl not-equal-of-append-of-singleton
  (not (equal x (append x (list y))))
  :use (:instance acl2::len-of-append (acl2::x x) (acl2::y (list y)))
  :disable acl2::len-of-append)

(defrule zip-next-identity-iff-zip-at-last-p
  (equal (equal (zip-next zip) (zip-fix zip))
         (zip-at-last-p zip))
  :use zip-after-of-zip-next
  :disable zip-after-of-zip-next
  :cases ((consp (zip-after zip))))

(defrule zip-prev-identity-iff-zip-at-first-p
  (equal (equal (zip-prev zip) (zip-fix zip))
         (zip-at-first-p zip))
  :use zip-before-of-zip-prev
  :disable zip-before-of-zip-prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The built trees hold exactly the elements of the oset sides.

(defrule tree-in-of-zip-path-tree-before
  (equal (tree-in x (zip-path-tree-before path acc))
         (or (set::in x (zip-path-oset-before path))
             (tree-in x acc)))
  :use ((:instance member-equal-of-tree-in-order-under-iff
                   (tree (zip-path-tree-before path acc)))
        (:instance member-equal-of-tree-in-order-under-iff
                   (tree (zip-path-tree-before path nil)))
        (:instance member-equal-of-tree-in-order-under-iff
                   (tree acc)))
  :disable member-equal-of-tree-in-order-under-iff)

(defrule tree-in-of-zip-path-tree-after
  (equal (tree-in x (zip-path-tree-after path acc))
         (or (set::in x (zip-path-oset-after path))
             (tree-in x acc)))
  :use ((:instance member-equal-of-tree-in-order-under-iff
                   (tree (zip-path-tree-after path acc)))
        (:instance member-equal-of-tree-in-order-under-iff
                   (tree (zip-path-tree-after path nil)))
        (:instance member-equal-of-tree-in-order-under-iff
                   (tree acc)))
  :disable member-equal-of-tree-in-order-under-iff)

(defrule tree-in-of-zip-tree-before
  (equal (tree-in x (zip-tree-before zip))
         (set::in x (zip-oset-before zip)))
  :enable (zip-tree-before
           zip-oset-before))

(defrule tree-in-of-zip-tree-after
  (equal (tree-in x (zip-tree-after zip))
         (set::in x (zip-oset-after zip)))
  :enable (zip-tree-after
           zip-oset-after))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Both invariants pass to the built trees. Each fact an added node needs is
;; inherited from the plug: the frame element bounds its sibling directly, and
;; bounds the accumulator because the accumulator stays a subset of the
;; subtree the focus came from.

;; What the plug knows about a plugged node, in the syntactic form the
;; induction below leaves in its wake.

(defruledl bstp-parts-of-zip-path-plug-of-tree-node
  (implies (bstp (zip-path-plug path (tree-node head left right)))
           (and (bstp left)
                (bstp right)
                (<<-all-l left (tree-element->val head))
                (<<-all-r (tree-element->val head) right)))
  :use (:instance bstp-of-arg2-when-bstp-of-zip-path-plug
                  (tree (tree-node head left right)))
  :disable bstp-of-arg2-when-bstp-of-zip-path-plug)

(defruledl heapp-parts-of-zip-path-plug-of-tree-node
  (implies (heapp (zip-path-plug path (tree-node head left right)))
           (and (heapp left)
                (heapp right)
                (heap<-all-l left (tree-element->val head))
                (heap<-all-l right (tree-element->val head))))
  :use (:instance heapp-of-arg2-when-heapp-of-zip-path-plug
                  (tree (tree-node head left right)))
  :disable heapp-of-arg2-when-heapp-of-zip-path-plug)

(defruledl <<-all-r-of-elem-when-subset-of-right
  (implies (and (tree-subset-p acc right)
                (bstp (zip-path-plug path (tree-node head left right))))
           (<<-all-r (tree-element->val head) acc))
  :use ((:instance <<-all-r-when-tree-subset-p
                   (x (tree-element->val head))
                   (tree right))
        (:instance bstp-of-arg2-when-bstp-of-zip-path-plug
                   (tree (tree-node head left right))))
  :disable bstp-of-arg2-when-bstp-of-zip-path-plug)

(defruledl <<-all-l-of-elem-when-subset-of-left
  (implies (and (tree-subset-p acc left)
                (bstp (zip-path-plug path (tree-node head left right))))
           (<<-all-l acc (tree-element->val head)))
  :use ((:instance <<-all-l-when-tree-subset-p
                   (x (tree-element->val head))
                   (tree left))
        (:instance bstp-of-arg2-when-bstp-of-zip-path-plug
                   (tree (tree-node head left right))))
  :disable bstp-of-arg2-when-bstp-of-zip-path-plug)

(defruledl heap<-all-l-when-subset-of-right
  (implies (and (tree-subset-p acc right)
                (heapp (zip-path-plug path (tree-node head left right))))
           (heap<-all-l acc (tree-element->val head)))
  :use ((:instance heap<-all-l-when-tree-subset-p
                   (x (tree-element->val head))
                   (tree right))
        (:instance heapp-of-arg2-when-heapp-of-zip-path-plug
                   (tree (tree-node head left right))))
  :disable heapp-of-arg2-when-heapp-of-zip-path-plug)

(defruledl heap<-all-l-when-subset-of-left
  (implies (and (tree-subset-p acc left)
                (heapp (zip-path-plug path (tree-node head left right))))
           (heap<-all-l acc (tree-element->val head)))
  :use ((:instance heap<-all-l-when-tree-subset-p
                   (x (tree-element->val head))
                   (tree left))
        (:instance heapp-of-arg2-when-heapp-of-zip-path-plug
                   (tree (tree-node head left right))))
  :disable heapp-of-arg2-when-heapp-of-zip-path-plug)

;; The accumulator stays a subset as both it and the reference subtree are
;; wrapped under the same frame.

(defruledl tree-subset-p-of-tree-nodes-sharing-left
  (implies (tree-subset-p acc tree)
           (tree-subset-p (tree-node head sibling acc)
                          (tree-node head sibling tree)))
  :enable (tree-subset-p
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right))

(defruledl tree-subset-p-of-tree-nodes-sharing-right
  (implies (tree-subset-p acc tree)
           (tree-subset-p (tree-node head acc sibling)
                          (tree-node head tree sibling)))
  :enable (tree-subset-p
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right))

;; The builders and the plug ascend the path together.

(local
  (define zip-path-tree-before-induction ((path zip-frame-listp)
                                          (tree treep)
                                          (acc treep))
    :verify-guards nil
    :enabled t
    (if (endp path)
        (list tree acc)
      (zip-path-tree-before-induction
        (cdr path)
        (zip-frame-plug (car path) tree)
        (if (zip-frame->from-left (car path))
            acc
          (tree-node (zip-frame->elem (car path))
                     (zip-frame->sibling (car path))
                     acc))))))

(local
  (define zip-path-tree-after-induction ((path zip-frame-listp)
                                         (tree treep)
                                         (acc treep))
    :verify-guards nil
    :enabled t
    (if (endp path)
        (list tree acc)
      (zip-path-tree-after-induction
        (cdr path)
        (zip-frame-plug (car path) tree)
        (if (zip-frame->from-left (car path))
            (tree-node (zip-frame->elem (car path))
                       acc
                       (zip-frame->sibling (car path)))
          acc)))))

(defruledl bstp-of-zip-path-tree-before
  (implies (and (bstp (zip-path-plug path tree))
                (bstp acc)
                (tree-subset-p acc tree))
           (bstp (zip-path-tree-before path acc)))
  :induct (zip-path-tree-before-induction path tree acc)
  :enable (zip-path-tree-before
           zip-path-plug
           zip-frame-plug
           bstp-parts-of-zip-path-plug-of-tree-node
           <<-all-r-of-elem-when-subset-of-right
           tree-subset-p-of-tree-nodes-sharing-left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)
  :disable (tree-element-elim
            zip-frame-elim
            tree-node-elim))

(defruledl heapp-of-zip-path-tree-before
  (implies (and (heapp (zip-path-plug path tree))
                (heapp acc)
                (tree-subset-p acc tree))
           (heapp (zip-path-tree-before path acc)))
  :induct (zip-path-tree-before-induction path tree acc)
  :enable (zip-path-tree-before
           zip-path-plug
           zip-frame-plug
           heapp-parts-of-zip-path-plug-of-tree-node
           heap<-all-l-when-subset-of-right
           tree-subset-p-of-tree-nodes-sharing-left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)
  :disable (tree-element-elim
            zip-frame-elim
            tree-node-elim))

(defruledl bstp-of-zip-path-tree-after
  (implies (and (bstp (zip-path-plug path tree))
                (bstp acc)
                (tree-subset-p acc tree))
           (bstp (zip-path-tree-after path acc)))
  :induct (zip-path-tree-after-induction path tree acc)
  :enable (zip-path-tree-after
           zip-path-plug
           zip-frame-plug
           bstp-parts-of-zip-path-plug-of-tree-node
           <<-all-l-of-elem-when-subset-of-left
           tree-subset-p-of-tree-nodes-sharing-right
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)
  :disable (tree-element-elim
            zip-frame-elim
            tree-node-elim))

(defruledl heapp-of-zip-path-tree-after
  (implies (and (heapp (zip-path-plug path tree))
                (heapp acc)
                (tree-subset-p acc tree))
           (heapp (zip-path-tree-after path acc)))
  :induct (zip-path-tree-after-induction path tree acc)
  :enable (zip-path-tree-after
           zip-path-plug
           zip-frame-plug
           heapp-parts-of-zip-path-plug-of-tree-node
           heap<-all-l-when-subset-of-left
           tree-subset-p-of-tree-nodes-sharing-right
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->left
           tree-subset-p-when-tree-subset-p-of-arg1-and-tree->right)
  :disable (tree-element-elim
            zip-frame-elim
            tree-node-elim))

;;;;;;;;;;;;;;;;;;;;

(defrule bstp-of-zip-tree-before-when-bstp-of-zip-plug
  (implies (bstp (zip-plug zip))
           (bstp (zip-tree-before zip)))
  :enable (zip-tree-before
           zip-plug
           bstp-of-zip-path-tree-before
           bstp-of-tree->left-when-bstp))

(defrule heapp-of-zip-tree-before-when-heapp-of-zip-plug
  (implies (heapp (zip-plug zip))
           (heapp (zip-tree-before zip)))
  :enable (zip-tree-before
           zip-plug
           heapp-of-zip-path-tree-before
           heapp-of-tree->left-when-heapp))

(defrule bstp-of-zip-tree-after-when-bstp-of-zip-plug
  (implies (bstp (zip-plug zip))
           (bstp (zip-tree-after zip)))
  :enable (zip-tree-after
           zip-plug
           bstp-of-zip-path-tree-after
           bstp-of-tree->right-when-bstp))

(defrule heapp-of-zip-tree-after-when-heapp-of-zip-plug
  (implies (heapp (zip-plug zip))
           (heapp (zip-tree-after zip)))
  :enable (zip-tree-after
           zip-plug
           heapp-of-zip-path-tree-after
           heapp-of-tree->right-when-heapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; One fold, three views: reading a built side back out recovers the other two
;; representations exactly. The in-order sequence of the tree side is the list
;; side, and its element set is the oset side, with no hypotheses -- the fold
;; is structural, whether or not the zipper's tree is a search tree.

(defrule tree-in-order-of-zip-tree-before
  (equal (tree-in-order (zip-tree-before zip))
         (zip-before zip))
  :enable (zip-tree-before
           zip-before))

(defrule tree-in-order-of-zip-tree-after
  (equal (tree-in-order (zip-tree-after zip))
         (zip-after zip))
  :enable (zip-tree-after
           zip-after))

(defrule tree-oset-of-zip-tree-before
  (equal (tree-oset (zip-tree-before zip))
         (zip-oset-before zip))
  :enable (zip-tree-before
           zip-oset-before))

(defrule tree-oset-of-zip-tree-after
  (equal (tree-oset (zip-tree-after zip))
         (zip-oset-after zip))
  :enable (zip-tree-after
           zip-oset-after))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Uniqueness by value. What follows the cursor is an order filter of the tree
;; (@(tsee in-of-zip-oset-after-when-bstp)), so the value fixes the tail, and
;; the tail already fixes the zipper.

;; What follows the cursor, as an oset, is an order filter of the tree, so it
;; is fixed by the tree and the value.

(defruled zip-oset-after-when-same-value
  (implies (and (bstp (zip-plug zip1))
                (equal (zip-plug zip1) (zip-plug zip2))
                (equal (zip-value zip1) (zip-value zip2)))
           (equal (zip-oset-after zip1) (zip-oset-after zip2)))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy)
  ;; in-of-zip-oset-after rewrites membership into member-equal on the
  ;; sequence, which gets in ahead of the order-filter rule and hides the
  ;; value. The bstp version is the one that matters here.
  :disable in-of-zip-oset-after)

;; Over a search tree the oset and the sequence are the same object, so the
;; sequences agree too. Pure equality chaining -- kept apart from the step
;; above so that double-containment is not fighting the conversion.

(defruled zip-after-when-same-value
  (implies (and (bstp (zip-plug zip1))
                (equal (zip-plug zip1) (zip-plug zip2))
                (equal (zip-value zip1) (zip-value zip2)))
           (equal (zip-after zip1) (zip-after zip2)))
  :use ((:instance zip-oset-after-becomes-zip-after (zip zip1))
        (:instance zip-oset-after-becomes-zip-after (zip zip2))
        zip-oset-after-when-same-value))

(defrule zip-uniqueness-when-same-value
  (implies (and (zipp zip1)
                (zipp zip2)
                (bstp (zip-plug zip1))
                (equal (zip-plug zip1) (zip-plug zip2))
                (equal (zip-value zip1) (zip-value zip2)))
           (equal zip1 zip2))
  :rule-classes nil
  :use (zip-uniqueness-when-zip-after-equal
        zip-after-when-same-value))
