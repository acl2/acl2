; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../../internal/tree-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../../internal/tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-p (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
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
  :returns (from-left booleanp :rule-classes :type-prescription
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
  :enable zip-frame->from-left)

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
  :enable zip-frame->elem)

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
  :enable zip-frame->sibling)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame
  ((from-left booleanp)
   (elem tree-element-p)
   (sibling treep))
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

(defrule zip-frame-of-t-and-accessors-when-from-left
  (implies (and (zip-frame-p frame)
                (zip-frame->from-left frame))
           (equal (zip-frame t
                             (zip-frame->elem frame)
                             (zip-frame->sibling frame))
                  frame))
  :enable (zip-frame
           zip-frame->elem
           zip-frame->sibling))

(defrule zip-frame-of-nil-and-accessors-when-not-from-left
  (implies (and (zip-frame-p frame)
                (not (zip-frame->from-left frame)))
           (equal (zip-frame nil
                             (zip-frame->elem frame)
                             (zip-frame->sibling frame))
                  frame))
  :enable (zip-frame
           zip-frame->elem
           zip-frame->sibling))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-frame-listp (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
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

(defrule zip-frame-list-fix-when-zip-frame-listp
  (implies (zip-frame-listp path)
           (equal (zip-frame-list-fix path)
                  path))
  :enable zip-frame-list-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-no-left-frames-p ((path zip-frame-listp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check that no frame of a path has the focus in its left child."
  :long
  (xdoc::topstring
   (xdoc::p
     "A frame whose focus lies in the left child holds a node which follows
      the focus in order, so this checks that nothing outside the focus
      subtree follows it.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the length of the path,
      although the check stops at the first left frame."))
  (or (acl2::endp path)
      (and (not (zip-frame->from-left (first path)))
           (zip-path-no-left-frames-p (rest path)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-path-no-right-frames-p ((path zip-frame-listp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check that no frame of a path has the focus in its right child."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-path-no-left-frames-p): this checks that
      nothing outside the focus subtree precedes it."))
  (or (acl2::endp path)
      (and (zip-frame->from-left (first path))
           (zip-path-no-right-frames-p (rest path)))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-path-no-left-frames-p-of-cons
  (equal (zip-path-no-left-frames-p (cons frame path))
         (and (not (zip-frame->from-left frame))
              (zip-path-no-left-frames-p path)))
  :enable zip-path-no-left-frames-p)

(defrule zip-path-no-right-frames-p-of-cons
  (equal (zip-path-no-right-frames-p (cons frame path))
         (and (zip-frame->from-left frame)
              (zip-path-no-right-frames-p path)))
  :enable zip-path-no-right-frames-p)

(defrule zip-path-no-left-frames-p-when-not-consp-cheap
  (implies (not (consp path))
           (zip-path-no-left-frames-p path))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-no-left-frames-p)

(defrule zip-path-no-right-frames-p-when-not-consp-cheap
  (implies (not (consp path))
           (zip-path-no-right-frames-p path))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :enable zip-path-no-right-frames-p)
