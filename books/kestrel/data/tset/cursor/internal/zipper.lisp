; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/heap-defs")
(include-book "zip-frame-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/bst"))
(local (include-book "../../internal/heap"))
(local (include-book "zip-frame"))

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
      "The focus may be empty. A zipper whose focus is a nonempty subtree is at
       an element, the root of that subtree, and one whose focus is empty is at
       a hole, a gap of the in-order sequence. A tree with @($n$) nodes has
       @($n+1$) empty subtrees, one per gap, so it has @($2n+1$) zippers in
       all, alternating between holes and elements in order. The empty tree
       has exactly one, a hole with an empty path.")
    (xdoc::p
      "Costs below are given as @($O(d)$), where @($d$) is a depth within the
       tree. That is the honest bound here, since a zipper is over an arbitrary
       @(see tree) and nothing at this level constrains its shape. Over a
       @(see tset), which is practically balanced, @($d$) is
       @($O(\\log(n))$)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zipp (x)
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Recognizer for @(see zipper)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "A zipper pairs a focus with the path from the root down to it. The focus
      is any tree, empty or not: an empty focus is a hole.")
   (xdoc::p
     "This recognizer is structural only. Whether the tree recovered from a
      zipper satisfies the @(see tset) invariants is a separate question."))
  (and (consp x)
       (treep (car x))
       (zip-frame-listp (cdr x))))

;;;;;;;;;;;;;;;;;;;;

(defrule zipp-compound-recognizer
  (implies (zipp x)
           (consp x))
  :rule-classes :compound-recognizer
  :enable zipp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-zip ()
  :returns (zip zipp
                :hints (("Goal" :in-theory (enable zipp))))
  :short "An irrelevant @(see zipper), used as the fixer's default."
  :long
  (xdoc::topstring-p
    "This is the one zipper of the empty tree, at its only hole.")
  (cons nil nil))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:e irr-zip)))

(defrule irr-zip-type-prescription
  (zipp (irr-zip))
  :rule-classes ((:type-prescription :typed-term (irr-zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-fix ((zip zipp))
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
  :long
  (xdoc::topstring-p
    "The zipper is at a hole exactly when this is empty.")
  (car (zip-fix zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip->focus-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip->focus zip0)
                  (zip->focus zip1)))
  :rule-classes :congruence
  :enable zip->focus)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip->path ((zip zipp))
  :returns (path zip-frame-listp
                 :hints (("Goal" :in-theory (enable zipp
                                                    zip-fix
                                                    irr-zip))))
  :short "Get the path from the root down to the focus."
  (cdr (zip-fix zip))
  :inline t
  :guard-hints (("Goal" :in-theory (enable zipp))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip->path-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip->path zip0)
                  (zip->path zip1)))
  :rule-classes :congruence
  :enable zip->path)

(defrule true-listp-of-zip->path
  (true-listp (zip->path zip))
  :rule-classes :type-prescription
  :enable (zip->path
           zip-fix
           zipp
           irr-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip
  ((focus treep)
   (path zip-frame-listp))
  :returns (zip zipp
                :hints (("Goal" :in-theory (enable zipp))))
  :short "Constructor for @(see zipper)s."
  (cons (tree-fix focus)
        (zip-frame-list-fix path))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-type-prescription
  (zipp (zip focus path))
  :rule-classes ((:type-prescription :typed-term (zip focus path))))

(defrule zip-when-tree-equiv-of-arg1-congruence
  (implies (tree-equiv focus0 focus1)
           (equal (zip focus0 path)
                  (zip focus1 path)))
  :rule-classes :congruence
  :enable zip)

(defrule zip->focus-of-zip
  (equal (zip->focus (zip focus path))
         (tree-fix focus))
  :enable (zip
           zip->focus
           zipp))

(defrule zip->path-of-zip
  (equal (zip->path (zip focus path))
         (zip-frame-list-fix path))
  :enable (zip
           zip->path
           zipp))

(defrule zip-elim
  (implies (zipp zip)
           (equal (zip (zip->focus zip)
                       (zip->path zip))
                  zip))
  :rule-classes :elim
  :enable (zip
           zip->focus
           zip->path
           zipp))

(defrule zip-of-zip-accessors
  (equal (zip (zip->focus zip) (zip->path zip))
         (zip-fix zip))
  :enable (zip
           zip->focus
           zip->path
           zip-fix
           zipp
           irr-zip))

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
  (if (acl2::endp path)
      (tree-fix tree)
    (zip-path-plug (rest path)
                   (zip-frame-plug (first path) tree))))

;;;;;;;;;;;;;;;;;;;;

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
      so @($O(\\log(n))$) over a @(see tset)."))
  (zip-path-plug (zip->path zip)
                 (zip->focus zip))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-plug-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-plug zip0)
                  (zip-plug zip1)))
  :rule-classes :congruence
  :enable zip-plug)

(defrule zip-plug-of-zip
  (equal (zip-plug (zip focus path))
         (zip-path-plug (zip-frame-list-fix path)
                        (tree-fix focus)))
  :enable zip-plug)

(defrule zip-plug-of-irr-zip
  (equal (zip-plug (irr-zip))
         nil)
  :enable irr-zip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-root ((tree treep))
  :returns (zip zipp)
  :short "The zipper focused on a whole tree, with an empty path."
  :long
  (xdoc::topstring-p
    "For the empty tree, this is its one hole.")
  (zip tree nil)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-root-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-root tree0)
                  (zip-root tree1)))
  :rule-classes :congruence
  :enable zip-root)

(defrule zip-plug-of-zip-root
  (equal (zip-plug (zip-root tree))
         (tree-fix tree))
  :enable zip-root)

(defrule zip->focus-of-zip-root
  (equal (zip->focus (zip-root tree))
         (tree-fix tree))
  :enable zip-root)

(defrule zip->path-of-zip-root
  (equal (zip->path (zip-root tree))
         nil)
  :enable zip-root)
