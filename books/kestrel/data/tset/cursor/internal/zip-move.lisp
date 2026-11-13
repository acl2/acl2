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

(include-book "../../internal/tree-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defrulel tree-node-of-tree->head-and-tree->left-and-tree->right
  (implies (not (tree-empty-p tree))
           (equal (tree-node (tree->head tree)
                             (tree->left tree)
                             (tree->right tree))
                  tree))
  :by tree-node-elim)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-left ((zip zipp))
  :type-prescription :none
  :guard (not (tree-empty-p (zip->focus zip)))
  :returns (zip$ zipp)
  :short "Move the focus to the left child, pushing a frame."
  :long
  (xdoc::topstring-p
    "The child may be empty, in which case the move lands on a hole.")
  (let ((focus (zip->focus zip)))
    (zip (tree->left focus)
         (cons (zip-frame t (tree->head focus) (tree->right focus))
               (zip->path zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-descend-left-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-left zip0)
                  (zip-descend-left zip1)))
  :rule-classes :congruence
  :enable zip-descend-left)

(defrule zip-plug-of-zip-descend-left
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-plug (zip-descend-left zip))
                  (zip-plug zip)))
  :enable (zip-descend-left
           zip-plug
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-right ((zip zipp))
  :type-prescription :none
  :guard (not (tree-empty-p (zip->focus zip)))
  :returns (zip$ zipp)
  :short "Move the focus to the right child, pushing a frame."
  :long
  (xdoc::topstring-p
    "The child may be empty, in which case the move lands on a hole.")
  (let ((focus (zip->focus zip)))
    (zip (tree->right focus)
         (cons (zip-frame nil (tree->head focus) (tree->left focus))
               (zip->path zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-descend-right-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-right zip0)
                  (zip-descend-right zip1)))
  :rule-classes :congruence
  :enable zip-descend-right)

(defrule zip-plug-of-zip-descend-right
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-plug (zip-descend-right zip))
                  (zip-plug zip)))
  :enable (zip-descend-right
           zip-plug
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;

(defrule zip->focus-of-zip-descend-left
  (equal (zip->focus (zip-descend-left zip))
         (tree->left (zip->focus zip)))
  :enable zip-descend-left)

(defrule zip->focus-of-zip-descend-right
  (equal (zip->focus (zip-descend-right zip))
         (tree->right (zip->focus zip)))
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
  :type-prescription :none
  :guard (consp (zip->path zip))
  :returns (zip$ zipp)
  :short "Move the focus up to its parent, popping a frame."
  (let ((frame (first (zip->path zip))))
    (zip (zip-frame-plug frame (zip->focus zip))
         (rest (zip->path zip))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

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
  :enable (zip-ascend-one
           zip-plug
           zip-path-plug))

(defrule zip->path-of-zip-ascend-one
  (implies (consp (zip->path zip))
           (equal (zip->path (zip-ascend-one zip))
                  (cdr (zip->path zip))))
  :enable zip-ascend-one)

(defrule zip->focus-of-zip-ascend-one
  (equal (zip->focus (zip-ascend-one zip))
         (zip-frame-plug (car (zip->path zip))
                         (zip->focus zip)))
  :enable zip-ascend-one)

(defrule zip-ascend-one-of-zip-descend-left
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-ascend-one (zip-descend-left zip))
                  (zip-fix zip)))
  :enable (zip-ascend-one
           zip-frame-plug))

(defrule zip-ascend-one-of-zip-descend-right
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-ascend-one (zip-descend-right zip))
                  (zip-fix zip)))
  :enable (zip-ascend-one
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-leftmost ((zip zipp))
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move the focus to the leftmost element within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "At a hole there is no element within the focus, and the zipper stays
      put.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended, and so
      @($O(\\log(n))$) over a @(see tset)."))
  (if (tree-empty-p (tree->left (zip->focus zip)))
      (zip-fix zip)
    (zip-descend-leftmost (zip-descend-left zip)))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

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
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move the focus to the rightmost element within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-descend-leftmost)."))
  (if (tree-empty-p (tree->right (zip->focus zip)))
      (zip-fix zip)
    (zip-descend-rightmost (zip-descend-right zip)))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-leftmost-hole ((zip zipp))
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move the focus to the leftmost hole within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "At a hole, that hole is the only one within the focus, and the zipper
      stays put.")
   (xdoc::p
     "Time complexity: @($O(d)$), where @($d$) is the depth descended, and so
      @($O(\\log(n))$) over a @(see tset)."))
  (if (tree-empty-p (zip->focus zip))
      (zip-fix zip)
    (zip-descend-leftmost-hole (zip-descend-left zip)))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-descend-rightmost-hole ((zip zipp))
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move the focus to the rightmost hole within it."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-descend-leftmost-hole)."))
  (if (tree-empty-p (zip->focus zip))
      (zip-fix zip)
    (zip-descend-rightmost-hole (zip-descend-right zip)))
  :measure (acl2-count (zip->focus zip)))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-descend-leftmost-hole-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-leftmost-hole zip0)
                  (zip-descend-leftmost-hole zip1)))
  :rule-classes :congruence
  :expand ((zip-descend-leftmost-hole zip0)
           (zip-descend-leftmost-hole zip1)))

(defrule zip-descend-rightmost-hole-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-descend-rightmost-hole zip0)
                  (zip-descend-rightmost-hole zip1)))
  :rule-classes :congruence
  :expand ((zip-descend-rightmost-hole zip0)
           (zip-descend-rightmost-hole zip1)))

(defrule zip-plug-of-zip-descend-leftmost-hole
  (equal (zip-plug (zip-descend-leftmost-hole zip))
         (zip-plug zip))
  :induct t
  :enable zip-descend-leftmost-hole)

(defrule zip-plug-of-zip-descend-rightmost-hole
  (equal (zip-plug (zip-descend-rightmost-hole zip))
         (zip-plug zip))
  :induct t
  :enable zip-descend-rightmost-hole)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-ascend-to-left-frame ((zip zipp))
  :type-prescription :none
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
      @($O(\\log(n))$) over a @(see tset)."))
  (cond ((acl2::endp (zip->path zip))
         (zip-fix zip))
        ((zip-frame->from-left (first (zip->path zip)))
         (zip-ascend-one zip))
        (t
         (zip-ascend-to-left-frame (zip-ascend-one zip))))
  :measure (len (zip->path zip)))

;;;;;;;;;;;;;;;;;;;;

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
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move the focus up to the nearest ancestor that precedes it."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-ascend-to-left-frame)."))
  (cond ((acl2::endp (zip->path zip))
         (zip-fix zip))
        ((zip-frame->from-left (first (zip->path zip)))
         (zip-ascend-to-right-frame (zip-ascend-one zip)))
        (t
         (zip-ascend-one zip)))
  :measure (len (zip->path zip)))

;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defrule zip-descend-leftmost-hole-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-descend-leftmost-hole zip)
                  (zip-fix zip)))
  :enable zip-descend-leftmost-hole)

(defrule zip-descend-rightmost-hole-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-descend-rightmost-hole zip)
                  (zip-fix zip)))
  :enable zip-descend-rightmost-hole)

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

(defrule tree-empty-p-of-focus-of-zip-descend-leftmost
  (equal (tree-empty-p (zip->focus (zip-descend-leftmost zip)))
         (tree-empty-p (zip->focus zip)))
  :induct t
  :enable zip-descend-leftmost)

(defrule tree-empty-p-of-focus-of-zip-descend-rightmost
  (equal (tree-empty-p (zip->focus (zip-descend-rightmost zip)))
         (tree-empty-p (zip->focus zip)))
  :induct t
  :enable zip-descend-rightmost)

(defrule tree-empty-p-of-focus-of-zip-descend-leftmost-hole
  (tree-empty-p (zip->focus (zip-descend-leftmost-hole zip)))
  :induct t
  :enable zip-descend-leftmost-hole)

(defrule tree-empty-p-of-focus-of-zip-descend-rightmost-hole
  (tree-empty-p (zip->focus (zip-descend-rightmost-hole zip)))
  :induct t
  :enable zip-descend-rightmost-hole)

(defruled zip-descend-leftmost-hole-becomes-descend-left-of-leftmost
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-descend-leftmost-hole zip)
                  (zip-descend-left (zip-descend-leftmost zip))))
  :induct (zip-descend-leftmost zip)
  :enable (zip-descend-leftmost
           zip-descend-leftmost-hole))

(defruled zip-descend-rightmost-hole-becomes-descend-right-of-rightmost
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-descend-rightmost-hole zip)
                  (zip-descend-right (zip-descend-rightmost zip))))
  :induct (zip-descend-rightmost zip)
  :enable (zip-descend-rightmost
           zip-descend-rightmost-hole))

(defrule zip-path-no-right-frames-p-of-path-of-zip-descend-leftmost
  (equal (zip-path-no-right-frames-p
           (zip->path (zip-descend-leftmost zip)))
         (zip-path-no-right-frames-p (zip->path zip)))
  :induct t
  :enable zip-descend-leftmost)

(defrule zip-path-no-left-frames-p-of-path-of-zip-descend-rightmost
  (equal (zip-path-no-left-frames-p
           (zip->path (zip-descend-rightmost zip)))
         (zip-path-no-left-frames-p (zip->path zip)))
  :induct t
  :enable zip-descend-rightmost)

(defrule zip-path-no-right-frames-p-of-path-of-zip-descend-leftmost-hole
  (equal (zip-path-no-right-frames-p
           (zip->path (zip-descend-leftmost-hole zip)))
         (zip-path-no-right-frames-p (zip->path zip)))
  :induct t
  :enable zip-descend-leftmost-hole)

(defrule zip-path-no-left-frames-p-of-path-of-zip-descend-rightmost-hole
  (equal (zip-path-no-left-frames-p
           (zip->path (zip-descend-rightmost-hole zip)))
         (zip-path-no-left-frames-p (zip->path zip)))
  :induct t
  :enable zip-descend-rightmost-hole)

(defrule not-tree-empty-p-of-focus-of-zip-ascend-to-left-frame
  (implies (not (zip-path-no-left-frames-p (zip->path zip)))
           (not (tree-empty-p (zip->focus (zip-ascend-to-left-frame zip)))))
  :induct t
  :enable (zip-ascend-to-left-frame
           zip-path-no-left-frames-p))

(defrule not-tree-empty-p-of-focus-of-zip-ascend-to-right-frame
  (implies (not (zip-path-no-right-frames-p (zip->path zip)))
           (not (tree-empty-p (zip->focus (zip-ascend-to-right-frame zip)))))
  :induct t
  :enable (zip-ascend-to-right-frame
           zip-path-no-right-frames-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled zip-descend-left-of-zip-ascend-one-when-from-left
  (implies (and (consp (zip->path zip))
                (zip-frame->from-left (car (zip->path zip))))
           (equal (zip-descend-left (zip-ascend-one zip))
                  (zip-fix zip)))
  :enable (zip-descend-left
           zip-frame-plug))

(defruled zip-descend-right-of-zip-ascend-one-when-not-from-left
  (implies (and (consp (zip->path zip))
                (not (zip-frame->from-left (car (zip->path zip)))))
           (equal (zip-descend-right (zip-ascend-one zip))
                  (zip-fix zip)))
  :enable (zip-descend-right
           zip-frame-plug))

(defruled zip-descend-rightmost-hole-of-zip-ascend-one-when-not-from-left
  (implies (and (consp (zip->path zip))
                (not (zip-frame->from-left (car (zip->path zip)))))
           (equal (zip-descend-rightmost-hole (zip-ascend-one zip))
                  (zip-descend-rightmost-hole zip)))
  :enable (zip-descend-rightmost-hole
           zip-frame-plug
           zip-descend-right-of-zip-ascend-one-when-not-from-left))

(defruled zip-descend-leftmost-hole-of-zip-ascend-one-when-from-left
  (implies (and (consp (zip->path zip))
                (zip-frame->from-left (car (zip->path zip))))
           (equal (zip-descend-leftmost-hole (zip-ascend-one zip))
                  (zip-descend-leftmost-hole zip)))
  :enable (zip-descend-leftmost-hole
           zip-frame-plug
           zip-descend-left-of-zip-ascend-one-when-from-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled zip-ascend-to-right-frame-of-zip-descend-leftmost-hole
  (equal (zip-ascend-to-right-frame (zip-descend-leftmost-hole zip))
         (zip-ascend-to-right-frame zip))
  :induct (zip-descend-leftmost-hole zip)
  :enable (zip-descend-leftmost-hole
           zip-ascend-to-right-frame))

(defruled zip-ascend-to-left-frame-of-zip-descend-rightmost-hole
  (equal (zip-ascend-to-left-frame (zip-descend-rightmost-hole zip))
         (zip-ascend-to-left-frame zip))
  :induct (zip-descend-rightmost-hole zip)
  :enable (zip-descend-rightmost-hole
           zip-ascend-to-left-frame))

(defruled zip-ascend-to-right-frame-of-zip-descend-right
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-ascend-to-right-frame (zip-descend-right zip))
                  (zip-fix zip)))
  :enable zip-ascend-to-right-frame)

(defruled zip-ascend-to-left-frame-of-zip-descend-left
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-ascend-to-left-frame (zip-descend-left zip))
                  (zip-fix zip)))
  :enable zip-ascend-to-left-frame)

(defruled zip-ascend-to-left-frame-of-zip-descend-right
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-ascend-to-left-frame (zip-descend-right zip))
                  (zip-ascend-to-left-frame zip)))
  :enable zip-ascend-to-left-frame)

(defruled zip-ascend-to-right-frame-of-zip-descend-left
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-ascend-to-right-frame (zip-descend-left zip))
                  (zip-ascend-to-right-frame zip)))
  :enable zip-ascend-to-right-frame)

(defruled zip-descend-rightmost-hole-of-descend-left-of-ascend-to-left-frame
  (implies (not (zip-path-no-left-frames-p (zip->path zip)))
           (equal (zip-descend-rightmost-hole
                    (zip-descend-left (zip-ascend-to-left-frame zip)))
                  (zip-descend-rightmost-hole zip)))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-path-no-left-frames-p
           zip-descend-left-of-zip-ascend-one-when-from-left
           zip-descend-rightmost-hole-of-zip-ascend-one-when-not-from-left))

(defruled zip-descend-leftmost-hole-of-descend-right-of-ascend-to-right-frame
  (implies (not (zip-path-no-right-frames-p (zip->path zip)))
           (equal (zip-descend-leftmost-hole
                    (zip-descend-right (zip-ascend-to-right-frame zip)))
                  (zip-descend-leftmost-hole zip)))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-path-no-right-frames-p
           zip-descend-right-of-zip-ascend-one-when-not-from-left
           zip-descend-leftmost-hole-of-zip-ascend-one-when-from-left))
