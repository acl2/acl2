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
(include-book "zip-move-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "../../internal/tree"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-move"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defruledl zip-of-focus-and-nil-when-path-not-consp
  (implies (not (consp (zip->path zip)))
           (equal (zip (zip->focus zip) nil)
                  (zip-fix zip)))
  :enable (zip
           zip->focus
           zip-fix
           irr-zip))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents zipper))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-at-begin-p ((zip zipp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is at the first hole."
  (and (tree-empty-p (zip->focus zip))
       (zip-path-no-right-frames-p (zip->path zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-at-end-p ((zip zipp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is at the last hole."
  (and (tree-empty-p (zip->focus zip))
       (zip-path-no-left-frames-p (zip->path zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-at-min-p ((zip zipp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is at the first element."
  (and (not (tree-empty-p (zip->focus zip)))
       (tree-empty-p (tree->left (zip->focus zip)))
       (zip-path-no-right-frames-p (zip->path zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-at-max-p ((zip zipp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :short "Check whether the zipper is at the last element."
  (and (not (tree-empty-p (zip->focus zip)))
       (tree-empty-p (tree->right (zip->focus zip)))
       (zip-path-no-left-frames-p (zip->path zip)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-at-begin-p-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-at-begin-p zip0)
                  (zip-at-begin-p zip1)))
  :rule-classes :congruence
  :enable zip-at-begin-p)

(defrule zip-at-end-p-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-at-end-p zip0)
                  (zip-at-end-p zip1)))
  :rule-classes :congruence
  :enable zip-at-end-p)

(defrule zip-at-min-p-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-at-min-p zip0)
                  (zip-at-min-p zip1)))
  :rule-classes :congruence
  :enable zip-at-min-p)

(defrule zip-at-max-p-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-at-max-p zip0)
                  (zip-at-max-p zip1)))
  :rule-classes :congruence
  :enable zip-at-max-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-step-forward ((zip zipp))
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move to the next position in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "From an element, this is the hole just after it, the leftmost hole of
      its right subtree. From a hole, it is the element just after it, the
      nearest ancestor that follows the hole. At the last hole there is
      nothing after, and the move saturates.")
   (xdoc::p
     "Time complexity: @($O(d)$) in the worst case -- @($O(\\log(n))$) over a
      @(see tset)."))
  (cond ((not (tree-empty-p (zip->focus zip)))
         (zip-descend-leftmost-hole (zip-descend-right zip)))
        ((zip-path-no-left-frames-p (zip->path zip))
         (zip-fix zip))
        (t
         (zip-ascend-to-left-frame zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-step-backward ((zip zipp))
  :type-prescription :none
  :returns (zip$ zipp)
  :short "Move to the previous position in order."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-step-forward)."))
  (cond ((not (tree-empty-p (zip->focus zip)))
         (zip-descend-rightmost-hole (zip-descend-left zip)))
        ((zip-path-no-right-frames-p (zip->path zip))
         (zip-fix zip))
        (t
         (zip-ascend-to-right-frame zip))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-step-forward-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-step-forward zip0)
                  (zip-step-forward zip1)))
  :rule-classes :congruence
  :enable zip-step-forward)

(defrule zip-step-backward-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-step-backward zip0)
                  (zip-step-backward zip1)))
  :rule-classes :congruence
  :enable zip-step-backward)

(defrule zip-plug-of-zip-step-forward
  (equal (zip-plug (zip-step-forward zip))
         (zip-plug zip))
  :enable zip-step-forward)

(defrule zip-plug-of-zip-step-backward
  (equal (zip-plug (zip-step-backward zip))
         (zip-plug zip))
  :enable zip-step-backward)

(defrule tree-empty-p-of-focus-of-zip-step-forward
  (equal (tree-empty-p (zip->focus (zip-step-forward zip)))
         (or (not (tree-empty-p (zip->focus zip)))
             (zip-path-no-left-frames-p (zip->path zip))))
  :enable zip-step-forward)

(defrule tree-empty-p-of-focus-of-zip-step-backward
  (equal (tree-empty-p (zip->focus (zip-step-backward zip)))
         (or (not (tree-empty-p (zip->focus zip)))
             (zip-path-no-right-frames-p (zip->path zip))))
  :enable zip-step-backward)

(defrule zip-step-forward-when-zip-at-end-p
  (implies (zip-at-end-p zip)
           (equal (zip-step-forward zip)
                  (zip-fix zip)))
  :enable (zip-step-forward
           zip-at-end-p))

(defrule zip-step-backward-when-zip-at-begin-p
  (implies (zip-at-begin-p zip)
           (equal (zip-step-backward zip)
                  (zip-fix zip)))
  :enable (zip-step-backward
           zip-at-begin-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule zip-step-backward-of-zip-step-forward
  (implies (not (zip-at-end-p zip))
           (equal (zip-step-backward (zip-step-forward zip))
                  (zip-fix zip)))
  :enable (zip-step-forward
           zip-step-backward
           zip-at-end-p
           zip-ascend-to-right-frame-of-zip-descend-leftmost-hole
           zip-ascend-to-right-frame-of-zip-descend-right
           zip-descend-rightmost-hole-of-descend-left-of-ascend-to-left-frame))

(defrule zip-step-forward-of-zip-step-backward
  (implies (not (zip-at-begin-p zip))
           (equal (zip-step-forward (zip-step-backward zip))
                  (zip-fix zip)))
  :enable (zip-step-forward
           zip-step-backward
           zip-at-begin-p
           zip-ascend-to-left-frame-of-zip-descend-rightmost-hole
           zip-ascend-to-left-frame-of-zip-descend-left
           zip-descend-leftmost-hole-of-descend-right-of-ascend-to-right-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Two steps from an element, taken directly. These are the executable bodies
;; of zip-next and zip-prev.

(defruledl zip-step-forward-of-zip-step-forward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-step-forward (zip-step-forward zip))
                  (cond ((not (tree-empty-p (tree->right (zip->focus zip))))
                         (zip-descend-leftmost (zip-descend-right zip)))
                        ((zip-path-no-left-frames-p (zip->path zip))
                         (zip-descend-right zip))
                        (t
                         (zip-ascend-to-left-frame zip)))))
  :enable (zip-step-forward
           zip-descend-leftmost-hole-becomes-descend-left-of-leftmost
           zip-ascend-to-left-frame-of-zip-descend-left
           zip-ascend-to-left-frame-of-zip-descend-right))

(defruledl zip-step-backward-of-zip-step-backward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-step-backward (zip-step-backward zip))
                  (cond ((not (tree-empty-p (tree->left (zip->focus zip))))
                         (zip-descend-rightmost (zip-descend-left zip)))
                        ((zip-path-no-right-frames-p (zip->path zip))
                         (zip-descend-left zip))
                        (t
                         (zip-ascend-to-right-frame zip)))))
  :enable (zip-step-backward
           zip-descend-rightmost-hole-becomes-descend-right-of-rightmost
           zip-ascend-to-right-frame-of-zip-descend-right
           zip-ascend-to-right-frame-of-zip-descend-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-next ((zip zipp))
  :type-prescription :none
  :guard (not (tree-empty-p (zip->focus zip)))
  :returns (zip$ zipp)
  :short "Move from an element to the next element in order, or to the last
          hole if there is none."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is two steps forward, from any position. From an
      element, it executes directly: the successor is the leftmost element of
      the right subtree when there is one, and otherwise the nearest ancestor
      that follows.")
   (xdoc::p
     "Time complexity: @($O(d)$) in the worst case -- @($O(\\log(n))$) over a
      @(see tset) -- but @($O(1)$) amortized over a traversal, since each
      edge of the tree is crossed twice."))
  (mbe :logic (zip-step-forward (zip-step-forward zip))
       :exec (cond ((not (tree-empty-p (tree->right (zip->focus zip))))
                    (zip-descend-leftmost (zip-descend-right zip)))
                   ((zip-path-no-left-frames-p (zip->path zip))
                    (zip-descend-right zip))
                   (t
                    (zip-ascend-to-left-frame zip))))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable zip-step-forward-of-zip-step-forward-when-not-tree-empty-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-prev ((zip zipp))
  :type-prescription :none
  :guard (not (tree-empty-p (zip->focus zip)))
  :returns (zip$ zipp)
  :short "Move from an element to the previous element in order, or to the
          first hole if there is none."
  :long
  (xdoc::topstring
   (xdoc::p
     "The mirror image of @(tsee zip-next)."))
  (mbe :logic (zip-step-backward (zip-step-backward zip))
       :exec (cond ((not (tree-empty-p (tree->left (zip->focus zip))))
                    (zip-descend-rightmost (zip-descend-left zip)))
                   ((zip-path-no-right-frames-p (zip->path zip))
                    (zip-descend-left zip))
                   (t
                    (zip-ascend-to-right-frame zip))))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable zip-step-backward-of-zip-step-backward-when-not-tree-empty-p))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-next-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-next zip0)
                  (zip-next zip1)))
  :rule-classes :congruence
  :enable zip-next)

(defrule zip-prev-when-zip-equiv-congruence
  (implies (zip-equiv zip0 zip1)
           (equal (zip-prev zip0)
                  (zip-prev zip1)))
  :rule-classes :congruence
  :enable zip-prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-begin ((tree treep))
  :type-prescription :none
  :returns (zip zipp)
  :short "The zipper at the first hole of a tree."
  (zip-descend-leftmost-hole (zip-root tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-end ((tree treep))
  :type-prescription :none
  :returns (zip zipp)
  :short "The zipper at the last hole of a tree."
  (zip-descend-rightmost-hole (zip-root tree))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-begin-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-begin tree0)
                  (zip-begin tree1)))
  :rule-classes :congruence
  :enable zip-begin)

(defrule zip-end-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-end tree0)
                  (zip-end tree1)))
  :rule-classes :congruence
  :enable zip-end)

(defrule zip-plug-of-zip-begin
  (equal (zip-plug (zip-begin tree))
         (tree-fix tree))
  :enable zip-begin)

(defrule zip-plug-of-zip-end
  (equal (zip-plug (zip-end tree))
         (tree-fix tree))
  :enable zip-end)

(defrule zip-at-begin-p-of-zip-begin
  (zip-at-begin-p (zip-begin tree))
  :enable (zip-begin
           zip-at-begin-p))

(defrule zip-at-end-p-of-zip-end
  (zip-at-end-p (zip-end tree))
  :enable (zip-end
           zip-at-end-p))

(defrule tree-empty-p-of-focus-of-zip-begin
  (tree-empty-p (zip->focus (zip-begin tree)))
  :enable zip-begin)

(defrule tree-empty-p-of-focus-of-zip-end
  (tree-empty-p (zip->focus (zip-end tree)))
  :enable zip-end)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl zip-root-of-zip-plug-becomes-zip-ascend-to-left-frame
  (implies (zip-path-no-left-frames-p (zip->path zip))
           (equal (zip-root (zip-plug zip))
                  (zip-ascend-to-left-frame zip)))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-path-no-left-frames-p
           zip-root
           zip-plug
           zip-of-focus-and-nil-when-path-not-consp))

(defruledl zip-root-of-zip-plug-becomes-zip-ascend-to-right-frame
  (implies (zip-path-no-right-frames-p (zip->path zip))
           (equal (zip-root (zip-plug zip))
                  (zip-ascend-to-right-frame zip)))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-path-no-right-frames-p
           zip-root
           zip-plug
           zip-of-focus-and-nil-when-path-not-consp))

(defruledl zip-rightmost-hole-of-ascend-to-left-frame-when-no-left-frames
  (implies (zip-path-no-left-frames-p (zip->path zip))
           (equal (zip-descend-rightmost-hole (zip-ascend-to-left-frame zip))
                  (zip-descend-rightmost-hole zip)))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-path-no-left-frames-p
           zip-descend-rightmost-hole-of-zip-ascend-one-when-not-from-left))

(defruledl zip-leftmost-hole-of-ascend-to-right-frame-when-no-right-frames
  (implies (zip-path-no-right-frames-p (zip->path zip))
           (equal (zip-descend-leftmost-hole (zip-ascend-to-right-frame zip))
                  (zip-descend-leftmost-hole zip)))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-path-no-right-frames-p
           zip-descend-leftmost-hole-of-zip-ascend-one-when-from-left))

(defrule zip-end-of-zip-plug-when-zip-at-end-p
  (implies (zip-at-end-p zip)
           (equal (zip-end (zip-plug zip))
                  (zip-fix zip)))
  :enable (zip-end
           zip-at-end-p
           zip-root-of-zip-plug-becomes-zip-ascend-to-left-frame
           zip-rightmost-hole-of-ascend-to-left-frame-when-no-left-frames))

(defrule zip-begin-of-zip-plug-when-zip-at-begin-p
  (implies (zip-at-begin-p zip)
           (equal (zip-begin (zip-plug zip))
                  (zip-fix zip)))
  :enable (zip-begin
           zip-at-begin-p
           zip-root-of-zip-plug-becomes-zip-ascend-to-right-frame
           zip-leftmost-hole-of-ascend-to-right-frame-when-no-right-frames))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-min ((tree treep))
  :type-prescription :none
  :returns (zip zipp)
  :short "The zipper at the first element of a tree, or at its one hole if it
          is empty."
  :long
  (xdoc::topstring-p
    "Logically, this is one step forward from @(tsee zip-begin). It executes
     as a direct descent to the leftmost element.")
  (mbe :logic (zip-step-forward (zip-begin tree))
       :exec (if (tree-empty-p tree)
                 (zip-root tree)
               (zip-descend-leftmost (zip-root tree))))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable zip-begin
            zip-step-forward
            zip-descend-leftmost-hole-becomes-descend-left-of-leftmost
            zip-ascend-to-left-frame-of-zip-descend-left))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zip-max ((tree treep))
  :type-prescription :none
  :returns (zip zipp)
  :short "The zipper at the last element of a tree, or at its one hole if it
          is empty."
  :long
  (xdoc::topstring-p
    "The mirror image of @(tsee zip-min).")
  (mbe :logic (zip-step-backward (zip-end tree))
       :exec (if (tree-empty-p tree)
                 (zip-root tree)
               (zip-descend-rightmost (zip-root tree))))
  :inline t
  :guard-hints
  (("Goal"
    :in-theory
    (enable zip-end
            zip-step-backward
            zip-descend-rightmost-hole-becomes-descend-right-of-rightmost
            zip-ascend-to-right-frame-of-zip-descend-right))))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-min-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-min tree0)
                  (zip-min tree1)))
  :rule-classes :congruence
  :enable zip-min)

(defrule zip-max-when-tree-equiv-congruence
  (implies (tree-equiv tree0 tree1)
           (equal (zip-max tree0)
                  (zip-max tree1)))
  :rule-classes :congruence
  :enable zip-max)
