; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-step-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/butlast" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local (include-book "../../internal/tree"))
(local (include-book "../../internal/in-order"))
(local (include-book "zip-frame"))
(local (include-book "zipper"))
(local (include-book "zip-move"))
(local (include-book "zip-step"))
(local (include-book "zip-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(defrulel butlast-when-<=-of-len
  (implies (<= (len x) (nfix n))
           (equal (butlast x n)
                  nil))
  :enable butlast)

(defruledl butlast-of-append-and-1
  (equal (butlast (append x y) 1)
         (if (consp y)
             (append x (butlast y 1))
           (butlast x 1)))
  :induct t
  :enable append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled zip-after-when-zip-at-end-p
  (implies (zip-at-end-p zip)
           (equal (zip-after zip)
                  nil))
  :enable (zip-at-end-p
           zip-after))

(defrule zip-after-when-zip-at-end-p-forward-chaining
  (implies (zip-at-end-p zip)
           (equal (zip-after zip)
                  nil))
  :rule-classes :forward-chaining
  :by zip-after-when-zip-at-end-p)

(defruled zip-before-when-zip-at-begin-p
  (implies (zip-at-begin-p zip)
           (equal (zip-before zip)
                  nil))
  :enable (zip-at-begin-p
           zip-before))

(defrule zip-before-when-zip-at-begin-p-forward-chaining
  (implies (zip-at-begin-p zip)
           (equal (zip-before zip)
                  nil))
  :rule-classes :forward-chaining
  :by zip-before-when-zip-at-begin-p)

(defruled zip-after-when-zip-at-max-p
  (implies (zip-at-max-p zip)
           (equal (zip-after zip)
                  nil))
  :enable (zip-at-max-p
           zip-after))

(defrule zip-after-when-zip-at-max-p-forward-chaining
  (implies (zip-at-max-p zip)
           (equal (zip-after zip)
                  nil))
  :rule-classes :forward-chaining
  :by zip-after-when-zip-at-max-p)

(defruled zip-before-when-zip-at-min-p
  (implies (zip-at-min-p zip)
           (equal (zip-before zip)
                  nil))
  :enable (zip-at-min-p
           zip-before))

(defrule zip-before-when-zip-at-min-p-forward-chaining
  (implies (zip-at-min-p zip)
           (equal (zip-before zip)
                  nil))
  :rule-classes :forward-chaining
  :by zip-before-when-zip-at-min-p)

(defrule zip-before-of-zip-begin
  (equal (zip-before (zip-begin tree))
         nil)
  :enable zip-before-when-zip-at-begin-p)

(defrule zip-after-of-zip-end
  (equal (zip-after (zip-end tree))
         nil)
  :enable zip-after-when-zip-at-end-p)

(defruled zip-at-end-p-becomes-not-consp-of-zip-after
  (equal (zip-at-end-p zip)
         (and (tree-empty-p (zip->focus zip))
              (not (consp (zip-after zip)))))
  :enable (zip-at-end-p
           zip-after)
  :cases ((zip-path-no-left-frames-p (zip->path zip))))

(defruled zip-at-begin-p-becomes-not-consp-of-zip-before
  (equal (zip-at-begin-p zip)
         (and (tree-empty-p (zip->focus zip))
              (not (consp (zip-before zip)))))
  :enable (zip-at-begin-p
           zip-before)
  :cases ((zip-path-no-right-frames-p (zip->path zip))))

(defruled zip-at-max-p-becomes-not-consp-of-zip-after
  (equal (zip-at-max-p zip)
         (and (not (tree-empty-p (zip->focus zip)))
              (not (consp (zip-after zip)))))
  :enable (zip-at-max-p
           zip-after)
  :cases ((and (zip-path-no-left-frames-p (zip->path zip))
                (tree-empty-p (tree->right (zip->focus zip))))))

(defruled zip-at-min-p-becomes-not-consp-of-zip-before
  (equal (zip-at-min-p zip)
         (and (not (tree-empty-p (zip->focus zip)))
              (not (consp (zip-before zip)))))
  :enable (zip-at-min-p
           zip-before)
  :cases ((and (zip-path-no-right-frames-p (zip->path zip))
                (tree-empty-p (tree->left (zip->focus zip))))))

(defrule zip-path-no-left-frames-p-of-zip->path-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-path-no-left-frames-p (zip->path zip))
                  (not (consp (zip-after zip)))))
  :enable zip-after
  :cases ((zip-path-no-left-frames-p (zip->path zip))))

(defrule zip-path-no-right-frames-p-of-zip->path-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-path-no-right-frames-p (zip->path zip))
                  (not (consp (zip-before zip)))))
  :enable zip-before
  :cases ((zip-path-no-right-frames-p (zip->path zip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A step forward from an element moves its value onto the end of what
;; precedes, and a step forward from a hole moves the next value off the front
;; of what follows. A step backward is the mirror image.

(defruledl zip-before-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-before zip)
                  (zip-path-before (zip->path zip))))
  :enable zip-before)

(defruledl zip-after-when-tree-empty-p-of-focus
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-after zip)
                  (zip-path-after (zip->path zip))))
  :enable zip-after)

(defruledl zip-before-of-zip-descend-leftmost-hole
  (equal (zip-before (zip-descend-leftmost-hole zip))
         (zip-path-before (zip->path zip)))
  :induct (zip-descend-leftmost-hole zip)
  :enable (zip-descend-leftmost-hole
           zip-before))

(defruledl zip-after-of-zip-descend-leftmost-hole
  (equal (zip-after (zip-descend-leftmost-hole zip))
         (append (tree-in-order (zip->focus zip))
                 (zip-path-after (zip->path zip))))
  :induct (zip-descend-leftmost-hole zip)
  :enable (zip-descend-leftmost-hole
           zip-after
           tree-in-order))

(defruledl zip-after-of-zip-descend-rightmost-hole
  (equal (zip-after (zip-descend-rightmost-hole zip))
         (zip-path-after (zip->path zip)))
  :induct (zip-descend-rightmost-hole zip)
  :enable (zip-descend-rightmost-hole
           zip-after))

(defruledl zip-before-of-zip-descend-rightmost-hole
  (equal (zip-before (zip-descend-rightmost-hole zip))
         (append (zip-path-before (zip->path zip))
                 (tree-in-order (zip->focus zip))))
  :induct (zip-descend-rightmost-hole zip)
  :enable (zip-descend-rightmost-hole
           zip-before
           tree-in-order))

(defruledl zip-before-of-zip-ascend-to-left-frame
  (implies (consp (zip-path-after (zip->path zip)))
           (equal (zip-before (zip-ascend-to-left-frame zip))
                  (append (zip-path-before (zip->path zip))
                          (tree-in-order (zip->focus zip)))))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-before
           zip-path-before
           zip-path-after
           zip-frame-plug
           tree-in-order))

(defruledl zip-after-of-zip-ascend-to-left-frame
  (implies (consp (zip-path-after (zip->path zip)))
           (equal (zip-after (zip-ascend-to-left-frame zip))
                  (cdr (zip-path-after (zip->path zip)))))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-after
           zip-path-after
           zip-frame-plug))

(defruledl zip-key+val-of-zip-ascend-to-left-frame
  (implies (consp (zip-path-after (zip->path zip)))
           (equal (zip-key+val (zip-ascend-to-left-frame zip))
                  (car (zip-path-after (zip->path zip)))))
  :induct (zip-ascend-to-left-frame zip)
  :expand ((zip-path-after (zip->path zip)))
  :enable (zip-ascend-to-left-frame
           zip-key+val
           zip-frame-plug))

(defruledl zip-after-of-zip-ascend-to-right-frame
  (implies (consp (zip-path-before (zip->path zip)))
           (equal (zip-after (zip-ascend-to-right-frame zip))
                  (append (tree-in-order (zip->focus zip))
                          (zip-path-after (zip->path zip)))))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-after
           zip-path-after
           zip-path-before
           zip-frame-plug
           tree-in-order))

(defruledl zip-before-of-zip-ascend-to-right-frame
  (implies (consp (zip-path-before (zip->path zip)))
           (equal (zip-before (zip-ascend-to-right-frame zip))
                  (butlast (zip-path-before (zip->path zip)) 1)))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-before
           zip-path-before
           zip-frame-plug
           butlast-of-append-and-1))

(defruledl zip-key+val-of-zip-ascend-to-right-frame
  (implies (consp (zip-path-before (zip->path zip)))
           (equal (zip-key+val (zip-ascend-to-right-frame zip))
                  (car (last (zip-path-before (zip->path zip))))))
  :induct (zip-ascend-to-right-frame zip)
  :expand ((zip-path-before (zip->path zip)))
  :enable (zip-ascend-to-right-frame
           zip-key+val
           zip-frame-plug))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-before-of-zip-step-forward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-before (zip-step-forward zip))
                  (append (zip-before zip)
                          (list (zip-key+val zip)))))
  :enable (zip-step-forward
           zip-before
           zip-key+val
           zip-before-of-zip-descend-leftmost-hole))

(defrule zip-before-of-zip-step-forward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-before (zip-step-forward zip))
                  (zip-before zip)))
  :enable (zip-step-forward
           zip-before-when-tree-empty-p-of-focus
           zip-after-when-tree-empty-p-of-focus
           zip-before-of-zip-ascend-to-left-frame))

(defrule zip-after-of-zip-step-forward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-after (zip-step-forward zip))
                  (zip-after zip)))
  :enable (zip-step-forward
           zip-after
           zip-after-of-zip-descend-leftmost-hole))

(defrule zip-after-of-zip-step-forward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-after (zip-step-forward zip))
                  (cdr (zip-after zip))))
  :enable (zip-step-forward
           zip-after-when-tree-empty-p-of-focus
           zip-after-of-zip-ascend-to-left-frame))

(defruled zip-after-of-zip-step-forward
  (equal (zip-after (zip-step-forward zip))
         (if (tree-empty-p (zip->focus zip))
             (cdr (zip-after zip))
           (zip-after zip))))

(defrule zip-key+val-of-zip-step-forward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-after zip)))
           (equal (zip-key+val (zip-step-forward zip))
                  (car (zip-after zip))))
  :enable (zip-step-forward
           zip-after-when-tree-empty-p-of-focus
           zip-key+val-of-zip-ascend-to-left-frame))

(defrule zip-key-of-zip-step-forward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-after zip)))
           (equal (zip-key (zip-step-forward zip))
                  (caar (zip-after zip))))
  :use zip-key+val-of-zip-step-forward-when-tree-empty-p
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val
  :disable zip-key+val-of-zip-step-forward-when-tree-empty-p)

(defrule zip-val-of-zip-step-forward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-after zip)))
           (equal (zip-val (zip-step-forward zip))
                  (cdar (zip-after zip))))
  :use zip-key+val-of-zip-step-forward-when-tree-empty-p
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val
  :disable zip-key+val-of-zip-step-forward-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defrule zip-after-of-zip-step-backward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-after (zip-step-backward zip))
                  (cons (zip-key+val zip)
                        (zip-after zip))))
  :enable (zip-step-backward
           zip-after
           zip-key+val
           zip-after-of-zip-descend-rightmost-hole))

(defrule zip-after-of-zip-step-backward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-after (zip-step-backward zip))
                  (zip-after zip)))
  :enable (zip-step-backward
           zip-before-when-tree-empty-p-of-focus
           zip-after-when-tree-empty-p-of-focus
           zip-after-of-zip-ascend-to-right-frame))

(defrule zip-before-of-zip-step-backward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-before (zip-step-backward zip))
                  (zip-before zip)))
  :enable (zip-step-backward
           zip-before
           zip-before-of-zip-descend-rightmost-hole))

(defrule zip-before-of-zip-step-backward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-before (zip-step-backward zip))
                  (butlast (zip-before zip) 1)))
  :enable (zip-step-backward
           zip-before-when-tree-empty-p-of-focus
           zip-before-of-zip-ascend-to-right-frame))

(defrule zip-key+val-of-zip-step-backward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (equal (zip-key+val (zip-step-backward zip))
                  (car (last (zip-before zip)))))
  :enable (zip-step-backward
           zip-before-when-tree-empty-p-of-focus
           zip-key+val-of-zip-ascend-to-right-frame))

(defrule zip-key-of-zip-step-backward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (equal (zip-key (zip-step-backward zip))
                  (caar (last (zip-before zip)))))
  :use zip-key+val-of-zip-step-backward-when-tree-empty-p
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val
  :disable zip-key+val-of-zip-step-backward-when-tree-empty-p)

(defrule zip-val-of-zip-step-backward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (equal (zip-val (zip-step-backward zip))
                  (cdar (last (zip-before zip)))))
  :use zip-key+val-of-zip-step-backward-when-tree-empty-p
  :enable zip-key+val-becomes-cons-of-zip-key-and-zip-val
  :disable zip-key+val-of-zip-step-backward-when-tree-empty-p)

;;;;;;;;;;;;;;;;;;;;

(defrule equal-of-zip-step-forward-and-zip-fix
  (equal (equal (zip-step-forward zip) (zip-fix zip))
         (zip-at-end-p zip))
  :use (zip-after-of-zip-step-forward-when-tree-empty-p
        tree-empty-p-of-focus-of-zip-step-forward)
  :enable zip-at-end-p-becomes-not-consp-of-zip-after
  :disable tree-empty-p-of-focus-of-zip-step-forward)

(defrule equal-of-zip-step-backward-and-zip-fix
  (equal (equal (zip-step-backward zip) (zip-fix zip))
         (zip-at-begin-p zip))
  :use (zip-after-of-zip-step-backward-when-not-tree-empty-p
        tree-empty-p-of-focus-of-zip-step-backward)
  :enable zip-at-begin-p-becomes-not-consp-of-zip-before
  :disable tree-empty-p-of-focus-of-zip-step-backward)
