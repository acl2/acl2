; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-step-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

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

(defruledl butlast-of-append-of-list
  (equal (butlast (append x (list a)) 1)
         (true-list-fix x))
  :induct t
  :enable append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule zip-after-when-zip-at-end-p
  (implies (zip-at-end-p zip)
           (equal (zip-after zip)
                  nil))
  :enable (zip-at-end-p
           zip-after))

(defrule zip-before-when-zip-at-begin-p
  (implies (zip-at-begin-p zip)
           (equal (zip-before zip)
                  nil))
  :enable (zip-at-begin-p
           zip-before))

(defrule zip-after-when-zip-at-max-p
  (implies (zip-at-max-p zip)
           (equal (zip-after zip)
                  nil))
  :enable (zip-at-max-p
           zip-after))

(defrule zip-before-when-zip-at-min-p
  (implies (zip-at-min-p zip)
           (equal (zip-before zip)
                  nil))
  :enable (zip-at-min-p
           zip-before))

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

(defruledl zip-before-of-zip-descend-leftmost-hole
  (equal (zip-before (zip-descend-leftmost-hole zip))
         (zip-path-before (zip->path zip)))
  :induct (zip-descend-leftmost-hole zip)
  :enable (zip-descend-leftmost-hole
           zip-before))

(defruledl zip-after-of-zip-descend-rightmost-hole
  (equal (zip-after (zip-descend-rightmost-hole zip))
         (zip-path-after (zip->path zip)))
  :induct (zip-descend-rightmost-hole zip)
  :enable (zip-descend-rightmost-hole
           zip-after))

(defruledl zip-before-of-zip-ascend-to-left-frame
  (implies (not (zip-path-no-left-frames-p (zip->path zip)))
           (equal (zip-before (zip-ascend-to-left-frame zip))
                  (append (zip-path-before (zip->path zip))
                          (tree-in-order (zip->focus zip)))))
  :induct (zip-ascend-to-left-frame zip)
  :enable (zip-ascend-to-left-frame
           zip-path-no-left-frames-p
           zip-before
           zip-path-before
           zip-frame-plug
           tree-in-order))

(defruledl zip-after-of-zip-ascend-to-right-frame
  (implies (not (zip-path-no-right-frames-p (zip->path zip)))
           (equal (zip-after (zip-ascend-to-right-frame zip))
                  (append (tree-in-order (zip->focus zip))
                          (zip-path-after (zip->path zip)))))
  :induct (zip-ascend-to-right-frame zip)
  :enable (zip-ascend-to-right-frame
           zip-path-no-right-frames-p
           zip-after
           zip-path-after
           zip-frame-plug
           tree-in-order))

;;;;;;;;;;;;;;;;;;;;

(defrule zip-before-of-zip-step-forward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-before (zip-step-forward zip))
                  (append (zip-before zip)
                          (list (zip-value zip)))))
  :enable (zip-step-forward
           zip-before
           zip-value
           zip-before-of-zip-descend-leftmost-hole))

(defrule zip-before-of-zip-step-forward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-before (zip-step-forward zip))
                  (zip-before zip)))
  :enable (zip-step-forward
           zip-before
           zip-before-of-zip-ascend-to-left-frame
           tree-in-order))

(defrule zip-after-of-zip-step-backward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-after (zip-step-backward zip))
                  (cons (zip-value zip)
                        (zip-after zip))))
  :enable (zip-step-backward
           zip-after
           zip-value
           zip-after-of-zip-descend-rightmost-hole))

(defrule zip-after-of-zip-step-backward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-after (zip-step-backward zip))
                  (zip-after zip)))
  :enable (zip-step-backward
           zip-after
           zip-after-of-zip-ascend-to-right-frame
           tree-in-order))

(defrule zip-after-of-zip-step-forward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-after (zip-step-forward zip))
                  (zip-after zip)))
  :use (tree-in-order-of-zip-plug-split-at-cursor
        (:instance tree-in-order-of-zip-plug-split-at-cursor
                   (zip (zip-step-forward zip)))))

(defrule zip-after-of-zip-step-forward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-after (zip-step-forward zip))
                  (cdr (zip-after zip))))
  :use (tree-in-order-of-zip-plug-split-at-cursor
        (:instance tree-in-order-of-zip-plug-split-at-cursor
                   (zip (zip-step-forward zip)))))

(defrule zip-value-of-zip-step-forward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-after zip)))
           (equal (zip-value (zip-step-forward zip))
                  (car (zip-after zip))))
  :use (tree-in-order-of-zip-plug-split-at-cursor
        (:instance tree-in-order-of-zip-plug-split-at-cursor
                   (zip (zip-step-forward zip)))))

(defrule zip-before-of-zip-step-backward-when-not-tree-empty-p
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (zip-before (zip-step-backward zip))
                  (zip-before zip)))
  :use (tree-in-order-of-zip-plug-split-at-cursor
        (:instance tree-in-order-of-zip-plug-split-at-cursor
                   (zip (zip-step-backward zip)))))

(defruledl zip-before-becomes-append-of-zip-step-backward
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (equal (zip-before zip)
                  (append (zip-before (zip-step-backward zip))
                          (list (zip-value (zip-step-backward zip))))))
  :use (:instance zip-before-of-zip-step-forward-when-not-tree-empty-p
                  (zip (zip-step-backward zip)))
  :disable zip-before-of-zip-step-forward-when-not-tree-empty-p)

(defrule zip-before-of-zip-step-backward-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (zip-before (zip-step-backward zip))
                  (butlast (zip-before zip) 1)))
  :cases ((consp (zip-before zip)))
  :enable (zip-before-becomes-append-of-zip-step-backward
           butlast-of-append-of-list
           zip-at-begin-p-becomes-not-consp-of-zip-before))

(defrule zip-value-of-zip-step-backward-when-tree-empty-p
  (implies (and (tree-empty-p (zip->focus zip))
                (consp (zip-before zip)))
           (equal (zip-value (zip-step-backward zip))
                  (car (last (zip-before zip)))))
  :use zip-before-becomes-append-of-zip-step-backward)

;;;;;;;;;;;;;;;;;;;;

(defrule equal-of-zip-step-forward-and-zip-fix
  (equal (equal (zip-step-forward zip) (zip-fix zip))
         (zip-at-end-p zip))
  :use (zip-after-of-zip-step-forward-when-tree-empty-p
        tree-empty-p-of-focus-of-zip-step-forward)
  :enable zip-at-end-p-becomes-not-consp-of-zip-after
  :disable (zip-after-of-zip-step-forward-when-tree-empty-p
            tree-empty-p-of-focus-of-zip-step-forward))

(defrule equal-of-zip-step-backward-and-zip-fix
  (equal (equal (zip-step-backward zip) (zip-fix zip))
         (zip-at-begin-p zip))
  :use (zip-after-of-zip-step-backward-when-not-tree-empty-p
        tree-empty-p-of-focus-of-zip-step-backward)
  :enable zip-at-begin-p-becomes-not-consp-of-zip-before
  :disable (zip-after-of-zip-step-backward-when-not-tree-empty-p
            tree-empty-p-of-focus-of-zip-step-backward))
