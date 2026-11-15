; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)
(include-book "std/osets/defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/bst-defs")
(include-book "../../internal/in-defs")
(include-book "zipper-defs")
(include-book "zip-side-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/oset" :dir :system))

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "../../internal/in-order"))
(local (include-book "zip-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The in-order sequence of a search tree is an oset. These put that fact,
;; cut at the cursor, where the oset rules about append can find it.

(defruledl append-of-zip-before-and-zip-after-when-tree-empty-p
  (implies (tree-empty-p (zip->focus zip))
           (equal (append (zip-before zip)
                          (zip-after zip))
                  (tree-in-order (zip-plug zip))))
  :enable tree-in-order-of-zip-plug-split-at-cursor)

(defruledl append-of-zip-before-and-cons-of-zip-value-and-zip-after
  (implies (not (tree-empty-p (zip->focus zip)))
           (equal (append (zip-before zip)
                          (cons (zip-value zip)
                                (zip-after zip)))
                  (tree-in-order (zip-plug zip))))
  :enable tree-in-order-of-zip-plug-split-at-cursor)

(defrulel osetp-of-append-of-sides-when-tree-empty-p-forward-chaining
  (implies (and (bstp (zip-plug zip))
                (tree-empty-p (zip->focus zip)))
           (set::setp (append (zip-before zip)
                              (zip-after zip))))
  :rule-classes :forward-chaining
  :enable append-of-zip-before-and-zip-after-when-tree-empty-p
  :disable tree-in-order-of-zip-plug)

(defrulel osetp-of-append-of-sides-when-not-tree-empty-p-forward-chaining
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (and (set::setp (append (zip-before zip)
                                   (cons (zip-value zip)
                                         (zip-after zip))))
                (set::setp (append (append (zip-before zip)
                                           (list (zip-value zip)))
                                   (zip-after zip)))))
  :rule-classes :forward-chaining
  :enable append-of-zip-before-and-cons-of-zip-value-and-zip-after
  :disable tree-in-order-of-zip-plug)

;;;;;;;;;;;;;;;;;;;;

(defrule osetp-of-zip-before-when-bstp
  (implies (bstp (zip-plug zip))
           (set::setp (zip-before zip)))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable data::setp-of-prefix-when-osetp-of-append)

(defrule osetp-of-zip-after-when-bstp
  (implies (bstp (zip-plug zip))
           (set::setp (zip-after zip)))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable data::setp-of-suffix-when-osetp-of-append)

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

(defrule not-member-equal-of-zip-value-and-zip-before
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (not (member-equal (zip-value zip) (zip-before zip))))
  :enable data::not-member-equal-of-prefix-when-osetp-of-append)

(defrule not-member-equal-of-zip-value-and-zip-after
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (not (member-equal (zip-value zip) (zip-after zip))))
  :enable data::not-member-equal-of-suffix-when-osetp-of-append)

(defrule in-of-zip-oset-before-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (set::in x (zip-oset-before zip))
                  (and (tree-in x (zip-plug zip))
                       (<< x (zip-value zip)))))
  :enable (tree-in-becomes-member-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor
           data::<<-across-append-of-members-when-osetp
           data::not-member-equal-of-prefix-when-osetp-of-append
           data::<<-rules)
  :disable member-equal-of-tree-in-order-under-iff)

(defrule in-of-zip-oset-after-when-bstp
  (implies (and (bstp (zip-plug zip))
                (not (tree-empty-p (zip->focus zip))))
           (equal (set::in x (zip-oset-after zip))
                  (and (tree-in x (zip-plug zip))
                       (<< (zip-value zip) x))))
  :enable (tree-in-becomes-member-equal-of-tree-in-order
           tree-in-order-of-zip-plug-split-at-cursor
           data::<<-across-append-of-members-when-osetp
           data::not-member-equal-of-suffix-when-osetp-of-append
           data::<<-rules)
  :disable member-equal-of-tree-in-order-under-iff)

(defruled not-member-equal-of-zip-before-when-member-equal-of-zip-after
  (implies (and (member-equal x (zip-after zip))
                (bstp (zip-plug zip)))
           (not (member-equal x (zip-before zip))))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable data::not-member-equal-of-prefix-when-osetp-of-append)

(defruled not-member-equal-of-zip-after-when-member-equal-of-zip-before
  (implies (and (member-equal x (zip-before zip))
                (bstp (zip-plug zip)))
           (not (member-equal x (zip-after zip))))
  :enable not-member-equal-of-zip-before-when-member-equal-of-zip-after)

(defruled <<-when-member-equal-of-zip-before-and-zip-after
  (implies (and (member-equal x (zip-before zip))
                (member-equal y (zip-after zip))
                (bstp (zip-plug zip)))
           (<< x y))
  :cases ((tree-empty-p (zip->focus zip)))
  :enable data::<<-across-append-of-members-when-osetp)
