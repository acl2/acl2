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

(include-book "../set-defs")
(include-book "../in-defs")
(include-book "../subset-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(local (include-book "../internal/in-order"))
(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../subset"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "internal/before-after"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define from-cursor ((cursor cursorp))
  :returns (set setp
                :hints (("Goal" :in-theory (enable* break-abstraction))))
  :parents (cursor)
  :short "The underlying @(see tset) of a @(see cursor)."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (zip-plug (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t from-cursor)))

(defrule from-cursor-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (from-cursor cursor0)
                  (from-cursor cursor1)))
  :rule-classes :congruence
  :enable from-cursor)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl in-of-from-cursor-becomes-tree-in
  (equal (in x (from-cursor cursor))
         (and (tree-in x (zip-plug (cursor-fix cursor))) t))
  :enable (in
           from-cursor
           break-abstraction))

(defruled in-of-from-cursor-becomes-in-of-before-or-entry-or-after
  (equal (in x (from-cursor cursor))
         (or (in x (before cursor))
             (and (entryp cursor)
                  (equal x (entry cursor)))
             (in x (after cursor))))
  :enable (in-of-before-becomes-member-equal
           in-of-after-becomes-member-equal
           in-of-from-cursor-becomes-tree-in
           tree-in-order-of-zip-plug-split-at-cursor
           entry
           entryp)
  :use (:instance member-equal-of-tree-in-order-under-iff
                  (tree (zip-plug (cursor-fix cursor))))
  :disable member-equal-of-tree-in-order-under-iff)

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-entry
  (implies (entryp cursor)
           (in (entry cursor) (from-cursor cursor)))
  :enable in-of-from-cursor-becomes-in-of-before-or-entry-or-after)

(defrule subset-of-before-and-from-cursor
  (subset (before cursor) (from-cursor cursor))
  :enable (pick-a-point
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

(defrule subset-of-after-and-from-cursor
  (subset (after cursor) (from-cursor cursor))
  :enable (pick-a-point
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))
