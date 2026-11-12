; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)

(include-book "../set-defs")
(include-book "../min-max-defs")
(include-book "../insert-defs")
(include-book "../delete-defs")
(include-book "../union-defs")
(include-book "../intersect-defs")
(include-book "../diff-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/min" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/max" :dir :system))

(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../min-max"))
(local (include-book "../insert"))
(local (include-book "../delete"))
(local (include-book "../union"))
(local (include-book "../intersect"))
(local (include-book "../diff"))
(local (include-book "../extensionality"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule intersect-of-after-and-before
  (equal (intersect (after cursor) (before cursor))
         (empty))
  :enable extensionality)

(defrule union-of-after-and-before
  (equal (union (after cursor) (before cursor))
         (if (entryp cursor)
             (delete (entry cursor) (from-cursor cursor))
           (from-cursor cursor)))
  :enable (extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

(defrule diff-of-from-cursor-and-before
  (equal (diff (from-cursor cursor) (before cursor))
         (if (entryp cursor)
             (insert (entry cursor) (after cursor))
           (after cursor)))
  :enable (extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

(defrule diff-of-from-cursor-and-after
  (equal (diff (from-cursor cursor) (after cursor))
         (if (entryp cursor)
             (insert (entry cursor) (before cursor))
           (before cursor)))
  :enable (extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled entry-becomes-min-of-diff
  (implies (entryp cursor)
           (equal (entry cursor)
                  (min (diff (from-cursor cursor) (before cursor)))))
  :enable min-<<)

(defruled entry-becomes-max-of-diff
  (implies (entryp cursor)
           (equal (entry cursor)
                  (max (diff (from-cursor cursor) (after cursor)))))
  :enable (max-<<
           data::<<-rules))
