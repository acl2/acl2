; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/defrule" :dir :system)

(include-book "../set-defs")
(include-book "../cardinality-defs")
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
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../cardinality"))
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

(defruled union-of-after-and-before
  (equal (union (after cursor) (before cursor))
         (if (entryp cursor)
             (delete (entry cursor) (from-cursor cursor))
           (from-cursor cursor)))
  :enable (extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

(defrule union-of-after-and-before-when-entryp
  (implies (entryp cursor)
           (equal (union (after cursor) (before cursor))
                  (delete (entry cursor) (from-cursor cursor))))
  :enable union-of-after-and-before)

(defrule union-of-after-and-before-when-not-entryp
  (implies (not (entryp cursor))
           (equal (union (after cursor) (before cursor))
                  (from-cursor cursor)))
  :enable union-of-after-and-before)

(defruled diff-of-from-cursor-and-before
  (equal (diff (from-cursor cursor) (before cursor))
         (if (entryp cursor)
             (insert (entry cursor) (after cursor))
           (after cursor)))
  :enable (extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

(defrule diff-of-from-cursor-and-before-when-entryp
  (implies (entryp cursor)
           (equal (diff (from-cursor cursor) (before cursor))
                  (insert (entry cursor) (after cursor))))
  :enable diff-of-from-cursor-and-before)

(defrule diff-of-from-cursor-and-before-when-not-entryp
  (implies (not (entryp cursor))
           (equal (diff (from-cursor cursor) (before cursor))
                  (after cursor)))
  :enable diff-of-from-cursor-and-before)

(defruled diff-of-from-cursor-and-after
  (equal (diff (from-cursor cursor) (after cursor))
         (if (entryp cursor)
             (insert (entry cursor) (before cursor))
           (before cursor)))
  :enable (extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after))

(defrule diff-of-from-cursor-and-after-when-entryp
  (implies (entryp cursor)
           (equal (diff (from-cursor cursor) (after cursor))
                  (insert (entry cursor) (before cursor))))
  :enable diff-of-from-cursor-and-after)

(defrule diff-of-from-cursor-and-after-when-not-entryp
  (implies (not (entryp cursor))
           (equal (diff (from-cursor cursor) (after cursor))
                  (before cursor)))
  :enable diff-of-from-cursor-and-after)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-from-cursor
  (equal (cardinality (from-cursor cursor))
         (+ (cardinality (before cursor))
            (if (entryp cursor) 1 0)
            (cardinality (after cursor))))
  :use (:instance cardinality-of-diff
                  (x (from-cursor cursor))
                  (y (before cursor)))
  :enable (diff-of-from-cursor-and-before
           intersect-when-subset-arg1-arg2
           intersect-when-subset-arg2-arg1
           acl2::fix)
  :disable cardinality-of-diff)

(defrule cardinality-of-from-cursor-lower-bound-linear
  (<= (+ (cardinality (before cursor))
         (cardinality (after cursor)))
      (cardinality (from-cursor cursor)))
  :rule-classes :linear
  :enable cardinality-of-from-cursor)

(defrule cardinality-of-from-cursor-upper-bound-linear
  (<= (cardinality (from-cursor cursor))
      (+ 1
         (cardinality (before cursor))
         (cardinality (after cursor))))
  :rule-classes :linear
  :enable cardinality-of-from-cursor)

(defrule cardinality-of-from-cursor-when-entryp-linear
  (implies (entryp cursor)
           (< (+ (cardinality (before cursor))
                 (cardinality (after cursor)))
              (cardinality (from-cursor cursor))))
  :rule-classes :linear
  :enable cardinality-of-from-cursor)

(defrule cardinality-of-from-cursor-when-not-entryp-linear
  (implies (not (entryp cursor))
           (<= (cardinality (from-cursor cursor))
               (+ (cardinality (before cursor))
                  (cardinality (after cursor)))))
  :rule-classes :linear
  :enable (cardinality-of-from-cursor
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy partition-extra-rules
  '(union-of-after-and-before
    diff-of-from-cursor-and-before
    diff-of-from-cursor-and-after
    cardinality-of-from-cursor))
