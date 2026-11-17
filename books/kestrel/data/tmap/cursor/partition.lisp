; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)

(include-book "kestrel/data/tset/cardinality-defs" :dir :system)

(include-book "../map-defs")
(include-book "../keys-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "kestrel/data/tset/set" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))
(local (include-book "kestrel/data/tset/subset" :dir :system))
(local (include-book "kestrel/data/tset/intersect" :dir :system))
(local (include-book "kestrel/data/tset/diff" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/extensionality" :dir :system))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl subset-of-keys-of-before-and-keys-of-from-cursor
  (tset::subset (keys (before cursor))
                (keys (from-cursor cursor)))
  :enable (tset::pick-a-point
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after))

(defruledl diff-of-keys-of-from-cursor-and-keys-of-before
  (equal (tset::diff (keys (from-cursor cursor))
                     (keys (before cursor)))
         (if (entryp cursor)
             (tset::insert (entry-key cursor) (keys (after cursor)))
           (keys (after cursor))))
  :enable (tset::extensionality
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after))

;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-keys-of-from-cursor
  (equal (tset::cardinality (keys (from-cursor cursor)))
         (+ (tset::cardinality (keys (before cursor)))
            (if (entryp cursor) 1 0)
            (tset::cardinality (keys (after cursor)))))
  :use (:instance tset::cardinality-of-diff
                  (x (keys (from-cursor cursor)))
                  (y (keys (before cursor))))
  :enable (diff-of-keys-of-from-cursor-and-keys-of-before
           subset-of-keys-of-before-and-keys-of-from-cursor
           tset::intersect-when-subset-arg1-arg2
           tset::intersect-when-subset-arg2-arg1
           acl2::fix)
  :disable tset::cardinality-of-diff)

(defrule cardinality-of-keys-of-from-cursor-lower-bound-linear
  (<= (+ (tset::cardinality (keys (before cursor)))
         (tset::cardinality (keys (after cursor))))
      (tset::cardinality (keys (from-cursor cursor))))
  :rule-classes :linear
  :enable cardinality-of-keys-of-from-cursor)

(defrule cardinality-of-keys-of-from-cursor-upper-bound-linear
  (<= (tset::cardinality (keys (from-cursor cursor)))
      (+ 1
         (tset::cardinality (keys (before cursor)))
         (tset::cardinality (keys (after cursor)))))
  :rule-classes :linear
  :enable cardinality-of-keys-of-from-cursor)

(defrule cardinality-of-keys-of-from-cursor-when-entryp-linear
  (implies (entryp cursor)
           (< (+ (tset::cardinality (keys (before cursor)))
                 (tset::cardinality (keys (after cursor))))
              (tset::cardinality (keys (from-cursor cursor)))))
  :rule-classes :linear
  :enable cardinality-of-keys-of-from-cursor)

(defrule cardinality-of-keys-of-from-cursor-when-not-entryp-linear
  (implies (not (entryp cursor))
           (<= (tset::cardinality (keys (from-cursor cursor)))
               (+ (tset::cardinality (keys (before cursor)))
                  (tset::cardinality (keys (after cursor))))))
  :rule-classes :linear
  :enable (cardinality-of-keys-of-from-cursor
           acl2::fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy partition-extra-rules
  '(cardinality-of-keys-of-from-cursor))
