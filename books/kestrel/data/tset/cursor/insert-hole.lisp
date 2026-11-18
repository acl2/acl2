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

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "../set-defs")
(include-book "../min-max-defs")
(include-book "../insert-defs")
(include-book "../delete-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "seek-defs")
(include-book "delete-entry-defs")
(include-book "internal/zip-insert-hole-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../internal/tree"))
(local (include-book "../internal/in"))
(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../min-max"))
(local (include-book "../insert"))
(local (include-book "../delete"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))
(local (include-book "extensionality"))
(local (include-book "seek"))
(local (include-book "delete-entry"))
(local (include-book "internal/zipper"))
(local (include-book "internal/zip-seek"))
(local (include-book "internal/zip-insert-hole"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adding an element at the hole of an unsuccessful search gives the cursor
;; which a search of the set with the element would.

(defrulel cursorp-of-zip-insert-hole-of-seek
  (implies (not (in x set))
           (cursorp (zip-insert-hole x (seek x set))))
  :enable (cursorp
           setp
           seek
           in
           break-abstraction))

(defrulel entryp-of-zip-insert-hole-of-seek
  (implies (not (in x set))
           (entryp (zip-insert-hole x (seek x set))))
  :enable entryp)

(defrulel entry-of-zip-insert-hole-of-seek
  (implies (not (in x set))
           (equal (entry (zip-insert-hole x (seek x set)))
                  x))
  :enable entry)

(defrulel in-of-from-cursor-of-zip-insert-hole-of-seek
  (implies (not (in x set))
           (equal (in y (from-cursor (zip-insert-hole x (seek x set))))
                  (or (equal y x)
                      (in y set))))
  :use cursorp-of-zip-insert-hole-of-seek
  :enable (from-cursor
           in
           seek
           cursorp
           break-abstraction)
  :disable cursorp-of-zip-insert-hole-of-seek)

(defrulel from-cursor-of-zip-insert-hole-of-seek
  (implies (not (in x set))
           (equal (from-cursor (zip-insert-hole x (seek x set)))
                  (insert x set)))
  :enable extensionality)

(defruledl zip-insert-hole-of-seek
  (implies (not (in x set))
           (equal (zip-insert-hole x (seek x set))
                  (seek x (insert x set))))
  :enable cursor-extensionality-when-entryp)

;;;;;;;;;;;;;;;;;;;;

(defruledl tree-empty-p-of-focus-when-not-entryp
  (implies (and (cursorp cursor)
                (not (entryp cursor)))
           (tree-empty-p (zip->focus cursor)))
  :enable entryp)

(defruledl in-of-from-cursor-when-not-entryp
  (implies (and (not (entryp cursor))
                (or (emptyp (before cursor))
                    (<< (max (before cursor)) x))
                (or (emptyp (after cursor))
                    (<< x (min (after cursor)))))
           (not (in x (from-cursor cursor))))
  :use (:instance entryp-of-seek
                  (set (from-cursor cursor)))
  :enable seek-of-from-cursor-when-not-entryp
  :disable entryp-of-seek)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert-hole
  (x
   (cursor cursorp))
  :guard (and (not (entryp cursor))
              (or (emptyp (before cursor))
                  (<< (max (before cursor)) x))
              (or (emptyp (after cursor))
                  (<< x (min (after cursor)))))
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Add an element at the hole a @(see cursor) is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The value must belong at the hole: above every element @(tsee before)
      the cursor and below every element @(tsee after) it. This holds of the
      hole which a @(tsee seek) of the value ends at. The cursor is left at
      the new entry, and @(tsee before) and @(tsee after) are unchanged. The
      underlying set is as after an @(tsee insert) of the value.")
   (xdoc::p
     "Logically, this is the @(tsee seek) of the value in the set with it
      inserted, wherever the cursor is.")
   (xdoc::p
     "Time complexity: expected @($O(1)$), aside from hashing the value, and
      @($O(\\log(n))$) in the worst case."))
  (mbe :logic (seek x (insert x (from-cursor cursor)))
       :exec (zip-insert-hole x cursor))
  :inline t
  :guard-hints
  (("Goal" :use (:instance zip-insert-hole-of-seek
                           (set (from-cursor cursor)))
           :in-theory (enable seek-of-from-cursor-when-not-entryp
                              in-of-from-cursor-when-not-entryp
                              tree-empty-p-of-focus-when-not-entryp
                              zipp-when-cursorp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule insert-hole-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (insert-hole x cursor0)
                  (insert-hole x cursor1)))
  :rule-classes :congruence
  :enable insert-hole)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-insert-hole
  (equal (from-cursor (insert-hole x cursor))
         (insert x (from-cursor cursor)))
  :enable insert-hole)

(defrule entryp-of-insert-hole
  (entryp (insert-hole x cursor))
  :enable insert-hole)

(defrule entry-of-insert-hole
  (equal (entry (insert-hole x cursor))
         x)
  :enable insert-hole)

(defrule before-of-insert-hole
  (equal (before (insert-hole x cursor))
         (before (seek x (from-cursor cursor))))
  :enable (insert-hole
           extensionality
           data::<<-rules))

(defrule after-of-insert-hole
  (equal (after (insert-hole x cursor))
         (after (seek x (from-cursor cursor))))
  :enable (insert-hole
           extensionality
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule delete-entry-of-insert-hole
  (equal (delete-entry (insert-hole x cursor))
         (seek x (delete x (from-cursor cursor))))
  :enable delete-entry)

(defrule insert-hole-of-entry-and-delete-entry
  (implies (entryp cursor)
           (equal (insert-hole (entry cursor) (delete-entry cursor))
                  (cursor-fix cursor)))
  :enable (cursor-extensionality-when-entryp
           extensionality))
