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
(include-book "../delete-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-defs")
(include-book "nexts-prevs-defs")
(include-book "internal/zip-delete-entry-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../delete"))
(local (include-book "../cardinality"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))
(local (include-book "extensionality"))
(local (include-book "begin-end"))
(local (include-book "seek"))
(local (include-book "nexts-prevs"))
(local (include-book "internal/zipper"))
(local (include-book "internal/zip-seek"))
(local (include-book "internal/zip-delete-entry"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete-entry ((cursor cursorp))
  :guard (entryp cursor)
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Remove the entry a @(see cursor) is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The cursor is left at the hole where the entry was, and @(tsee before)
      and @(tsee after) are unchanged. The underlying set is as after a @(tsee
      delete) of the element. Logically, a cursor at a hole is left as it
      is.")
   (xdoc::p
     "A walk which removes entries moves on from that hole with @(tsee
      step-forward).")
   (xdoc::p
     "Time complexity: expected @($O(1)$), and @($O(\\log(n))$) in the worst
      case."))
  (mbe :logic (if (entryp cursor)
                  (seek (entry cursor)
                        (delete (entry cursor) (from-cursor cursor)))
                (cursor-fix cursor))
       :exec (zip-delete-entry cursor))
  :inline t
  :guard-hints
  (("Goal"
    :use (:instance setp-of-delete$inline
                    (x (entry cursor))
                    (set (from-cursor cursor)))
    :in-theory
    (enable* zip-delete-entry-becomes-zip-seek-of-zip-root-of-tree-delete
             seek
             delete
             from-cursor
             entry
             entryp
             break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule delete-entry-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (delete-entry cursor0)
                  (delete-entry cursor1)))
  :rule-classes :congruence
  :enable delete-entry)

(defruled delete-entry-when-not-entryp
  (implies (not (entryp cursor))
           (equal (delete-entry cursor)
                  (cursor-fix cursor)))
  :enable delete-entry)

(defrule delete-entry-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (equal (delete-entry cursor)
                  (cursor-fix cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by delete-entry-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-delete-entry
  (not (entryp (delete-entry cursor)))
  :enable delete-entry)

(defrule from-cursor-of-delete-entry
  (implies (entryp cursor)
           (equal (from-cursor (delete-entry cursor))
                  (delete (entry cursor) (from-cursor cursor))))
  :enable delete-entry)

(defrule before-of-delete-entry
  (equal (before (delete-entry cursor))
         (before cursor))
  :enable (delete-entry
           extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after
           <<-when-in-of-before-and-in-of-after
           data::<<-rules))

(defrule after-of-delete-entry
  (equal (after (delete-entry cursor))
         (after cursor))
  :enable (delete-entry
           extensionality
           in-of-from-cursor-becomes-in-of-before-or-entry-or-after
           <<-when-in-of-before-and-in-of-after
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-delete-entry
  (equal (beginp (delete-entry cursor))
         (emptyp (before cursor)))
  :enable beginp)

(defrule endp-of-delete-entry
  (equal (endp (delete-entry cursor))
         (emptyp (after cursor)))
  :enable endp)

(defrule nexts-of-delete-entry
  (implies (entryp cursor)
           (equal (nexts (delete-entry cursor))
                  (- (nexts cursor) 1)))
  :enable nexts)

(defrule prevs-of-delete-entry
  (implies (entryp cursor)
           (equal (prevs (delete-entry cursor))
                  (- (prevs cursor) 1)))
  :enable prevs)
