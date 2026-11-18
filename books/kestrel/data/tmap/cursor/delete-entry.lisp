; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "../map-defs")
(include-book "../delete-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-defs")
(include-book "nexts-prevs-defs")
(include-book "update-entry-defs")
(include-book "update-hole-defs")
(include-book "internal/zip-delete-entry-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../update"))
(local (include-book "../delete"))
(local (include-book "../size"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))
(local (include-book "extensionality"))
(local (include-book "begin-end"))
(local (include-book "seek"))
(local (include-book "nexts-prevs"))
(local (include-book "update-entry"))
(local (include-book "update-hole"))
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
      and @(tsee after) are unchanged. The underlying map is as after a @(tsee
      delete) of the key. Logically, a cursor at a hole is left as it is.")
   (xdoc::p
     "A walk which removes entries moves on from that hole with @(tsee
      step-forward).")
   (xdoc::p
     "Time complexity: expected @($O(1)$), and @($O(\\log(n))$) in the worst
      case."))
  (mbe :logic (if (entryp cursor)
                  (seek (entry-key cursor)
                        (delete (entry-key cursor) (from-cursor cursor)))
                (cursor-fix cursor))
       :exec (zip-delete-entry cursor))
  :inline t
  :guard-hints
  (("Goal"
    :use (:instance mapp-of-delete$inline
                    (key (entry-key cursor))
                    (map (from-cursor cursor)))
    :in-theory
    (enable* zip-delete-entry-becomes-zip-seek-of-zip-root-of-tree-delete
             seek
             delete
             from-cursor
             entry-key
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
                  (delete (entry-key cursor) (from-cursor cursor))))
  :enable delete-entry)

(defrule before-of-delete-entry
  (equal (before (delete-entry cursor))
         (before cursor))
  :enable (delete-entry
           extensionality
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after
           <<-when-in-of-keys-of-before-and-in-of-keys-of-after
           lookup-when-not-in-of-keys
           data::<<-rules))

(defrule after-of-delete-entry
  (equal (after (delete-entry cursor))
         (after cursor))
  :enable (delete-entry
           extensionality
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after
           <<-when-in-of-keys-of-before-and-in-of-keys-of-after
           lookup-when-not-in-of-keys
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

;;;;;;;;;;;;;;;;;;;;

(defrule update-hole-of-entry-key-and-entry-val-and-delete-entry
  (implies (entryp cursor)
           (equal (update-hole (entry-key cursor)
                               (entry-val cursor)
                               (delete-entry cursor))
                  (cursor-fix cursor)))
  :enable (cursor-extensionality-when-entryp
           extensionality))

(defrule delete-entry-of-update-hole
  (equal (delete-entry (update-hole key val cursor))
         (seek key (delete key (from-cursor cursor))))
  :enable delete-entry)

(defrule delete-entry-of-update-entry
  (equal (delete-entry (update-entry val cursor))
         (delete-entry cursor))
  :cases ((entryp cursor))
  :enable delete-entry)
