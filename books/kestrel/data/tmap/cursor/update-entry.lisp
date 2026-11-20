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
(include-book "../update-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-min-max-defs")
(include-book "seek-defs")
(include-book "nexts-prevs-defs")
(include-book "internal/zip-update-entry-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../update"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "from-cursor"))
(local (include-book "extensionality"))
(local (include-book "begin-end"))
(local (include-book "seek-min-max"))
(local (include-book "seek"))
(local (include-book "nexts-prevs"))
(local (include-book "internal/zipper"))
(local (include-book "internal/zip-side"))
(local (include-book "internal/zip-update-entry"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The view of a cursor whose zipper has had its value replaced.

(defrulel cursorp-of-zip-update-entry-of-cursor-fix
  (cursorp (zip-update-entry val (cursor-fix cursor)))
  :use mapp-of-zip-plug-of-cursor-fix
  :enable (cursorp
           mapp)
  :disable mapp-of-zip-plug-of-cursor-fix)

(defrulel entryp-of-zip-update-entry-of-cursor-fix
  (equal (entryp (zip-update-entry val (cursor-fix cursor)))
         (entryp cursor))
  :enable entryp)

(defrulel entry-key-of-zip-update-entry-of-cursor-fix
  (equal (entry-key (zip-update-entry val (cursor-fix cursor)))
         (entry-key cursor))
  :enable entry-key)

(defrulel entry-val-of-zip-update-entry-of-cursor-fix
  (implies (entryp cursor)
           (equal (entry-val (zip-update-entry val (cursor-fix cursor)))
                  val))
  :enable (entry-val
           entryp))

(defrulel before-of-zip-update-entry-of-cursor-fix
  (equal (before (zip-update-entry val (cursor-fix cursor)))
         (before cursor))
  :enable before)

(defrulel after-of-zip-update-entry-of-cursor-fix
  (equal (after (zip-update-entry val (cursor-fix cursor)))
         (after cursor))
  :enable after)

(defrulel from-cursor-of-zip-update-entry-of-cursor-fix
  (implies (entryp cursor)
           (equal (from-cursor (zip-update-entry val (cursor-fix cursor)))
                  (update (entry-key cursor) val (from-cursor cursor))))
  :enable (extensionality
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after))

(defruledl seek-of-entry-key-and-update-of-from-cursor
  (implies (entryp cursor)
           (equal (seek (entry-key cursor)
                        (update (entry-key cursor) val (from-cursor cursor)))
                  (zip-update-entry val (cursor-fix cursor))))
  :enable cursor-extensionality-when-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-entry
  (val
   (cursor cursorp))
  :guard (entryp cursor)
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Replace the value of the entry a @(see cursor) is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The cursor stays at the same key, and @(tsee before) and @(tsee after)
      are unchanged. The underlying map is as after an @(tsee update) of that
      key. Logically, a cursor at a hole is left as it is.")
   (xdoc::p
     "Time complexity: @($O(1)$)."))
  (mbe :logic (if (entryp cursor)
                  (seek (entry-key cursor)
                        (update (entry-key cursor) val (from-cursor cursor)))
                (cursor-fix cursor))
       :exec (zip-update-entry val (cursor-fix cursor)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* seek-of-entry-key-and-update-of-from-cursor
                                            entryp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule update-entry-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (update-entry val cursor0)
                  (update-entry val cursor1)))
  :rule-classes :congruence
  :enable update-entry)

(defruled update-entry-when-not-entryp
  (implies (not (entryp cursor))
           (equal (update-entry val cursor)
                  (cursor-fix cursor)))
  :enable update-entry)

(defrule update-entry-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (equal (update-entry val cursor)
                  (cursor-fix cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by update-entry-when-not-entryp)

(defruledl update-entry-becomes-zip-update-entry
  (equal (update-entry val cursor)
         (zip-update-entry val (cursor-fix cursor)))
  :enable (update-entry
           seek-of-entry-key-and-update-of-from-cursor
           zip-update-entry
           entryp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-update-entry
  (equal (entryp (update-entry val cursor))
         (entryp cursor))
  :enable update-entry-becomes-zip-update-entry)

(defrule before-of-update-entry
  (equal (before (update-entry val cursor))
         (before cursor))
  :enable update-entry-becomes-zip-update-entry)

(defrule after-of-update-entry
  (equal (after (update-entry val cursor))
         (after cursor))
  :enable update-entry-becomes-zip-update-entry)

(defrule entry-key-of-update-entry
  (equal (entry-key (update-entry val cursor))
         (entry-key cursor))
  :enable update-entry-becomes-zip-update-entry)

(defrule entry-val-of-update-entry
  (implies (entryp cursor)
           (equal (entry-val (update-entry val cursor))
                  val))
  :enable update-entry-becomes-zip-update-entry)

(defrule from-cursor-of-update-entry
  (implies (entryp cursor)
           (equal (from-cursor (update-entry val cursor))
                  (update (entry-key cursor) val (from-cursor cursor))))
  :enable update-entry-becomes-zip-update-entry)

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-update-entry
  (equal (beginp (update-entry val cursor))
         (beginp cursor))
  :enable beginp)

(defrule endp-of-update-entry
  (equal (endp (update-entry val cursor))
         (endp cursor))
  :enable endp)

(defrule minp-of-update-entry
  (equal (minp (update-entry val cursor))
         (minp cursor))
  :enable minp)

(defrule maxp-of-update-entry
  (equal (maxp (update-entry val cursor))
         (maxp cursor))
  :enable maxp)

(defrule nexts-of-update-entry
  (equal (nexts (update-entry val cursor))
         (nexts cursor))
  :enable nexts)

(defrule prevs-of-update-entry
  (equal (prevs (update-entry val cursor))
         (prevs cursor))
  :enable prevs)

;;;;;;;;;;;;;;;;;;;;

(defrule update-entry-of-update-entry
  (equal (update-entry val1 (update-entry val0 cursor))
         (update-entry val1 cursor))
  :cases ((entryp cursor))
  :enable cursor-extensionality-when-entryp)

(defrule update-entry-of-entry-val
  (equal (update-entry (entry-val cursor) cursor)
         (cursor-fix cursor))
  :cases ((entryp cursor))
  :enable cursor-extensionality-when-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy update-entry-extra-rules
  '(update-entry-when-not-entryp))
