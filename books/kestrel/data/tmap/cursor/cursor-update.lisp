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
(include-book "internal/zip-update-defs")

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
(local (include-book "internal/zip-update"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The view of a cursor whose zipper has had its value replaced.

(defrulel cursorp-of-zip-update-of-cursor-fix
  (cursorp (zip-update val (cursor-fix cursor)))
  :use mapp-of-zip-plug-of-cursor-fix
  :enable (cursorp
           mapp)
  :disable mapp-of-zip-plug-of-cursor-fix)

(defrulel entryp-of-zip-update-of-cursor-fix
  (equal (entryp (zip-update val (cursor-fix cursor)))
         (entryp cursor))
  :enable entryp)

(defrulel entry-key-of-zip-update-of-cursor-fix
  (equal (entry-key (zip-update val (cursor-fix cursor)))
         (entry-key cursor))
  :enable entry-key)

(defrulel entry-val-of-zip-update-of-cursor-fix
  (implies (entryp cursor)
           (equal (entry-val (zip-update val (cursor-fix cursor)))
                  val))
  :enable (entry-val
           entryp))

(defrulel before-of-zip-update-of-cursor-fix
  (equal (before (zip-update val (cursor-fix cursor)))
         (before cursor))
  :enable before)

(defrulel after-of-zip-update-of-cursor-fix
  (equal (after (zip-update val (cursor-fix cursor)))
         (after cursor))
  :enable after)

(defrulel from-cursor-of-zip-update-of-cursor-fix
  (implies (entryp cursor)
           (equal (from-cursor (zip-update val (cursor-fix cursor)))
                  (update (entry-key cursor) val (from-cursor cursor))))
  :enable (extensionality
           in-of-keys-of-from-cursor-becomes-in-of-keys-of-before-or-entry-key-or-after
           lookup-of-from-cursor-becomes-lookup-of-before-or-entry-val-or-after))

(defruledl seek-of-entry-key-and-update-of-from-cursor
  (implies (entryp cursor)
           (equal (seek (entry-key cursor)
                        (update (entry-key cursor) val (from-cursor cursor)))
                  (zip-update val (cursor-fix cursor))))
  :enable cursor-extensionality-when-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursor-update
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
       :exec (zip-update val (cursor-fix cursor)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* seek-of-entry-key-and-update-of-from-cursor
                                            entryp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule cursor-update-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (cursor-update val cursor0)
                  (cursor-update val cursor1)))
  :rule-classes :congruence
  :enable cursor-update)

(defruled cursor-update-when-not-entryp
  (implies (not (entryp cursor))
           (equal (cursor-update val cursor)
                  (cursor-fix cursor)))
  :enable cursor-update)

(defrule cursor-update-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (equal (cursor-update val cursor)
                  (cursor-fix cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by cursor-update-when-not-entryp)

(defruledl cursor-update-becomes-zip-update
  (equal (cursor-update val cursor)
         (zip-update val (cursor-fix cursor)))
  :enable (cursor-update
           seek-of-entry-key-and-update-of-from-cursor
           zip-update
           entryp
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-cursor-update
  (equal (entryp (cursor-update val cursor))
         (entryp cursor))
  :enable cursor-update-becomes-zip-update)

(defrule before-of-cursor-update
  (equal (before (cursor-update val cursor))
         (before cursor))
  :enable cursor-update-becomes-zip-update)

(defrule after-of-cursor-update
  (equal (after (cursor-update val cursor))
         (after cursor))
  :enable cursor-update-becomes-zip-update)

(defrule entry-key-of-cursor-update
  (equal (entry-key (cursor-update val cursor))
         (entry-key cursor))
  :enable cursor-update-becomes-zip-update)

(defrule entry-val-of-cursor-update
  (implies (entryp cursor)
           (equal (entry-val (cursor-update val cursor))
                  val))
  :enable cursor-update-becomes-zip-update)

(defrule from-cursor-of-cursor-update
  (implies (entryp cursor)
           (equal (from-cursor (cursor-update val cursor))
                  (update (entry-key cursor) val (from-cursor cursor))))
  :enable cursor-update-becomes-zip-update)

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-cursor-update
  (equal (beginp (cursor-update val cursor))
         (beginp cursor))
  :enable beginp)

(defrule endp-of-cursor-update
  (equal (endp (cursor-update val cursor))
         (endp cursor))
  :enable endp)

(defrule minp-of-cursor-update
  (equal (minp (cursor-update val cursor))
         (minp cursor))
  :enable minp)

(defrule maxp-of-cursor-update
  (equal (maxp (cursor-update val cursor))
         (maxp cursor))
  :enable maxp)

(defrule nexts-of-cursor-update
  (equal (nexts (cursor-update val cursor))
         (nexts cursor))
  :enable nexts)

(defrule prevs-of-cursor-update
  (equal (prevs (cursor-update val cursor))
         (prevs cursor))
  :enable prevs)

;;;;;;;;;;;;;;;;;;;;

(defrule cursor-update-of-cursor-update
  (equal (cursor-update val1 (cursor-update val0 cursor))
         (cursor-update val1 cursor))
  :cases ((entryp cursor))
  :enable cursor-extensionality-when-entryp)

(defrule cursor-update-of-entry-val
  (equal (cursor-update (entry-val cursor) cursor)
         (cursor-fix cursor))
  :cases ((entryp cursor))
  :enable cursor-extensionality-when-entryp)
