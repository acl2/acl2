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

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/min-max-defs" :dir :system)

(include-book "../map-defs")
(include-book "../keys-defs")
(include-book "../size-defs")
(include-book "../min-max-defs")
(include-book "../update-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-min-max-defs")
(include-book "seek-defs")
(include-book "nexts-prevs-defs")
(include-book "update-entry-defs")
(include-book "internal/zip-update-hole-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/insert" :dir :system))

(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "../internal/tree"))
(local (include-book "../internal/keys"))
(local (include-book "../internal/lookup"))
(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../min-max"))
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
(local (include-book "update-entry"))
(local (include-book "internal/zipper"))
(local (include-book "internal/zip-seek"))
(local (include-book "internal/zip-update-hole"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adding an entry at the hole of an unsuccessful search gives the cursor which
;; a search of the updated map would.

(defrulel cursorp-of-zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (cursorp (zip-update-hole key val (seek key map))))
  :enable (cursorp
           mapp
           seek
           keys
           break-abstraction))

(defrulel entryp-of-zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (entryp (zip-update-hole key val (seek key map))))
  :enable entryp)

(defrulel entry-key-of-zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (equal (entry-key (zip-update-hole key val (seek key map)))
                  key))
  :enable entry-key)

(defrulel in-of-keys-of-from-cursor-of-zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (equal (tset::in x (keys (from-cursor
                                      (zip-update-hole key val (seek key map)))))
                  (or (equal x key)
                      (tset::in x (keys map)))))
  :use cursorp-of-zip-update-hole-of-seek
  :enable (from-cursor
           keys
           seek
           cursorp
           break-abstraction)
  :disable cursorp-of-zip-update-hole-of-seek)

(defrulel lookup-of-from-cursor-of-zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (equal (lookup x
                          (from-cursor
                            (zip-update-hole key val (seek key map)))
                          :default default)
                  (if (equal x key)
                      val
                    (lookup x map :default default))))
  :use (cursorp-of-zip-update-hole-of-seek
        in-of-keys-of-from-cursor-of-zip-update-hole-of-seek)
  :enable (from-cursor
           lookup
           keys
           seek
           cursorp
           break-abstraction)
  :disable (cursorp-of-zip-update-hole-of-seek
            in-of-keys-of-from-cursor-of-zip-update-hole-of-seek))

(defrulel from-cursor-of-zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (equal (from-cursor (zip-update-hole key val (seek key map)))
                  (update key val map)))
  :enable extensionality)

(defruledl tree-empty-p-of-focus-when-not-entryp
  (implies (and (cursorp cursor)
                (not (entryp cursor)))
           (tree-empty-p (zip->focus cursor)))
  :enable entryp)

(defruled in-of-keys-of-from-cursor-when-not-entryp
  (implies (and (not (entryp cursor))
                (or (emptyp (before cursor))
                    (<< (tset::max (keys (before cursor))) key))
                (or (emptyp (after cursor))
                    (<< key (tset::min (keys (after cursor))))))
           (not (tset::in key (keys (from-cursor cursor)))))
  :use (:instance entryp-of-seek
                  (x key)
                  (map (from-cursor cursor)))
  :enable seek-of-from-cursor-when-not-entryp
  :disable entryp-of-seek)

(defruledl zip-update-hole-of-seek
  (implies (not (tset::in key (keys map)))
           (equal (zip-update-hole key val (seek key map))
                  (seek key (update key val map))))
  :enable cursor-extensionality-when-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-hole
  (key
   val
   (cursor cursorp))
  :guard (and (not (entryp cursor))
              (or (emptyp (before cursor))
                  (<< (max-key (before cursor)) key))
              (or (emptyp (after cursor))
                  (<< key (min-key (after cursor)))))
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Add an entry at the hole a @(see cursor) is at."
  :long
  (xdoc::topstring
   (xdoc::p
     "The key must belong at the hole: above every key @(tsee before) the
      cursor and below every key @(tsee after) it. This holds of the hole
      which a @(tsee seek) of the key ends at. The cursor is left at the new
      entry, and @(tsee before) and @(tsee after) are unchanged. The
      underlying map is as after an @(tsee update) of the key.")
   (xdoc::p
     "Logically, this is the @(tsee seek) of the key in the updated map,
      wherever the cursor is.")
   (xdoc::p
     "Time complexity: expected @($O(1)$), aside from hashing the key, and
      @($O(\\log(n))$) in the worst case."))
  (mbe :logic (seek key (update key val (from-cursor cursor)))
       :exec (zip-update-hole key val cursor))
  :inline t
  :guard-hints
  (("Goal" :use (:instance zip-update-hole-of-seek
                           (map (from-cursor cursor)))
           :in-theory (enable seek-of-from-cursor-when-not-entryp
                              in-of-keys-of-from-cursor-when-not-entryp
                              tree-empty-p-of-focus-when-not-entryp
                              zipp-when-cursorp-forward-chaining))))

;;;;;;;;;;;;;;;;;;;;

(defrule update-hole-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (update-hole key val cursor0)
                  (update-hole key val cursor1)))
  :rule-classes :congruence
  :enable update-hole)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-update-hole
  (equal (from-cursor (update-hole key val cursor))
         (update key val (from-cursor cursor)))
  :enable update-hole)

(defrule entryp-of-update-hole
  (entryp (update-hole key val cursor))
  :enable update-hole)

(defrule entry-key-of-update-hole
  (equal (entry-key (update-hole key val cursor))
         key)
  :enable update-hole)

(defrule entry-val-of-update-hole
  (equal (entry-val (update-hole key val cursor))
         val)
  :enable update-hole)

(defrule before-of-update-hole
  (equal (before (update-hole key val cursor))
         (before (seek key (from-cursor cursor))))
  :enable (update-hole
           extensionality
           data::<<-rules))

(defrule after-of-update-hole
  (equal (after (update-hole key val cursor))
         (after (seek key (from-cursor cursor))))
  :enable (update-hole
           extensionality
           data::<<-rules))

;;;;;;;;;;;;;;;;;;;;

(defrule beginp-of-update-hole
  (not (beginp (update-hole key val cursor)))
  :enable beginp)

(defrule endp-of-update-hole
  (not (endp (update-hole key val cursor)))
  :enable endp)

(defrule minp-of-update-hole
  (equal (minp (update-hole key val cursor))
         (emptyp (before (seek key (from-cursor cursor)))))
  :enable minp)

(defrule maxp-of-update-hole
  (equal (maxp (update-hole key val cursor))
         (emptyp (after (seek key (from-cursor cursor)))))
  :enable maxp)

(defrule nexts-of-update-hole
  (equal (nexts (update-hole key val cursor))
         (+ 1 (size (after (seek key (from-cursor cursor))))))
  :enable nexts)

(defrule prevs-of-update-hole
  (equal (prevs (update-hole key val cursor))
         (+ 1 (size (before (seek key (from-cursor cursor))))))
  :enable prevs)

;;;;;;;;;;;;;;;;;;;;

(defrule update-entry-of-update-hole
  (equal (update-entry val1 (update-hole key val0 cursor))
         (update-hole key val1 cursor))
  :enable cursor-extensionality-when-entryp)
