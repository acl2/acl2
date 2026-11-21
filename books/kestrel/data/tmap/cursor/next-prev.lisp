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
(include-book "../min-max-defs")
(include-book "../update-defs")
(include-book "../delete-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "step-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/tset/in" :dir :system))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../update"))
(local (include-book "../delete"))
(local (include-book "../min-max"))
(local (include-book "../submap"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "from-cursor"))
(local (include-book "begin-end"))
(local (include-book "step"))

(local (include-book "internal/zip-step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define next ((cursor cursorp))
  :guard (entryp cursor)
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Move a @(see cursor) from an entry to the next entry, or to @(tsee
          end) if there is none."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is two @(tsee step-forward)s.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) in the worst case, and @($O(1)$)
      amortized over a walk."))
  (mbe :logic (step-forward (step-forward cursor))
       :exec (zip-next (cursor-fix cursor)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* step-forward
                                            zip-next
                                            entryp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prev ((cursor cursorp))
  :guard (entryp cursor)
  :returns (cursor$ cursorp)
  :parents (cursor)
  :short "Move a @(see cursor) from an entry to the previous entry, or to
          @(tsee begin) if there is none."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is two @(tsee step-backward)s.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) in the worst case, and @($O(1)$)
      amortized over a walk."))
  (mbe :logic (step-backward (step-backward cursor))
       :exec (zip-prev (cursor-fix cursor)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* step-backward
                                            zip-prev
                                            entryp
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule next-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (next cursor0)
                  (next cursor1)))
  :rule-classes :congruence
  :enable next)

(defrule prev-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (prev cursor0)
                  (prev cursor1)))
  :rule-classes :congruence
  :enable prev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-next
  (equal (from-cursor (next cursor))
         (from-cursor cursor))
  :enable next)

(defrule from-cursor-of-prev
  (equal (from-cursor (prev cursor))
         (from-cursor cursor))
  :enable prev)

;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-next
  (equal (entryp (next cursor))
         (and (entryp cursor)
              (not (emptyp (after cursor)))))
  :cases ((entryp cursor))
  :enable next)

(defrule endp-of-next
  (implies (entryp cursor)
           (equal (endp (next cursor))
                  (emptyp (after cursor))))
  :enable (next
           endp
           not))

(defrule beginp-of-next
  (equal (beginp (next cursor))
         (emptyp (from-cursor cursor)))
  :cases ((entryp cursor)
          (endp cursor))
  :use ((:instance tset::not-emptyp-when-in
                   (x (entry-key cursor))
                   (set (keys (from-cursor cursor))))
        (:instance submap-when-emptyp-of-arg2
                   (x (after cursor))
                   (y (from-cursor cursor))))
  :enable (next
           beginp
           before-when-endp)
  :disable submap-when-emptyp-of-arg2)

(defrule before-of-next
  (implies (entryp cursor)
           (equal (before (next cursor))
                  (update (entry-key cursor)
                          (entry-val cursor)
                          (before cursor))))
  :enable next)

(defrule after-of-next
  (equal (after (next cursor))
         (delete (min-key (after cursor)) (after cursor)))
  :cases ((entryp cursor)
          (and (not (entryp cursor))
               (emptyp (after cursor))))
  :enable next)

(defrule entry-key-of-next
  (implies (entryp cursor)
           (equal (entry-key (next cursor))
                  (min-key (after cursor))))
  :enable next)

(defrule entry-val-of-next
  (implies (entryp cursor)
           (equal (entry-val (next cursor))
                  (min-val (after cursor))))
  :enable next)

;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-prev
  (equal (entryp (prev cursor))
         (and (entryp cursor)
              (not (emptyp (before cursor)))))
  :cases ((entryp cursor))
  :enable prev)

(defrule beginp-of-prev
  (implies (entryp cursor)
           (equal (beginp (prev cursor))
                  (emptyp (before cursor))))
  :enable (prev
           beginp
           not))

(defrule endp-of-prev
  (equal (endp (prev cursor))
         (emptyp (from-cursor cursor)))
  :cases ((entryp cursor)
          (beginp cursor))
  :use ((:instance tset::not-emptyp-when-in
                   (x (entry-key cursor))
                   (set (keys (from-cursor cursor))))
        (:instance submap-when-emptyp-of-arg2
                   (x (before cursor))
                   (y (from-cursor cursor))))
  :enable (prev
           endp
           after-when-beginp)
  :disable submap-when-emptyp-of-arg2)

(defrule after-of-prev
  (implies (entryp cursor)
           (equal (after (prev cursor))
                  (update (entry-key cursor)
                          (entry-val cursor)
                          (after cursor))))
  :enable prev)

(defrule before-of-prev
  (equal (before (prev cursor))
         (delete (max-key (before cursor)) (before cursor)))
  :cases ((entryp cursor)
          (and (not (entryp cursor))
               (emptyp (before cursor))))
  :enable prev)

(defrule entry-key-of-prev
  (implies (entryp cursor)
           (equal (entry-key (prev cursor))
                  (max-key (before cursor))))
  :enable prev)

(defrule entry-val-of-prev
  (implies (entryp cursor)
           (equal (entry-val (prev cursor))
                  (max-val (before cursor))))
  :enable prev)

;;;;;;;;;;;;;;;;;;;;

(defrule prev-of-next
  (implies (not (emptyp (after cursor)))
           (equal (prev (next cursor))
                  (cursor-fix cursor)))
  :cases ((entryp cursor))
  :enable (next
           prev
           endp))

(defrule next-of-prev
  (implies (not (emptyp (before cursor)))
           (equal (next (prev cursor))
                  (cursor-fix cursor)))
  :cases ((entryp cursor))
  :enable (next
           prev
           beginp))
