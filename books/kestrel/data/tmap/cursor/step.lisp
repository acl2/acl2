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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/data/utilities/omap" :dir :system))
(local (include-book "kestrel/data/utilities/total-order/total-order" :dir :system))

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../update"))
(local (include-book "../min-max"))
(local (include-book "../delete"))
(local (include-book "../extensionality"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "internal/before-after"))
(local (include-book "from-cursor"))
(local (include-book "begin-end"))
(local (include-book "internal/begin-end"))

(local (include-book "internal/zipper"))
(local (include-book "internal/zip-step"))
(local (include-book "internal/zip-side"))
(local (include-book "internal/zip-order"))
(local (include-book "internal/zip-step-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-forward ((cursor cursorp))
  :returns (cursor$ cursorp
                    :hints (("Goal" :in-theory (enable* cursorp
                                                        break-abstraction))))
  :parents (cursor)
  :short "Move a @(see cursor) to the next position."
  :long
  (xdoc::topstring
   (xdoc::p
     "From an entry, this is the hole just after it; from a hole, the entry
      just after it. At @(tsee end) there is nothing after, and the cursor
      stays put.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) in the worst case, and @($O(1)$)
      amortized over a walk."))
  (zip-step-forward (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step-backward ((cursor cursorp))
  :returns (cursor$ cursorp
                    :hints (("Goal" :in-theory (enable* cursorp
                                                        break-abstraction))))
  :parents (cursor)
  :short "Move a @(see cursor) to the previous position."
  :long
  (xdoc::topstring
   (xdoc::p
     "From an entry, this is the hole just before it; from a hole, the entry
      just before it. At @(tsee begin) there is nothing before, and the cursor
      stays put.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$) in the worst case, and @($O(1)$)
      amortized over a walk."))
  (zip-step-backward (cursor-fix cursor))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule step-forward-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (step-forward cursor0)
                  (step-forward cursor1)))
  :rule-classes :congruence
  :enable step-forward)

(defrule step-backward-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (step-backward cursor0)
                  (step-backward cursor1)))
  :rule-classes :congruence
  :enable step-backward)

(defruled cursor-fix-of-zip-step-forward-of-cursor-fix
  (equal (cursor-fix (zip-step-forward (cursor-fix cursor)))
         (zip-step-forward (cursor-fix cursor)))
  :use cursorp-of-step-forward
  :enable step-forward)

(add-to-ruleset break-abstraction
                '(cursor-fix-of-zip-step-forward-of-cursor-fix))

(defruled cursor-fix-of-zip-step-backward-of-cursor-fix
  (equal (cursor-fix (zip-step-backward (cursor-fix cursor)))
         (zip-step-backward (cursor-fix cursor)))
  :use cursorp-of-step-backward
  :enable step-backward)

(add-to-ruleset break-abstraction
                '(cursor-fix-of-zip-step-backward-of-cursor-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-step-forward
  (equal (from-cursor (step-forward cursor))
         (from-cursor cursor))
  :enable (from-cursor
           step-forward
           break-abstraction))

(defrule from-cursor-of-step-backward
  (equal (from-cursor (step-backward cursor))
         (from-cursor cursor))
  :enable (from-cursor
           step-backward
           break-abstraction))

(defrule equal-of-step-forward-and-cursor-fix
  (equal (equal (step-forward cursor) (cursor-fix cursor))
         (endp cursor))
  :enable (step-forward
           endp-becomes-zip-at-end-p
           break-abstraction)
  :use (:instance equal-of-zip-step-forward-and-zip-fix
                  (zip (cursor-fix cursor))))

(defrule equal-of-step-backward-and-cursor-fix
  (equal (equal (step-backward cursor) (cursor-fix cursor))
         (beginp cursor))
  :enable (step-backward
           beginp-becomes-zip-at-begin-p
           break-abstraction)
  :use (:instance equal-of-zip-step-backward-and-zip-fix
                  (zip (cursor-fix cursor))))

(defrule equal-of-step-forward-and-arg1
  (equal (equal (step-forward cursor) cursor)
         (and (cursorp cursor)
              (endp cursor)))
  :use equal-of-step-forward-and-cursor-fix
  :disable equal-of-step-forward-and-cursor-fix)

(defrule equal-of-step-backward-and-arg1
  (equal (equal (step-backward cursor) cursor)
         (and (cursorp cursor)
              (beginp cursor)))
  :use equal-of-step-backward-and-cursor-fix
  :disable equal-of-step-backward-and-cursor-fix)

(defruled step-forward-when-endp
  (implies (endp cursor)
           (equal (step-forward cursor)
                  (cursor-fix cursor)))
  :use equal-of-step-forward-and-cursor-fix
  :disable equal-of-step-forward-and-cursor-fix)

(defrule step-forward-when-endp-cheap
  (implies (endp cursor)
           (equal (step-forward cursor)
                  (cursor-fix cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by step-forward-when-endp)

(defruled step-backward-when-beginp
  (implies (beginp cursor)
           (equal (step-backward cursor)
                  (cursor-fix cursor)))
  :use equal-of-step-backward-and-cursor-fix
  :disable equal-of-step-backward-and-cursor-fix)

(defrule step-backward-when-beginp-cheap
  (implies (beginp cursor)
           (equal (step-backward cursor)
                  (cursor-fix cursor)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by step-backward-when-beginp)

(defrule step-backward-of-step-forward
  (implies (not (endp cursor))
           (equal (step-backward (step-forward cursor))
                  (cursor-fix cursor)))
  :enable (step-forward
           step-backward
           endp-becomes-zip-at-end-p
           break-abstraction))

(defrule step-forward-of-step-backward
  (implies (not (beginp cursor))
           (equal (step-forward (step-backward cursor))
                  (cursor-fix cursor)))
  :enable (step-forward
           step-backward
           beginp-becomes-zip-at-begin-p
           break-abstraction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-step-forward
  (equal (entryp (step-forward cursor))
         (and (not (entryp cursor))
              (not (emptyp (after cursor)))))
  :enable (entryp
           step-forward
           emptyp-of-after-becomes-not-consp
           break-abstraction))

(defrule before-of-step-forward-when-entryp
  (implies (entryp cursor)
           (equal (before (step-forward cursor))
                  (update (entry-key cursor)
                          (entry-val cursor)
                          (before cursor))))
  :enable (extensionality
           lookup-of-before-becomes-assoc-equal
           step-forward
           entry-key
           entry-val
           entryp
           break-abstraction))

(defrule after-of-step-forward-when-entryp
  (implies (entryp cursor)
           (equal (after (step-forward cursor))
                  (after cursor)))
  :enable (extensionality
           lookup-of-after-becomes-assoc-equal
           step-forward
           entryp
           break-abstraction))

(defrule before-of-step-forward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (before (step-forward cursor))
                  (before cursor)))
  :enable (extensionality
           lookup-of-before-becomes-assoc-equal
           step-forward
           entryp
           break-abstraction))

(defrule entry-key-of-step-forward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry-key (step-forward cursor))
                  (min-key (after cursor))))
  :cases ((emptyp (after cursor)))
  :enable (min-of-keys-of-after-becomes-caar-of-zip-after
           emptyp-of-after-becomes-not-consp
           zip-at-end-p-becomes-not-consp-of-zip-after
           step-forward
           entry-key
           entryp
           break-abstraction))

(defrule entry-val-of-step-forward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry-val (step-forward cursor))
                  (min-val (after cursor))))
  :cases ((emptyp (after cursor)))
  :enable (min-of-keys-of-after-becomes-caar-of-zip-after
           lookup-of-after-becomes-assoc-equal
           emptyp-of-after-becomes-not-consp
           zip-at-end-p-becomes-not-consp-of-zip-after
           step-forward
           entry-val
           entryp
           data::assoc-equal-of-caar
           break-abstraction))

(defrule after-of-step-forward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (after (step-forward cursor))
                  (delete (min-key (after cursor)) (after cursor))))
  :enable (extensionality
           lookup-of-after-becomes-assoc-equal
           min-of-keys-of-after-becomes-caar-of-zip-after
           step-forward
           entryp
           data::assoc-equal-of-cdr-when-omapp
           break-abstraction))

(defrule endp-of-step-forward
  (equal (endp (step-forward cursor))
         (emptyp (after cursor)))
  :cases ((entryp cursor))
  :enable endp)

;;;;;;;;;;;;;;;;;;;;

(defrule entryp-of-step-backward
  (equal (entryp (step-backward cursor))
         (and (not (entryp cursor))
              (not (emptyp (before cursor)))))
  :enable (entryp
           step-backward
           emptyp-of-before-becomes-not-consp
           break-abstraction))

(defrule after-of-step-backward-when-entryp
  (implies (entryp cursor)
           (equal (after (step-backward cursor))
                  (update (entry-key cursor)
                          (entry-val cursor)
                          (after cursor))))
  :enable (extensionality
           lookup-of-after-becomes-assoc-equal
           step-backward
           entry-key
           entry-val
           entryp
           break-abstraction))

(defrule before-of-step-backward-when-entryp
  (implies (entryp cursor)
           (equal (before (step-backward cursor))
                  (before cursor)))
  :enable (extensionality
           lookup-of-before-becomes-assoc-equal
           step-backward
           entryp
           break-abstraction))

(defrule after-of-step-backward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (after (step-backward cursor))
                  (after cursor)))
  :enable (extensionality
           lookup-of-after-becomes-assoc-equal
           step-backward
           entryp
           break-abstraction))

(defrule entry-key-of-step-backward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry-key (step-backward cursor))
                  (max-key (before cursor))))
  :cases ((emptyp (before cursor)))
  :enable (max-of-keys-of-before-becomes-caar-of-last-of-zip-before
           emptyp-of-before-becomes-not-consp
           zip-at-begin-p-becomes-not-consp-of-zip-before
           step-backward
           entry-key
           entryp
           break-abstraction))

(defrule entry-val-of-step-backward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (entry-val (step-backward cursor))
                  (max-val (before cursor))))
  :cases ((emptyp (before cursor)))
  :enable (max-of-keys-of-before-becomes-caar-of-last-of-zip-before
           lookup-of-before-becomes-assoc-equal
           emptyp-of-before-becomes-not-consp
           zip-at-begin-p-becomes-not-consp-of-zip-before
           step-backward
           entry-val
           entryp
           data::assoc-equal-of-caar-of-last-when-omapp
           break-abstraction))

(defrule before-of-step-backward-when-not-entryp
  (implies (not (entryp cursor))
           (equal (before (step-backward cursor))
                  (delete (max-key (before cursor)) (before cursor))))
  :enable (extensionality
           lookup-of-before-becomes-assoc-equal
           max-of-keys-of-before-becomes-caar-of-last-of-zip-before
           step-backward
           entryp
           data::assoc-equal-of-butlast-when-omapp
           break-abstraction))

(defrule beginp-of-step-backward
  (equal (beginp (step-backward cursor))
         (emptyp (before cursor)))
  :cases ((entryp cursor))
  :enable beginp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy step-extra-rules
  '(step-forward-when-endp
    step-backward-when-beginp))
