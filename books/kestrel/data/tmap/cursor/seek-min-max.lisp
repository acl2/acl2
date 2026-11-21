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
(include-book "../delete-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "step-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../map"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../min-max"))
(local (include-book "../delete"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "internal/before-after"))
(local (include-book "begin-end"))
(local (include-book "step"))

(local (include-book "internal/zip-step"))
(local (include-book "internal/zip-step-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek-min ((map mapp))
  :returns (cursor cursorp)
  :parents (cursor)
  :short "Construct a @(see cursor) at the least entry of a @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is one @(tsee step-forward) from @(tsee begin). So over
      an empty @(see tmap), where there is no entry, it is the one hole.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$)."))
  (mbe :logic (step-forward (begin map))
       :exec (zip-min (fix map)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* step-forward
                                            begin
                                            zip-min
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek-max ((map mapp))
  :returns (cursor cursorp)
  :parents (cursor)
  :short "Construct a @(see cursor) at the greatest entry of a @(see tmap)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is one @(tsee step-backward) from @(tsee end). So over
      an empty @(see tmap), where there is no entry, it is the one hole.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$)."))
  (mbe :logic (step-backward (end map))
       :exec (zip-max (fix map)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* step-backward
                                            end
                                            zip-max
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule seek-min-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (seek-min map0)
                  (seek-min map1)))
  :rule-classes :congruence
  :enable seek-min)

(defrule seek-max-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (seek-max map0)
                  (seek-max map1)))
  :rule-classes :congruence
  :enable seek-max)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minp ((cursor cursorp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Check whether a @(see cursor) is at the least entry."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (and (entryp cursor)
                   (emptyp (before cursor)))
       :exec (zip-at-min-p (cursor-fix cursor)))
  :inline t
  :guard-hints
  (("Goal" :in-theory (enable* entryp
                               emptyp-of-before-becomes-not-consp
                               zip-at-min-p-becomes-not-consp-of-zip-before
                               break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maxp ((cursor cursorp))
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :parents (cursor)
  :short "Check whether a @(see cursor) is at the greatest entry."
  :long
  (xdoc::topstring-p
    "Time complexity: @($O(\\log(n))$).")
  (mbe :logic (and (entryp cursor)
                   (emptyp (after cursor)))
       :exec (zip-at-max-p (cursor-fix cursor)))
  :inline t
  :guard-hints
  (("Goal" :in-theory (enable* entryp
                               emptyp-of-after-becomes-not-consp
                               zip-at-max-p-becomes-not-consp-of-zip-after
                               break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(defrule minp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (minp cursor0)
                  (minp cursor1)))
  :rule-classes :congruence
  :enable minp)

(defrule maxp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (maxp cursor0)
                  (maxp cursor1)))
  :rule-classes :congruence
  :enable maxp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled entryp-when-minp
  (implies (minp cursor)
           (entryp cursor))
  :enable minp)

(defrule entryp-when-minp-forward-chaining
  (implies (minp cursor)
           (entryp cursor))
  :rule-classes :forward-chaining
  :by entryp-when-minp)

(defruled entryp-when-maxp
  (implies (maxp cursor)
           (entryp cursor))
  :enable maxp)

(defrule entryp-when-maxp-forward-chaining
  (implies (maxp cursor)
           (entryp cursor))
  :rule-classes :forward-chaining
  :by entryp-when-maxp)

(defruled not-minp-when-not-entryp
  (implies (not (entryp cursor))
           (not (minp cursor))))

(defrule not-minp-when-not-entryp-forward-chaining
  (implies (not (entryp cursor))
           (not (minp cursor)))
  :rule-classes :forward-chaining
  :by not-minp-when-not-entryp)

(defruled not-maxp-when-not-entryp
  (implies (not (entryp cursor))
           (not (maxp cursor))))

(defrule not-maxp-when-not-entryp-forward-chaining
  (implies (not (entryp cursor))
           (not (maxp cursor)))
  :rule-classes :forward-chaining
  :by not-maxp-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;

(defruled before-when-minp
  (implies (minp cursor)
           (equal (before cursor)
                  (empty)))
  :enable (minp
           emptyp-alt-definition))

(defruled emptyp-of-before-when-minp
  (implies (minp cursor)
           (emptyp (before cursor)))
  :enable minp)

(defrule emptyp-of-before-when-minp-forward-chaining
  (implies (minp cursor)
           (emptyp (before cursor)))
  :rule-classes :forward-chaining
  :by emptyp-of-before-when-minp)

(defruled after-when-maxp
  (implies (maxp cursor)
           (equal (after cursor)
                  (empty)))
  :enable (maxp
           emptyp-alt-definition))

(defruled emptyp-of-after-when-maxp
  (implies (maxp cursor)
           (emptyp (after cursor)))
  :enable maxp)

(defrule emptyp-of-after-when-maxp-forward-chaining
  (implies (maxp cursor)
           (emptyp (after cursor)))
  :rule-classes :forward-chaining
  :by emptyp-of-after-when-maxp)

;;;;;;;;;;;;;;;;;;;;

(defruled not-emptyp-of-before-when-not-minp-and-entryp
  (implies (and (not (minp cursor))
                (entryp cursor))
           (not (emptyp (before cursor))))
  :enable minp)

(defrule not-emptyp-of-before-when-not-minp-and-entryp-forward-chaining
  (implies (and (not (minp cursor))
                (entryp cursor))
           (not (emptyp (before cursor))))
  :rule-classes :forward-chaining
  :by not-emptyp-of-before-when-not-minp-and-entryp)

(defruled not-emptyp-of-after-when-not-maxp-and-entryp
  (implies (and (not (maxp cursor))
                (entryp cursor))
           (not (emptyp (after cursor))))
  :enable maxp)

(defrule not-emptyp-of-after-when-not-maxp-and-entryp-forward-chaining
  (implies (and (not (maxp cursor))
                (entryp cursor))
           (not (emptyp (after cursor))))
  :rule-classes :forward-chaining
  :by not-emptyp-of-after-when-not-maxp-and-entryp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-seek-min
  (equal (from-cursor (seek-min map))
         (fix map))
  :enable seek-min)

(defrule from-cursor-of-seek-max
  (equal (from-cursor (seek-max map))
         (fix map))
  :enable seek-max)

(defrule entryp-of-seek-min
  (equal (entryp (seek-min map))
         (not (emptyp map)))
  :enable seek-min)

(defrule entryp-of-seek-max
  (equal (entryp (seek-max map))
         (not (emptyp map)))
  :enable seek-max)

(defrule before-of-seek-min
  (equal (before (seek-min map))
         (empty))
  :enable seek-min)

(defrule after-of-seek-max
  (equal (after (seek-max map))
         (empty))
  :enable seek-max)

(defrule after-of-seek-min
  (equal (after (seek-min map))
         (delete (min-key map) map))
  :enable seek-min)

(defrule before-of-seek-max
  (equal (before (seek-max map))
         (delete (max-key map) map))
  :enable seek-max)

(defrule entry-key-of-seek-min
  (equal (entry-key (seek-min map))
         (min-key map))
  :enable seek-min)

(defrule entry-val-of-seek-min
  (equal (entry-val (seek-min map))
         (min-val map))
  :enable seek-min)

(defrule entry-key-of-seek-max
  (equal (entry-key (seek-max map))
         (max-key map))
  :enable seek-max)

(defrule entry-val-of-seek-max
  (equal (entry-val (seek-max map))
         (max-val map))
  :enable seek-max)

(defrule beginp-of-seek-min
  (equal (beginp (seek-min map))
         (emptyp map))
  :enable (beginp
           not))

(defrule endp-of-seek-max
  (equal (endp (seek-max map))
         (emptyp map))
  :enable (endp
           not))

(defrule endp-of-seek-min
  (equal (endp (seek-min map))
         (emptyp map))
  :enable (endp
           not))

(defrule beginp-of-seek-max
  (equal (beginp (seek-max map))
         (emptyp map))
  :enable (beginp
           not))

(defrule minp-of-seek-min
  (equal (minp (seek-min map))
         (not (emptyp map)))
  :enable minp)

(defrule maxp-of-seek-max
  (equal (maxp (seek-max map))
         (not (emptyp map)))
  :enable maxp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy seek-min-max-extra-rules
  '(entryp-when-minp
    entryp-when-maxp
    not-minp-when-not-entryp
    not-maxp-when-not-entryp
    before-when-minp
    emptyp-of-before-when-minp
    after-when-maxp
    emptyp-of-after-when-maxp
    not-emptyp-of-before-when-not-minp-and-entryp
    not-emptyp-of-after-when-not-maxp-and-entryp))
