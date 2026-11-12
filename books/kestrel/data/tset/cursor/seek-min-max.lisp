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
(include-book "../min-max-defs")
(include-book "../delete-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "step-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "../set"))
(local (include-book "../min-max"))
(local (include-book "../delete"))
(local (include-book "cursor"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "internal/before-after"))
(local (include-book "begin-end"))
(local (include-book "step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek-min ((set setp))
  :returns (cursor cursorp)
  :parents (cursor)
  :short "Construct a @(see cursor) at the least entry of a @(see tset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is one @(tsee step-forward) from @(tsee begin). So over
      an empty @(see tset), where there is no entry, it is the one hole.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$)."))
  (mbe :logic (step-forward (begin set))
       :exec (zip-min (fix set)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* step-forward
                                            begin
                                            zip-min
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seek-max ((set setp))
  :returns (cursor cursorp)
  :parents (cursor)
  :short "Construct a @(see cursor) at the greatest entry of a @(see tset)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Logically, this is one @(tsee step-backward) from @(tsee end). So over
      an empty @(see tset), where there is no entry, it is the one hole.")
   (xdoc::p
     "Time complexity: @($O(\\log(n))$)."))
  (mbe :logic (step-backward (end set))
       :exec (zip-max (fix set)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable* step-backward
                                            end
                                            zip-max
                                            break-abstraction))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t seek-min) (:t seek-max)))

(defrule seek-min-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (seek-min set0)
                  (seek-min set1)))
  :rule-classes :congruence
  :enable seek-min)

(defrule seek-max-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (seek-max set0)
                  (seek-max set1)))
  :rule-classes :congruence
  :enable seek-max)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minp ((cursor cursorp))
  :type-prescription :none
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
  :type-prescription :none
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

(defrule before-when-minp-cheap
  (implies (minp cursor)
           (equal (before cursor)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by before-when-minp)

(defruled after-when-maxp
  (implies (maxp cursor)
           (equal (after cursor)
                  (empty)))
  :enable (maxp
           emptyp-alt-definition))

(defrule after-when-maxp-cheap
  (implies (maxp cursor)
           (equal (after cursor)
                  (empty)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by after-when-maxp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule from-cursor-of-seek-min
  (equal (from-cursor (seek-min set))
         (fix set))
  :enable seek-min)

(defrule from-cursor-of-seek-max
  (equal (from-cursor (seek-max set))
         (fix set))
  :enable seek-max)

(defrule entryp-of-seek-min
  (equal (entryp (seek-min set))
         (not (emptyp set)))
  :enable seek-min)

(defrule entryp-of-seek-max
  (equal (entryp (seek-max set))
         (not (emptyp set)))
  :enable seek-max)

(defrule before-of-seek-min
  (equal (before (seek-min set))
         (empty))
  :enable seek-min)

(defrule after-of-seek-max
  (equal (after (seek-max set))
         (empty))
  :enable seek-max)

(defrule after-of-seek-min
  (equal (after (seek-min set))
         (delete (min set) set))
  :enable seek-min)

(defrule before-of-seek-max
  (equal (before (seek-max set))
         (delete (max set) set))
  :enable seek-max)

(defrule entry-of-seek-min
  (equal (entry (seek-min set))
         (min set))
  :enable seek-min)

(defrule entry-of-seek-max
  (equal (entry (seek-max set))
         (max set))
  :enable seek-max)

(defrule endp-of-seek-min
  (equal (endp (seek-min set))
         (emptyp set))
  :enable (endp
           not))

(defrule beginp-of-seek-max
  (equal (beginp (seek-max set))
         (emptyp set))
  :enable (beginp
           not))

(defrule minp-of-seek-min
  (equal (minp (seek-min set))
         (not (emptyp set)))
  :enable minp)

(defrule maxp-of-seek-max
  (equal (maxp (seek-max set))
         (not (emptyp set)))
  :enable maxp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy seek-min-max-extra-rules
  '(entryp-when-minp
    entryp-when-maxp
    not-minp-when-not-entryp
    not-maxp-when-not-entryp
    before-when-minp
    after-when-maxp))
