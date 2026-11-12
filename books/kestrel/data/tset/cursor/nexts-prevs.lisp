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

(include-book "../cardinality-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "begin-end-defs")
(include-book "seek-min-max-defs")
(include-book "next-prev-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))

(local (include-book "../set"))
(local (include-book "../min-max"))
(local (include-book "../delete"))
(local (include-book "../cardinality"))
(local (include-book "entry"))
(local (include-book "before-after"))
(local (include-book "begin-end"))
(local (include-book "step"))
(local (include-book "seek-min-max"))
(local (include-book "next-prev"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nexts ((cursor cursorp))
  :type-prescription :none
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (cursor)
  :short "The number of entries at or after a @(see cursor)."
  :long
  (xdoc::topstring-p
    "This is a measure for a walk with @(tsee next): it decreases until the
     cursor is at @(tsee end).")
  (+ (cardinality (after cursor))
     (if (entryp cursor) 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prevs ((cursor cursorp))
  :type-prescription :none
  :returns (measure natp :rule-classes (:rewrite :type-prescription))
  :parents (cursor)
  :short "The number of entries at or before a @(see cursor)."
  :long
  (xdoc::topstring-p
    "This is a measure for a walk with @(tsee prev): it decreases until the
     cursor is at @(tsee begin).")
  (+ (cardinality (before cursor))
     (if (entryp cursor) 1 0)))

;;;;;;;;;;;;;;;;;;;;

(defrule nexts-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (nexts cursor0)
                  (nexts cursor1)))
  :rule-classes :congruence
  :enable nexts)

(defrule prevs-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (prevs cursor0)
                  (prevs cursor1)))
  :rule-classes :congruence
  :enable prevs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled equal-of-nexts-and-0-becomes-endp
  (equal (equal (nexts cursor) 0)
         (endp cursor))
  :enable (nexts
           endp
           equal-of-cardinality-and-0-becomes-emptyp))

(defrule nexts-when-endp-forward-chaining
  (implies (endp cursor)
           (equal (nexts cursor) 0))
  :rule-classes :forward-chaining
  :enable equal-of-nexts-and-0-becomes-endp)

(defrule endp-when-equal-nexts-and-0-forward-chaining
  (implies (equal (nexts cursor) 0)
           (endp cursor))
  :rule-classes :forward-chaining
  :enable equal-of-nexts-and-0-becomes-endp)

(defrule nexts-when-not-endp-type-prescription
  (implies (not (endp cursor))
           (and (integerp (nexts cursor))
                (< 0 (nexts cursor))))
  :rule-classes :type-prescription
  :enable equal-of-nexts-and-0-becomes-endp)

(defruled nexts-when-not-endp-linear
  (implies (not (endp cursor))
           (< 0 (nexts cursor)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;

(defruled equal-of-prevs-and-0-becomes-beginp
  (equal (equal (prevs cursor) 0)
         (beginp cursor))
  :enable (prevs
           beginp
           equal-of-cardinality-and-0-becomes-emptyp))

(defrule prevs-when-beginp-forward-chaining
  (implies (beginp cursor)
           (equal (prevs cursor) 0))
  :rule-classes :forward-chaining
  :enable equal-of-prevs-and-0-becomes-beginp)

(defrule beginp-when-equal-prevs-and-0-forward-chaining
  (implies (equal (prevs cursor) 0)
           (beginp cursor))
  :rule-classes :forward-chaining
  :enable equal-of-prevs-and-0-becomes-beginp)

(defrule prevs-when-not-beginp-type-prescription
  (implies (not (beginp cursor))
           (and (integerp (prevs cursor))
                (< 0 (prevs cursor))))
  :rule-classes :type-prescription
  :enable equal-of-prevs-and-0-becomes-beginp)

(defruled prevs-when-not-beginp-linear
  (implies (not (beginp cursor))
           (< 0 (prevs cursor)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;

(defrule nexts-of-next
  (implies (not (endp cursor))
           (equal (nexts (next cursor))
                  (- (nexts cursor) 1)))
  :cases ((entryp cursor))
  :enable (nexts
           next
           endp))

(defrule prevs-of-prev
  (implies (not (beginp cursor))
           (equal (prevs (prev cursor))
                  (- (prevs cursor) 1)))
  :cases ((entryp cursor))
  :enable (prevs
           prev
           beginp))

(defrule nexts-of-next-linear
  (implies (not (endp cursor))
           (< (nexts (next cursor))
              (nexts cursor)))
  :rule-classes :linear)

(defrule prevs-of-prev-linear
  (implies (not (beginp cursor))
           (< (prevs (prev cursor))
              (prevs cursor)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;

(defrule nexts-of-begin
  (equal (nexts (begin set))
         (cardinality set))
  :enable nexts)

(defrule nexts-of-end
  (equal (nexts (end set))
         0)
  :enable nexts)

(defrule nexts-of-seek-min
  (equal (nexts (seek-min set))
         (cardinality set))
  :cases ((emptyp set))
  :enable nexts)

(defruled nexts-of-seek-max
  (equal (nexts (seek-max set))
         (if (emptyp set) 0 1))
  :enable nexts)

(defrule nexts-of-seek-max-linear
  (<= (nexts (seek-max set)) 1)
  :rule-classes :linear
  :enable nexts-of-seek-max)

;;;;;;;;;;;;;;;;;;;;

(defrule prevs-of-end
  (equal (prevs (end set))
         (cardinality set))
  :enable prevs)

(defrule prevs-of-begin
  (equal (prevs (begin set))
         0)
  :enable prevs)

(defrule prevs-of-seek-max
  (equal (prevs (seek-max set))
         (cardinality set))
  :cases ((emptyp set))
  :enable prevs)

(defruled prevs-of-seek-min
  (equal (prevs (seek-min set))
         (if (emptyp set) 0 1))
  :enable prevs)

(defrule prevs-of-seek-min-linear
  (<= (prevs (seek-min set)) 1)
  :rule-classes :linear
  :enable prevs-of-seek-min)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy nexts-prevs-extra-rules
  '(nexts-when-not-endp-linear
    prevs-when-not-beginp-linear
    nexts-of-seek-max
    prevs-of-seek-min))
