; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "../set-defs")
(include-book "../in-defs")
(include-book "../min-max-defs")
(include-book "../generic-typed-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "before-after-defs")
(include-book "from-cursor-defs")
(include-book "begin-end-defs")
(include-book "seek-min-max-defs")
(include-book "next-prev-defs")
(include-book "nexts-prevs-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../generic-typed"))
(local (include-book "entry"))
(local (include-book "from-cursor"))
(local (include-book "begin-end"))
(local (include-book "seek-min-max"))
(local (include-book "next-prev"))
(local (include-book "nexts-prevs"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursor-all-genericp ((cursor cursorp))
  :type-prescription :none
  :returns (yes/no booleanp :rule-classes :type-prescription)
  :guard (or (entryp cursor)
             (endp cursor))
  (or (not (entryp cursor))
      (and (genericp (entry cursor))
           (cursor-all-genericp (next cursor))))
  :measure (nexts cursor))

;;;;;;;;;;;;;;;;;;;;

(defrule cursor-all-genericp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (cursor-all-genericp cursor0)
                  (cursor-all-genericp cursor1)))
  :rule-classes :congruence
  :expand ((cursor-all-genericp cursor0)
           (cursor-all-genericp cursor1)))

(defruled cursor-all-genericp-when-not-entryp
  (implies (not (entryp cursor))
           (cursor-all-genericp cursor))
  :enable cursor-all-genericp)

(defrule cursor-all-genericp-when-not-entryp-cheap
  (implies (not (entryp cursor))
           (cursor-all-genericp cursor))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by cursor-all-genericp-when-not-entryp)

;;;;;;;;;;;;;;;;;;;;

(defrule genericp-of-entry-when-set-all-genericp
  (implies (and (set-all-genericp (from-cursor cursor))
                (entryp cursor))
           (genericp (entry cursor))))

(defruled cursor-all-genericp-becomes-set-all-genericp-of-after
  (equal (cursor-all-genericp cursor)
         (or (not (entryp cursor))
             (and (genericp (entry cursor))
                  (set-all-genericp (after cursor)))))
  :induct (cursor-all-genericp cursor)
  :enable (cursor-all-genericp
           set-all-genericp))

(defruled cursor-all-genericp-when-set-all-genericp
  (implies (set-all-genericp (from-cursor cursor))
           (cursor-all-genericp cursor))
  :enable (cursor-all-genericp-becomes-set-all-genericp-of-after
           set-all-genericp-when-set-all-genericp-and-subset))

(defrule cursor-all-genericp-of-seek-min
  (equal (cursor-all-genericp (seek-min set))
         (set-all-genericp set))
  :enable (cursor-all-genericp-becomes-set-all-genericp-of-after
           set-all-genericp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy cursor-all-genericp-extra-rules
  '(cursor-all-genericp-when-not-entryp))
