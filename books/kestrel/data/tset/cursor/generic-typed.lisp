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

(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../set"))
(local (include-book "../in"))
(local (include-book "../delete"))
(local (include-book "../generic-typed"))
(local (include-book "entry"))
(local (include-book "from-cursor"))
(local (include-book "begin-end"))
(local (include-book "seek-min-max"))
(local (include-book "next-prev"))
(local (include-book "nexts-prevs"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable acl2::equal-of-booleans-cheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cursor-all-genericp ((cursor cursorp))
  :type-prescription :none
  :guard (or (entryp cursor)
             (endp cursor))
  (or (endp cursor)
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

(defrule genericp-of-entry-when-set-all-genericp
  (implies (and (set-all-genericp (from-cursor cursor))
                (entryp cursor))
           (genericp (entry cursor)))
  :enable set-all-genericp-pick-a-point
  :use (:instance set-all-genericp-sk-necc
                  (elem (entry cursor))
                  (set (from-cursor cursor))))

(defruled cursor-all-genericp-when-set-all-genericp
  (implies (and (set-all-genericp (from-cursor cursor))
                (or (entryp cursor)
                    (endp cursor)))
           (cursor-all-genericp cursor))
  :induct (cursor-all-genericp cursor)
  :enable cursor-all-genericp)

(defrule cursor-all-genericp-when-endp
  (implies (endp cursor)
           (cursor-all-genericp cursor))
  :enable cursor-all-genericp)

(defruledl genericp-when-in-of-after
  (implies (and (in x (after cursor))
                (or (entryp cursor)
                    (endp cursor))
                (cursor-all-genericp cursor))
           (genericp x))
  :induct (cursor-all-genericp cursor)
  :expand ((cursor-all-genericp cursor)
           (cursor-all-genericp (next cursor)))
  :enable (cursor-all-genericp
           not-emptyp-when-in))

(defruledl genericp-of-min-when-cursor-all-genericp-of-seek-min
  (implies (and (cursor-all-genericp (seek-min set))
                (not (emptyp set)))
           (genericp (min set)))
  :expand ((cursor-all-genericp (seek-min set))))

(defruledl genericp-when-in-and-cursor-all-genericp-of-seek-min
  (implies (and (in x set)
                (cursor-all-genericp (seek-min set)))
           (genericp x))
  :use ((:instance in-of-from-cursor-becomes-in-of-before-or-entry-or-after
                   (cursor (seek-min set))))
  :enable (genericp-when-in-of-after
           genericp-of-min-when-cursor-all-genericp-of-seek-min
           not-emptyp-when-in)
  ;; after-of-seek-min would rewrite the `after' term away before
  ;; genericp-when-in-of-after, which is keyed on it, could fire.
  :disable (in-of-from-cursor-becomes-in-of-before-or-entry-or-after
            after-of-seek-min))

(defruled set-all-genericp-when-cursor-all-genericp-of-seek-min
  (implies (cursor-all-genericp (seek-min set))
           (set-all-genericp set))
  :enable (set-all-genericp-pick-a-point
           genericp-when-in-and-cursor-all-genericp-of-seek-min))

(defrule booleanp-of-cursor-all-genericp
  (booleanp (cursor-all-genericp cursor))
  :rule-classes (:rewrite :type-prescription)
  :induct (cursor-all-genericp cursor)
  :enable cursor-all-genericp)

(defrule cursor-all-genericp-of-seek-min
  (equal (cursor-all-genericp (seek-min set))
         (set-all-genericp set))
  :enable set-all-genericp-when-cursor-all-genericp-of-seek-min
  :use (:instance cursor-all-genericp-when-set-all-genericp
                  (cursor (seek-min set))))
