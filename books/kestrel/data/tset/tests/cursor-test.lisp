; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "../set-defs")
(include-book "../cardinality-defs")
(include-book "../in-defs")
(include-book "../subset-defs")
(include-book "../insert-defs")
(include-book "../delete-defs")
(include-book "../min-max-defs")
(include-book "../cursor/defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../set"))
(local (include-book "../cardinality"))
(local (include-book "../in"))
(local (include-book "../subset"))
(local (include-book "../insert"))
(local (include-book "../delete"))
(local (include-book "../min-max"))
(local (include-book "../cursor/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk in the recommended style: it tests for an entry, and its guard says
;; that any hole it is at is the end, which a walk from @(tsee seek-min) with
;; @(tsee next) maintains.

(define cursor-any-evenp ((cursor cursorp))
  :guard (or (entryp cursor)
             (endp cursor))
  (and (entryp cursor)
       (or (evenp (nfix (entry cursor)))
           (cursor-any-evenp (next cursor))))
  :measure (nexts cursor))

(defrule cursor-any-evenp-when-cursor-equiv-congruence
  (implies (cursor-equiv cursor0 cursor1)
           (equal (cursor-any-evenp cursor0)
                  (cursor-any-evenp cursor1)))
  :rule-classes :congruence
  :induct (cursor-any-evenp cursor0)
  :enable cursor-any-evenp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define any-evenp ((set setp))
  (mbe :logic (and (not (emptyp set))
                   (or (evenp (nfix (min set)))
                       (any-evenp (delete (min set) set))))
       :exec (cursor-any-evenp (seek-min set)))
  :measure (cardinality set)
  :verify-guards nil ;; Verified below
  ///

  (defrule cursor-any-evenp-becomes-any-evenp
    (equal (cursor-any-evenp cursor)
           (and (entryp cursor)
                (or (evenp (nfix (entry cursor)))
                    (any-evenp (after cursor)))))
    :induct (cursor-any-evenp cursor)
    :enable (cursor-any-evenp
             any-evenp))

  (verify-guards any-evenp))

(defrule any-evenp-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (any-evenp set0)
                  (any-evenp set1)))
  :rule-classes :congruence
  :induct (any-evenp set0)
  :enable any-evenp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk over the elements at or above a value. It starts from the seek of
;; the value, stepping forward once if that is at a hole.

(define cursor-count ((cursor cursorp))
  :guard (or (entryp cursor)
             (endp cursor))
  :returns (count natp :rule-classes :type-prescription)
  (if (entryp cursor)
      (+ 1 (cursor-count (next cursor)))
    0)
  :measure (nexts cursor)
  :verify-guards :after-returns)

(define count-from
  (x
   (set setp))
  :returns (count natp :rule-classes :type-prescription)
  (let ((cursor (seek x set)))
    (cursor-count (if (entryp cursor)
                      cursor
                    (step-forward cursor)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adding a value where a search for it ends.

(define insert-by-cursor
  (x
   (set setp))
  :returns (set$ setp)
  (let ((cursor (seek x set)))
    (from-cursor (if (entryp cursor)
                     cursor
                   (insert-hole x cursor)))))

(defrule insert-by-cursor-becomes-insert
  (equal (insert-by-cursor x set)
         (insert x set))
  :enable insert-by-cursor)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk which removes elements as it passes: drop the even ones. After a
;; removal the cursor is at a hole, so the walk moves on with a single step.

(define cursor-drop-evens ((cursor cursorp))
  :guard (or (entryp cursor)
             (endp cursor))
  :returns (set setp)
  (cond ((not (entryp cursor))
         (from-cursor cursor))
        ((evenp (nfix (entry cursor)))
         (cursor-drop-evens (step-forward (delete-entry cursor))))
        (t (cursor-drop-evens (next cursor))))
  :measure (nexts cursor))

(defrule subset-of-cursor-drop-evens
  (subset (cursor-drop-evens cursor)
          (from-cursor cursor))
  :induct t
  :enable cursor-drop-evens)
