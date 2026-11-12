; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/util/define" :dir :system)

(include-book "../set-defs")
(include-book "../cardinality-defs")
(include-book "../delete-defs")
(include-book "../min-max-defs")
(include-book "../cursor/defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../set"))
(local (include-book "../cardinality"))
(local (include-book "../delete"))
(local (include-book "../min-max"))
(local (include-book "../cursor/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk in the recommended style: it tests for the end hole, and its guard
;; says that any hole it is at is the end, which a walk from @(tsee seek-min)
;; with @(tsee next) maintains.

(define cursor-any-evenp ((cursor cursorp))
  :guard (or (entryp cursor)
             (endp cursor))
  (and (not (endp cursor))
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
    (implies (or (entryp cursor)
                 (endp cursor))
             (equal (cursor-any-evenp cursor)
                    (and (entryp cursor)
                         (or (evenp (nfix (entry cursor)))
                             (any-evenp (after cursor))))))
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
