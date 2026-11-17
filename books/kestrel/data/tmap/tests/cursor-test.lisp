; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/define" :dir :system)

(include-book "../map-defs")
(include-book "../size-defs")
(include-book "../keys-defs")
(include-book "../lookup-defs")
(include-book "../delete-defs")
(include-book "../min-max-defs")
(include-book "../cursor/defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../map"))
(local (include-book "../size"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../delete"))
(local (include-book "../min-max"))
(local (include-book "../cursor/top"))

(local (include-book "kestrel/data/tset/delete" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/in" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Deleting a key which is there makes the map smaller. TMAP has no size
;; law for delete, so read it off the key set, where TSET has one.

(defrulel in-of-keys-of-min-key-when-not-emptyp
  (implies (not (emptyp map))
           (tset::in (min-key map) (keys map)))
  :enable (min-key$inline
           tset::in-of-min
           emptyp-of-keys))

(defrulel size-of-delete-when-in-of-keys
  (implies (tset::in key (keys map))
           (< (size (delete key map))
              (size map)))
  :rule-classes :linear
  :enable (size$inline
           tset::cardinality-of-delete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A walk in the recommended style: it tests for an entry, and its guard says
;; that any hole it is at is the end, which a walk from @(tsee seek-min) with
;; @(tsee next) maintains.

(define cursor-any-evenp ((cursor cursorp))
  :guard (or (entryp cursor)
             (endp cursor))
  (and (entryp cursor)
       (or (evenp (nfix (entry-val cursor)))
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

(define any-evenp ((map mapp))
  (mbe :logic (and (not (emptyp map))
                   (or (evenp (nfix (min-val map)))
                       (any-evenp (delete (min-key map) map))))
       :exec (cursor-any-evenp (seek-min map)))
  :measure (size map)
  ;; Keep `size' and `min-key' folded, so the linear rule above fires on the
  ;; measure conjecture rather than the goal dropping to the key set.
  :hints (("Goal" :in-theory (disable size$inline min-key$inline)
                  :use (:instance size-of-delete-when-in-of-keys
                                  (key (min-key map)))))
  :verify-guards nil ;; Verified below
  ///

  (defrule cursor-any-evenp-becomes-any-evenp
    (equal (cursor-any-evenp cursor)
           (and (entryp cursor)
                (or (evenp (nfix (entry-val cursor)))
                    (any-evenp (after cursor)))))
    :induct t
    :enable (cursor-any-evenp
             any-evenp))

  (verify-guards any-evenp))

(defrule any-evenp-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (any-evenp map0)
                  (any-evenp map1)))
  :rule-classes :congruence
  :induct (any-evenp map0)
  :enable any-evenp)
