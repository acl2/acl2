; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)

(include-book "../map-defs")
(include-book "../size-defs")
(include-book "../keys-defs")
(include-book "../lookup-defs")
(include-book "../delete-defs")
(include-book "../min-max-defs")
(include-book "../iter-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../map"))
(local (include-book "../size"))
(local (include-book "../keys"))
(local (include-book "../lookup"))
(local (include-book "../delete"))
(local (include-book "../min-max"))
(local (include-book "../iter"))

(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Deleting a key which is there makes the map smaller. TREEMAP has no size
;; law for delete, so read it off the key set, where TREESET has one.

(defrulel in-of-keys-of-min-key-when-not-emptyp
  (implies (not (emptyp map))
           (treeset::in (min-key map) (keys map)))
  :enable (min-key$inline
           treeset::in-of-min
           emptyp-of-keys))

(defrulel size-of-delete-when-in-of-keys
  (implies (treeset::in key (keys map))
           (< (size (delete key map))
              (size map)))
  :rule-classes :linear
  :enable (size$inline
           treeset::cardinality-of-delete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-any-evenp ((iter iterp))
  (and (has-valuep iter)
       (or (evenp (nfix (entry-val iter)))
           (iter-any-evenp (next iter))))
  :measure (nexts iter))

(defrule iter-any-evenp-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (iter-any-evenp iter0)
                  (iter-any-evenp iter1)))
  :rule-classes :congruence
  :induct (iter-any-evenp iter0)
  :enable iter-any-evenp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define any-evenp ((map mapp))
  (mbe :logic (and (not (emptyp map))
                   (or (evenp (nfix (min-val map)))
                       (any-evenp (delete (min-key map) map))))
       :exec (iter-any-evenp (iter-min map)))
  :measure (size map)
  ;; Keep `size' and `min-key' folded, so the linear rule above fires on the
  ;; measure conjecture rather than the goal dropping to the key set.
  :hints (("Goal" :in-theory (disable size$inline min-key$inline)
                  :use (:instance size-of-delete-when-in-of-keys
                                  (key (min-key map)))))
  :verify-guards nil ;; Verified below
  ///

  (defrule iter-any-evenp-becomes-any-evenp
    (equal (iter-any-evenp iter)
           (and (has-valuep iter)
                (or (evenp (nfix (entry-val iter)))
                    (any-evenp (after iter)))))
    :induct t
    :enable (iter-any-evenp
             any-evenp))

  (verify-guards any-evenp))

(defrule any-evenp-when-equiv-congruence
  (implies (equiv map0 map1)
           (equal (any-evenp map0)
                  (any-evenp map1)))
  :rule-classes :congruence
  :induct (any-evenp map0)
  :enable any-evenp)
