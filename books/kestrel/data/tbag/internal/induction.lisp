; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TBAG")

(include-book "std/util/define" :dir :system)

(include-book "kestrel/data/tset/cardinality-defs" :dir :system)
(include-book "kestrel/data/tmap/keys-defs" :dir :system)
(include-book "kestrel/data/tmap/min-max-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)

(include-book "../bag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/tset/in" :dir :system))
(local (include-book "kestrel/data/tset/min-max" :dir :system))
(local (include-book "kestrel/data/tset/cardinality" :dir :system))
(local (include-book "kestrel/data/tset/delete" :dir :system))

(local (include-book "kestrel/data/tmap/map" :dir :system))
(local (include-book "kestrel/data/tmap/keys" :dir :system))
(local (include-book "kestrel/data/tmap/min-max" :dir :system))
(local (include-book "kestrel/data/tmap/delete" :dir :system))

(local (include-book "../bag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inductions over bags which recur through the representation: each step
;; removes every occurrence of an element by deleting its key from the bag's
;; map. Recurring on the fixed bag keeps every inductive hypothesis about a
;; bag.

;; Remove the smallest element.
(define min-delete-induction ((bag bagp))
  :type-prescription :none
  (or (emptyp bag)
      (min-delete-induction
        (tmap::delete (tmap::min-key (fix bag)) (fix bag))))
  :measure (tset::cardinality (tmap::keys (fix bag)))
  :hints (("Goal" :in-theory (enable* emptyp
                                      break-abstraction)))
  :verify-guards nil)

(in-theory (enable (:i min-delete-induction)))

;; Remove the smallest element of the first bag from both bags.
(define min-delete-both-induction ((a bagp)
                                   (b bagp))
  :type-prescription :none
  (if (emptyp a)
      (list a b)
    (let ((x (tmap::min-key (fix a))))
      (min-delete-both-induction (tmap::delete x (fix a))
                                 (tmap::delete x (fix b)))))
  :measure (tset::cardinality (tmap::keys (fix a)))
  :hints (("Goal" :in-theory (enable* emptyp
                                      break-abstraction)))
  :verify-guards nil)

(in-theory (enable (:i min-delete-both-induction)))
