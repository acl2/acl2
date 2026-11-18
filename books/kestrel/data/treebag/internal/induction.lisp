; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "std/util/define" :dir :system)

(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/min-max-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "../bag-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))

(local (include-book "kestrel/data/treemap/map" :dir :system))
(local (include-book "kestrel/data/treemap/keys" :dir :system))
(local (include-book "kestrel/data/treemap/min-max" :dir :system))
(local (include-book "kestrel/data/treemap/delete" :dir :system))

(local (include-book "../bag"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inductions over bags which recur through the representation: each step
;; removes every occurrence of an element by deleting its key from the bag's
;; map. Recurring on the fixed bag keeps every inductive hypothesis about a
;; bag.

;; Remove the smallest element.
(define min-delete-induction ((bag bagp))
  (or (emptyp bag)
      (min-delete-induction
        (treemap::delete (treemap::min-key (fix bag)) (fix bag))))
  :measure (treeset::cardinality (treemap::keys (fix bag)))
  :hints (("Goal" :in-theory (enable* emptyp
                                      break-abstraction)))
  :verify-guards nil)

(in-theory (enable (:i min-delete-induction)))

;; Remove the smallest element of the first bag from both bags.
(define min-delete-both-induction ((a bagp)
                                   (b bagp))
  (if (emptyp a)
      (list a b)
    (let ((x (treemap::min-key (fix a))))
      (min-delete-both-induction (treemap::delete x (fix a))
                                 (treemap::delete x (fix b)))))
  :measure (treeset::cardinality (treemap::keys (fix a)))
  :hints (("Goal" :in-theory (enable* emptyp
                                      break-abstraction)))
  :verify-guards nil)

(in-theory (enable (:i min-delete-both-induction)))
