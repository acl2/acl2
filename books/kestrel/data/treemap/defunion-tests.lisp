; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(include-book "kestrel/data/treeset/in" :dir :system)
(include-book "kestrel/data/treeset/min-max" :dir :system)
(include-book "kestrel/data/treeset/cardinality" :dir :system)
(include-book "kestrel/data/treeset/delete" :dir :system)

(include-book "kestrel/data/treemap/lookup" :dir :system)
(include-book "kestrel/data/treemap/update" :dir :system)
(include-book "kestrel/data/treemap/update-star" :dir :system)
(include-book "kestrel/data/treemap/defunion" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *m1*
  (treemap::update 1 3 (treemap::update 2 4 (treemap::empty))))

(defconst *m2*
  (treemap::update 2 5 (treemap::update 6 7 (treemap::empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keeping the first map's value is the left-biased union, update*. A treap
;; is determined by its entries, so the two agree exactly.

(treemap::defunion union-left
  :combine (lambda (key x y)
             (declare (ignore key y))
             x))

(assert! (equal (union-left *m1* *m2*)
                (treemap::update* *m1* *m2*)))

(assert! (equal (union-left *m2* *m1*)
                (treemap::update* *m2* *m1*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Summing positive values, so that the union of maps with positive values
;; has positive values.

(define set-all-posp ((set treeset::setp))
  (or (treeset::emptyp set)
      (and (posp (treeset::min set))
           (set-all-posp (treeset::delete (treeset::min set) set))))
  :measure (treeset::cardinality set)
  :hints (("Goal" :in-theory (enable treeset::cardinality-of-delete-when-in
                                     treeset::in-of-min))))

(treemap::defunion union-plus
  :combine (lambda (key x y)
             (declare (ignore key))
             (+ (nfix x) (nfix y)))
  :val-pred posp
  :val-set-pred set-all-posp
  :combine-hints (("Goal" :in-theory (enable nfix))))

(assert! (equal (treemap::lookup 2 (union-plus *m1* *m2*)) 9))

(assert! (equal (treemap::lookup 6 (union-plus *m1* *m2*)) 7))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A combination given as a function symbol.

(define max-combine (key x y)
  (declare (ignore key))
  (max (nfix x) (nfix y)))

(treemap::defunion union-max
  :combine max-combine)

(assert! (equal (treemap::lookup 2 (union-max *m1* *m2*)) 5))

(assert! (equal (treemap::lookup 1 (union-max *m1* *m2*)) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (treemap::defunion union-bad
    :combine (lambda (x y) x))
  :expected :hard)
