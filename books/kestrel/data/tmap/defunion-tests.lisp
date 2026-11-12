; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(include-book "kestrel/data/tset/in" :dir :system)
(include-book "kestrel/data/tset/min-max" :dir :system)
(include-book "kestrel/data/tset/cardinality" :dir :system)
(include-book "kestrel/data/tset/delete" :dir :system)

(include-book "kestrel/data/tmap/lookup" :dir :system)
(include-book "kestrel/data/tmap/update" :dir :system)
(include-book "kestrel/data/tmap/update-star" :dir :system)
(include-book "kestrel/data/tmap/defunion" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *m1*
  (tmap::update 1 3 (tmap::update 2 4 (tmap::empty))))

(defconst *m2*
  (tmap::update 2 5 (tmap::update 6 7 (tmap::empty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keeping the first map's value is the left-biased union, update*. A treap
;; is determined by its entries, so the two agree exactly.

(tmap::defunion union-left
  :combine (lambda (key x y)
             (declare (ignore key y))
             x))

(assert! (equal (union-left *m1* *m2*)
                (tmap::update* *m1* *m2*)))

(assert! (equal (union-left *m2* *m1*)
                (tmap::update* *m2* *m1*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Summing positive values, so that the union of maps with positive values
;; has positive values.

(define set-all-posp ((set tset::setp))
  :type-prescription :none
  (or (tset::emptyp set)
      (and (posp (tset::min set))
           (set-all-posp (tset::delete (tset::min set) set))))
  :measure (tset::cardinality set)
  :hints (("Goal" :in-theory (enable tset::cardinality-of-delete-when-in
                                     tset::in-of-min))))

(tmap::defunion union-plus
  :combine (lambda (key x y)
             (declare (ignore key))
             (+ (nfix x) (nfix y)))
  :val-pred posp
  :val-set-pred set-all-posp
  :combine-hints (("Goal" :in-theory (enable nfix))))

(assert! (equal (tmap::lookup 2 (union-plus *m1* *m2*)) 9))

(assert! (equal (tmap::lookup 6 (union-plus *m1* *m2*)) 7))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A combination given as a function symbol.

(define max-combine (key x y)
  :type-prescription :none
  (declare (ignore key))
  (max (nfix x) (nfix y)))

(tmap::defunion union-max
  :combine max-combine)

(assert! (equal (tmap::lookup 2 (union-max *m1* *m2*)) 5))

(assert! (equal (tmap::lookup 1 (union-max *m1* *m2*)) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (tmap::defunion union-bad
    :combine (lambda (x y) x))
  :expected :hard)
