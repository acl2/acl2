; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public Lic-
; ense along with this program; if not, write to the Free Soft- ware
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.


; outer.lisp
;
; Theorems relating the more complicated set operations (union, intersect,
; etc.)  to one another.

(in-package "SET")
(include-book "delete")
(include-book "union")
(include-book "intersect")
(include-book "difference")
(include-book "cardinality")
(set-verify-guards-eagerness 2)


(defthm union-delete-X
    (equal (union (delete a X) Y)
           (if (in a Y)
               (union X Y)
             (delete a (union X Y)))))

(defthm union-delete-Y
    (equal (union X (delete a Y))
           (if (in a X)
               (union X Y)
             (delete a (union X Y)))))


(defthm intersect-delete-X
  (equal (intersect (delete a X) Y)
         (delete a (intersect X Y))))

(defthm intersect-delete-Y
  (equal (intersect X (delete a Y))
         (delete a (intersect X Y))))

(defthm union-over-intersect
  (equal (union X (intersect Y Z))
         (intersect (union X Y) (union X Z))))

(defthm intersect-over-union
  (equal (intersect X (union Y Z))
         (union (intersect X Y) (intersect X Z))))


(defthm difference-over-union
  (equal (difference X (union Y Z))
         (intersect (difference X Y) (difference X Z))))

(defthm difference-over-intersect
  (equal (difference X (intersect Y Z))
         (union (difference X Y) (difference X Z))))

(defthm difference-delete-X
  (equal (difference (delete a X) Y)
         (delete a (difference X Y))))

(defthm difference-delete-Y
  (equal (difference X (delete a Y))
         (if (in a X)
             (insert a (difference X Y))
           (difference X Y))))

(defthm difference-insert-Y
  (equal (difference X (insert a Y))
         (delete a (difference X Y))))


(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y))
      (cardinality X))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y))
      (cardinality Y))
  :rule-classes (:rewrite :linear))


; There are also some interesting properties about cardinality which are more
; precise.

(defthm expand-cardinality-of-union
  ;; This is pretty questionable -- it used to also be a :linear rule, but that was
  ;; really expensive.
  (equal (cardinality (union X Y))
         (- (+ (cardinality X) (cardinality Y))
            (cardinality (intersect X Y)))))

(defthm expand-cardinality-of-difference
  ;; Also questionable, also used to be :linear
  (equal (cardinality (difference X Y))
         (- (cardinality X)
            (cardinality (intersect X Y)))))

;; We used to have this rule, but it was silly -- (intersect X Y) can just rewrite to
;; (SFIX X) when X is a subset of Y.
;; (defthm intersect-cardinality-subset
;;     (implies (subset X Y)
;;              (equal (cardinality (intersect X Y))
;;                     (cardinality X))))

(defthmd intersect-cardinality-non-subset
  (implies (not (subset x y))
           (< (cardinality (intersect x y))
              (cardinality x)))
  :rule-classes (:rewrite :linear))

(defthmd intersect-cardinality-subset-2
  (equal (equal (cardinality (intersect X Y))
                (cardinality X))
         (subset X Y)))

(defthmd intersect-cardinality-non-subset-2
  (equal (< (cardinality (intersect x y))
            (cardinality x))
         (not (subset x y))))
