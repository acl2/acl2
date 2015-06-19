; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(in-package "SET")
(include-book "fast")
(include-book "std/osets/cardinality" :dir :system)
(include-book "std/osets/union" :dir :system)
(include-book "std/osets/intersect" :dir :system)
(include-book "std/osets/delete" :dir :system)
(set-verify-guards-eagerness 2)

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defun double-delete-induction (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (if (or (empty X) (empty Y))
      (list X Y)
    (double-delete-induction (delete (head X) X)
                             (delete (head X) Y))))

(defthmd subset-double-delete
  (implies (subset X Y)
           (subset (delete a X) (delete a Y))))

(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y)) (cardinality X))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y)) (cardinality Y))
  :rule-classes (:rewrite :linear))

(defthm expand-cardinality-of-union
  (equal (cardinality (union X Y))
         (- (+ (cardinality X) (cardinality Y))
            (cardinality (intersect X Y)))))

(defthm expand-cardinality-of-difference
  (equal (cardinality (difference X Y))
         (- (cardinality X)
            (cardinality (intersect X Y)))))

(defthm intersect-cardinality-subset
  (implies (subset X Y)
           (equal (cardinality (intersect X Y))
                  (cardinality X)))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-non-subset
  (implies (not (subset x y))
           (< (cardinality (intersect x y))
              (cardinality x)))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-subset-2
  (equal (equal (cardinality (intersect X Y)) (cardinality X))
         (subset X Y)))

(defthm intersect-cardinality-non-subset-2
  (equal (< (cardinality (intersect x y)) (cardinality x))
         (not (subset x y))))
