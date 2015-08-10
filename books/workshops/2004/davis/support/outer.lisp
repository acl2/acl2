; Fully Ordered Finite Sets, Version 0.9
; Copyright (C) 2003, 2004 Kookamara LLC
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
;
; outer.lisp
;
; This file is the outermost layer of the set theory library.  We have already
; built up a framework for doing pick-a-point and double containment proofs in
; membership.lisp, but we have not even introduced a number of set functions --
; deletion, union, intersect, difference, and so forth.
;
; Here, we introduce these functions and prove many important facts about them.
; Taking a quick look through here, it should be obvious that our automatic
; strategies are doing a very good job at keeping saving us from having to
; provide hints.

(in-package "SET")
(include-book "fast")
(set-verify-guards-eagerness 2)



; -------------------------------------------------------------------
; Delete

(defun delete (a X)
  (declare (xargs :guard (setp X)
                  :verify-guards nil))
  (cond ((empty X) nil)
        ((equal a (head X)) (tail X))
        (t (insert (head X) (delete a (tail X))))))

(defthm delete-set
  (setp (delete a X)))

(verify-guards delete)

(defthm delete-preserves-empty
  (implies (empty X)
           (empty (delete a X))))

(defthm delete-in
  (equal (in a (delete b X))
         (and (in a X)
              (not (equal a b)))))

(defthm delete-sfix-cancel
  (equal (delete a (sfix X))
	 (delete a X)))

(defthm delete-nonmember-cancel
  (implies (not (in a X))
           (equal (delete a X) (sfix X))))

(defthm delete-delete
  (equal (delete a (delete b X))
         (delete b (delete a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm repeated-delete
  (equal (delete a (delete a X))
         (delete a X)))

(defthm delete-insert-cancel
  (equal (delete a (insert a X))
         (delete a X)))

(defthm insert-delete-cancel
  (equal (insert a (delete a X))
         (insert a X)))

(defthm subset-delete
  (subset (delete a X) X))


; -------------------------------------------------------------------
; Union

(defun union (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  (sfix Y)
                (insert (head X) (union (tail X) Y)))
       :exec  (fast-union X Y)))

(defthm union-set
  (setp (union X Y)))

(defthm union-sfix-cancel-X
  (equal (union (sfix X) Y) (union X Y)))

(defthm union-sfix-cancel-Y
  (equal (union X (sfix Y)) (union X Y)))

(defthm union-empty-X
  (implies (empty X)
           (equal (union X Y) (sfix Y))))

(defthm union-empty-Y
  (implies (empty Y)
           (equal (union X Y) (sfix X))))

(defthm union-empty
  (equal (empty (union X Y))
	 (and (empty X) (empty Y))))

(defthm union-in
  (equal (in a (union X Y))
         (or (in a X) (in a Y))))

(verify-guards union
  :hints(("Goal" :in-theory (enable fast-union-theory))))


(defthm union-symmetric
  (equal (union X Y) (union Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-subset-X
  (subset X (union X Y)))

(defthm union-subset-Y
  (subset Y (union X Y)))

(defthm union-insert-X
  (equal (union (insert a X) Y)
         (insert a (union X Y))))

(defthm union-insert-Y
  (equal (union X (insert a Y))
         (insert a (union X Y))))

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

(defthm union-self
  (equal (union X X) (sfix X)))

(defthm union-associative
  (equal (union (union X Y) Z)
         (union X (union Y Z))))

(defthm union-commutative
  (equal (union X (union Y Z))
         (union Y (union X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-outer-cancel
  (equal (union X (union X Z))
         (union X Z)))



; -------------------------------------------------------------------
; Intersect

(defun intersect (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y)
                     (insert (head X) (intersect (tail X) Y)))
                    (t (intersect (tail X) Y)))
       :exec (fast-intersect X Y)))

(defthm intersect-set
  (setp (intersect X Y)))

(defthm intersect-sfix-cancel-X
  (equal (intersect (sfix X) Y) (intersect X Y)))

(defthm intersect-sfix-cancel-Y
  (equal (intersect X (sfix Y)) (intersect X Y)))

(defthm intersect-empty-X
  (implies (empty X) (empty (intersect X Y))))

(defthm intersect-empty-Y
  (implies (empty Y) (empty (intersect X Y))))

(encapsulate ()

  (local (defthm intersect-in-Y
    (implies (not (in a Y))
             (not (in a (intersect X Y))))))

  (local (defthm intersect-in-X
    (implies (not (in a X))
             (not (in a (intersect X Y))))))

  (defthm intersect-in
    (equal (in a (intersect X Y))
           (and (in a Y) (in a X))))
)

(verify-guards intersect
  :hints(("Goal" :in-theory (enable fast-intersect-theory))))


(defthm intersect-symmetric
  (equal (intersect X Y) (intersect Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm intersect-subset-X
  (subset (intersect X Y) X))

(defthm intersect-subset-Y
  (subset (intersect X Y) Y))

(defthm intersect-insert-X
  (implies (not (in a Y))
           (equal (intersect (insert a X) Y)
                  (intersect X Y))))

(defthm intersect-insert-Y
  (implies (not (in a X))
           (equal (intersect X (insert a Y))
                  (intersect X Y))))

(defthm intersect-delete-X
  (equal (intersect (delete a X) Y)
         (delete a (intersect X Y))))

(defthm intersect-delete-Y
  (equal (intersect X (delete a Y))
         (delete a (intersect X Y))))

(defthm intersect-self
  (equal (intersect X X) (sfix X)))

(defthm intersect-associative
  (equal (intersect (intersect X Y) Z)
         (intersect X (intersect Y Z))))

(defthm union-over-intersect
  (equal (union X (intersect Y Z))
         (intersect (union X Y) (union X Z))))

(defthm intersect-over-union
  (equal (intersect X (union Y Z))
         (union (intersect X Y) (intersect X Z))))

(defthm intersect-commutative
  (equal (intersect X (intersect Y Z))
         (intersect Y (intersect X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm intersect-outer-cancel
  (equal (intersect X (intersect X Z))
         (intersect X Z)))


; -------------------------------------------------------------------
; Difference

(defun difference (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y) (difference (tail X) Y))
                    (t (insert (head X) (difference (tail X) Y))))
       :exec (fast-difference X Y)))

(defthm difference-set
  (setp (difference X Y)))

(defthm difference-sfix-X
  (equal (difference (sfix X) Y) (difference X Y)))

(defthm difference-sfix-Y
  (equal (difference X (sfix Y)) (difference X Y)))

(defthm difference-empty-X
  (implies (empty X)
           (equal (difference X Y) (sfix X))))

(defthm difference-empty-Y
  (implies (empty Y)
           (equal (difference X Y) (sfix X))))

(encapsulate ()

  (local (defthm difference-in-X
    (implies (in a (difference X Y))
             (in a X))))

  (local (defthm difference-in-Y
    (implies (in a (difference X Y))
             (not (in a Y)))))

  (defthm difference-in
    (equal (in a (difference X Y))
           (and (in a X)
                (not (in a Y)))))
)

(verify-guards difference
  :hints(("Goal" :in-theory (enable fast-difference-theory))))

(defthm difference-subset-X
  (subset (difference X Y) X))

(defthm subset-difference
  (equal (empty (difference X Y))
         (subset X Y)))

(defthm difference-over-union
  (equal (difference X (union Y Z))
         (intersect (difference X Y) (difference X Z))))

(defthm difference-over-intersect
  (equal (difference X (intersect Y Z))
         (union (difference X Y) (difference X Z))))

(defthm difference-insert-X
  (equal (difference (insert a X) Y)
         (if (in a Y)
             (difference X Y)
           (insert a (difference X Y)))))

(defthm difference-insert-Y
  (equal (difference X (insert a Y))
         (delete a (difference X Y))))

(defthm difference-delete-X
  (equal (difference (delete a X) Y)
         (delete a (difference X Y))))

(defthm difference-delete-Y
  (equal (difference X (delete a Y))
         (if (in a X)
             (insert a (difference X Y))
           (difference X Y))))

(defthm difference-preserves-subset
  (implies (subset X Y)
	   (subset (difference X Z)
		   (difference Y Z))))


; -------------------------------------------------------------------
; Cardinality

(defun cardinality (X)
  (declare (xargs :guard (setp X)
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  0
                (1+ (cardinality (tail X))))
       :exec  (len X)))

(verify-guards cardinality
  ;; Normally we would never want to enable the primitives theory.
  ;; However, here we need to show that cardinality is equal to
  ;; len, and for this we need to be able to reason about tail and
  ;; empty.  Think of this as a tiny extension of "fast.lisp"
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cardinality-type
  (and (integerp (cardinality X))
       (<= 0 (cardinality X)))
  :rule-classes :type-prescription)

(defthm cardinality-zero-empty
  (equal (equal (cardinality x) 0)
	 (empty x)))

(defthm cardinality-sfix-cancel
  (equal (cardinality (sfix X)) (cardinality X)))

(encapsulate ()

  (local (defthm cardinality-insert-empty
    (implies (empty X)
             (equal (cardinality (insert a X)) 1))
    :hints(("Goal" :use (:instance cardinality (x (insert a X)))))))

  (defthm insert-cardinality
    (equal (cardinality (insert a X))
           (if (in a X)
               (cardinality X)
             (1+ (cardinality X)))))
)

(defthm delete-cardinality
  (equal (cardinality (delete a X))
         (if (in a X)
             (1- (cardinality X))
           (cardinality X))))

; Now that we have the delete function, we can prove an interesting
; theorem, namely that if (subset X Y) and |X| = |Y|, then X = Y.  In
; order to do this, we need to induct by deleting elements from both
; X and Y.  This is a little ugly, but along the way we will show the
; nice theorem, subset-cardinality.

(defun double-delete-induction (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (if (or (empty X) (empty Y))
      (list X Y)
    (double-delete-induction (delete (head X) X)
                             (delete (head X) Y))))

(defthmd subset-double-delete
  (implies (subset X Y)
           (subset (delete a X) (delete a Y))))

(encapsulate ()

  (local (defthm subset-cardinality-lemma
    (implies (and (not (or (empty x) (empty y)))
                  (implies (subset (delete (head x) x)
                                   (delete (head x) y))
                           (<= (cardinality (delete (head x) x))
                               (cardinality (delete (head x) y)))))
             (implies (subset x y)
                      (<= (cardinality x) (cardinality y))))
    :hints(("goal" :use ((:instance subset-double-delete
                                  (a (head x))
                                  (x x)
                                  (y y)))))))

  (defthm subset-cardinality
    (implies (subset X Y)
             (<= (cardinality X) (cardinality Y)))
    :hints(("Goal" :induct (double-delete-induction X Y)))
    :rule-classes (:rewrite :linear))

)

(defthmd equal-cardinality-subset-is-equality
  (implies (and (setp X)
		(setp Y)
                (subset X Y)
                (equal (cardinality X) (cardinality Y)))
           (equal (equal X Y) t))
  :hints(("Goal" :induct (double-delete-induction X Y))
         ("Subgoal *1/2"
          :use ((:instance subset-double-delete
                           (a (head X))
                           (X X)
                           (Y Y))
                (:instance (:theorem
                  (implies (equal X Y)
                           (equal (insert a X) (insert a Y))))
	             (a (head X))
                     (X (tail X))
                     (Y (delete (head X) Y)))))))

(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y)) (cardinality X))
  :rule-classes :linear)

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y)) (cardinality Y))
  :rule-classes :linear)



; There are also some interesting properties about cardinality which
; are more precise.

(defthm expand-cardinality-of-union
  (equal (cardinality (union X Y))
         (- (+ (cardinality X) (cardinality Y))
            (cardinality (intersect X Y))))
  :rule-classes :linear)

(defthm expand-cardinality-of-difference
  (equal (cardinality (difference X Y))
         (- (cardinality X)
            (cardinality (intersect X Y))))
  :rule-classes :linear)

(defthm intersect-cardinality-subset
  (implies (subset X Y)
           (equal (cardinality (intersect X Y))
                  (cardinality X)))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-non-subset
  (implies (not (subset x y))
           (< (cardinality (intersect x y))
              (cardinality x)))
  :rule-classes :linear)

(defthm intersect-cardinality-subset-2
  (equal (equal (cardinality (intersect X Y)) (cardinality X))
	 (subset X Y)))

(defthm intersect-cardinality-non-subset-2
  (equal (< (cardinality (intersect x y)) (cardinality x))
	 (not (subset x y))))
