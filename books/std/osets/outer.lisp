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


#|| 
Q. Why do we need SUBSET enabled?

I think I understand what's going on here.  For a reproducible example, you can
just open up std/osets/outer.lisp and try to prove the first theorem with
subset disabled.  This leads to the goal below, which is perfectly fine, just
before the pick-a-point strategy kicks in:

   Subgoal 2.2
   (IMPLIES (IN A Y)
            (SUBSET (UNION Y (DELETE A X))
                    (UNION X Y))).

But after the hint applies, it produces a really weird goal, which ultimately
fails to prove and seems to be the real culprit:

   Subgoal 2.2.1
   (EQUAL (SUBSET SET-FOR-ALL-REDUCTION (UNION X Y))
          (COND ((EMPTY SET-FOR-ALL-REDUCTION) T)
                ((IN (HEAD SET-FOR-ALL-REDUCTION)
                     (UNION X Y))
                 (SUBSET (TAIL SET-FOR-ALL-REDUCTION)
                         (UNION X Y)))
                (T NIL))).

I don't like this goal at all.  It appears to be due to needing to prove that
(SUBSET X Y) is equivalent to (ALL X) when (PREDICATE A) == (IN A Y).  The goal
above basically corresponds to the recursive definition of ALL:

  (defun all (set-for-all-reduction)
    (declare (xargs :guard (setp set-for-all-reduction)))
    (if (empty set-for-all-reduction)
        t
      (and (predicate (head set-for-all-reduction))
           (all (tail set-for-all-reduction)))))

After tinkering around with several solutions, I think I found one that will
work well.  I'm doing a full regression with it now.  I'm not planning to
disable subset by default (which would be a bigger change), but with this rule
in place it does seem like the pick-a-point proofs in the osets library are
going through OK even with subset disabled, so I'm optimistic that the new
rule will work:

  (defthm pick-a-point-subset-constraint-helper
    ;; When we do a pick-a-point proof of subset, we need to show that (SUBSET X
    ;; Y) is just the same as (ALL X) with (PREDICATE A) = (IN A Y).  Since ALL
    ;; is defined recursively, the proof goals we get end up mentioning
    ;; HEAD/TAIL.  This doesn't always work well if the user's theory doesn't
    ;; have the right rules enabled.  This rule is intended to open up SUBSET in
    ;; only this very special case to solve such goals.
    (implies (syntaxp (equal set-for-all-reduction 'set-for-all-reduction))
             (equal (subset set-for-all-reduction rhs)
                    (cond ((empty set-for-all-reduction) t)
                          ((in (head set-for-all-reduction) rhs)
                           (subset (tail set-for-all-reduction) rhs))
                          (t nil)))))

Once the regressions pass I'll push it...

Cheers,
Jared
||#

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
  :rule-classes (:rewrite :linear)
  :hints(("Goal" :in-theory (enable subset))))

(defthmd intersect-cardinality-subset-2
  (equal (equal (cardinality (intersect X Y))
                (cardinality X))
         (subset X Y)))

(defthmd intersect-cardinality-non-subset-2
  (equal (< (cardinality (intersect x y))
            (cardinality x))
         (not (subset x y))))
