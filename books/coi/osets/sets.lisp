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
(set-verify-guards-eagerness 2)
(include-book "std/osets/top" :dir :system)


(local (include-book "outer"))
(local (include-book "sort"))
(local (include-book "primitives"))
(local (include-book "membership"))
(local (include-book "fast"))
(set-enforce-redundancy t)


(defmacro emptyset ()
  nil)

(defun list-to-set (list)
  (cond
   ((consp list)
    (insert (car list) (list-to-set (cdr list))))
   (t
    nil)))

(defund split-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) (mv nil nil))
        ((endp (cdr x)) (mv (list (car x)) nil))
        (t (mv-let (part1 part2)
                   (split-list (cddr x))
                   (mv (cons (car x) part1)
                       (cons (cadr x) part2))))))

(defun in-list (a x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (or (equal a (car x))
	(in-list a (cdr x)))))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

(defthm head-insert-empty
  (implies (empty X)
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
           (empty (tail (insert a X)))))


(defthm intersect-cardinality-subset
  (implies (subset X Y)
           (equal (cardinality (intersect X Y))
                  (cardinality X)))
  :rule-classes (:rewrite :linear))

(defthm in-list-cons
  (equal (in-list a (cons b x))
	 (or (equal a b)
	     (in-list a x))))

(defthm in-list-append
  (equal (in-list a (append x y))
	 (or (in-list a x)
	     (in-list a y))))

(defthm in-list-revappend
  (equal (in-list a (revappend x y))
	 (or (in-list a x)
	     (in-list a y))))

(defthm in-list-reverse
  (equal (in-list a (reverse x))
	 (in-list a x)))

(defthm in-list-on-set
  (implies (setp X)
	   (equal (in-list a X)
		  (in a X))))

;; conflicts with std/osets/top where we use member instead

;; (defthm in-mergesort
;;   (equal (in a (mergesort x))
;; 	 (in-list a x)))


(set-enforce-redundancy nil)

(in-theory (disable double-containment))

(defthm double-containment-expensive
  ;; COI's version didn't have a backchain limit like std/osets/top.  The
  ;; backchain limit causes some lemmas to fail in multicons, so try to
  ;; make this as compatible as possible.
  (implies (and (setp x)
                (setp y))
           (equal (equal x y)
                  (and (subset x y)
                       (subset y x))))
  :hints(("Goal" :use ((:instance double-containment)))))

(theory-invariant
 (not (and (acl2::active-runep '(:rewrite double-containment))
           (acl2::active-runep '(:rewrite double-containment-expensive)))))


;; these were all enabled in coi/osets
(in-theory (enable in subset delete union intersect difference cardinality in-list
                   mergesort all weak-insert-induction
                   ;; things that sol put into expensive-rules
                   pick-a-point-subset-strategy
                   subset-transitive
                   subset-in
                   subset-in-2
                   union-symmetric
                   union-commutative
                   union-delete-x
                   union-delete-y
                   intersect-over-union
                   difference-over-union
                   difference-over-intersect
                   difference-insert-x
                   difference-delete-y
                   insert-cardinality
                   delete-cardinality
                   ))

