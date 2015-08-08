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
;
; sets.lisp
;
; This is the top level file, which you should include to use the ordered set
; theory library.

(in-package "SET")
(set-verify-guards-eagerness 2)


; We need some program-mode definitions which are used in order to
; automate the pick-a-point strategies.

(include-book "computed-hints")


; The definitions in this file are redundant from the local include
; books.  This approach has several advantages.
;
;  - it gives a better event order than simply including the books
;    one by one
;
;  - this file is also faster to include than all of the local books
;    below, and allows the "ugliness" of auxilliary lemmas to be
;    hidden away
;
;  - it makes clear that these theorems are public, and entirely
;    prevents the use of "internal" lemmas and theorems.

(local (include-book "primitives"))
(local (include-book "membership"))
(local (include-book "fast"))
(local (include-book "outer"))
(local (include-book "sort"))


; We begin with the definitions of the set theory functions and a
; few trivial type prescriptions.

(defund << (a b)
  (declare (xargs :guard t))
  (and (lexorder a b)
       (not (equal a b))))

(defund setp (X)
  (declare (xargs :guard t))
  (if (atom X)
      (null X)
    (or (null (cdr X))
        (and (consp (cdr X))
             (<< (car X) (cadr X))
             (setp (cdr X))))))

(defthm setp-type
  (or (equal (setp X) t)
      (equal (setp X) nil))
  :rule-classes :type-prescription)

(defund empty (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (or (null X)
                  (not (setp X)))
       :exec  (null X)))

(defthm empty-type
  (or (equal (empty X) t)
      (equal (empty X) nil))
  :rule-classes :type-prescription)

(defund sfix (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X) nil X)
       :exec  X))

(defund head (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (car (sfix X))
       :exec  (car X)))

(defund tail (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (cdr (sfix X))
       :exec  (cdr X)))

(defund insert (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) (list a))
        ((equal (head X) a) X)
        ((<< a (head X)) (cons a X))
        (t (cons (head X) (insert a (tail X))))))

(defun in (a X)
  (declare (xargs :guard (setp X)))
  (and (not (empty X))
       (or (equal a (head X))
           (in a (tail X)))))

(defthm in-type
  (or (equal (in a X) t)
      (equal (in a X) nil))
  :rule-classes :type-prescription)

(defund fast-subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (cond ((empty X) t)
        ((empty Y) nil)
        ((<< (head X) (head Y)) nil)
        ((equal (head X) (head Y)) (fast-subset (tail X) (tail Y)))
        (t (fast-subset X (tail Y)))))

(defund subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (if (empty X)
		  t
		(and (in (head X) Y)
		     (subset (tail X) Y)))
       :exec (fast-subset X Y)))

(defthm subset-type
  (or (equal (subset X Y) t)
      (equal (subset X Y) nil))
  :rule-classes :type-prescription)

(defund fast-measure (X Y)
  (+ (acl2-count X) (acl2-count Y)))

(defund fast-union (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) Y)
        ((empty Y) X)
        ((equal (head X) (head Y))
         (cons (head X) (fast-union (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (cons (head X) (fast-union (tail X) Y)))
        (t (cons (head Y) (fast-union X (tail Y))))))

(defund fast-intersect (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) (sfix Y))
        ((equal (head X) (head Y))
         (cons (head X)
               (fast-intersect (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (fast-intersect (tail X) Y))
        (t (fast-intersect X (tail Y)))))

(defund fast-difference (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) X)
        ((equal (head X) (head Y))
         (fast-difference (tail X) (tail Y)))
        ((<< (head X) (head Y))
         (cons (head X) (fast-difference (tail X) Y)))
        (t (fast-difference X (tail Y)))))

(defun delete (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((equal a (head X)) (tail X))
        (t (insert (head X) (delete a (tail X))))))

(defun union (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (if (empty X)
                  (sfix Y)
                (insert (head X) (union (tail X) Y)))
       :exec  (fast-union X Y)))

(defun intersect (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y)
                     (insert (head X) (intersect (tail X) Y)))
                    (t (intersect (tail X) Y)))
       :exec (fast-intersect X Y)))

(defun difference (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y) (difference (tail X) Y))
                    (t (insert (head X) (difference (tail X) Y))))
       :exec (fast-difference X Y)))

(defun cardinality (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X)
                  0
                (1+ (cardinality (tail X))))
       :exec  (len X)))

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

(defun mergesort-exec (x)
  (declare (xargs :guard (true-listp x)
                  :measure (:? x)))
  (cond ((endp x) nil)
	((endp (cdr x)) (insert (car x) nil))
        (t (mv-let (part1 part2)
		   (split-list x)
		   (union (mergesort-exec part1) (mergesort-exec part2))))))

(defun mergesort (x)
  (declare (xargs :guard (true-listp x)))
  (mbe :logic (if (endp x)
		  nil
		(insert (car x)
			(mergesort (cdr x))))
       :exec (mergesort-exec x)))



; "High Powered" Strategies
;
;   We put these at the beginning of the file so that they are tried
;   as a last resort when simple methods have failed.

(encapsulate
 (((predicate *) => *))
  (local (defun predicate (x) x)))

(defun all (set-for-all-reduction)
  (declare (xargs :guard (setp set-for-all-reduction)))
  (if (empty set-for-all-reduction)
      t
    (and (predicate (head set-for-all-reduction))
	 (all (tail set-for-all-reduction)))))

(encapsulate
 (((all-hyps) => *)
  ((all-set) => *))

 (local (defun all-hyps () nil))
 (local (defun all-set () nil))

 (defthmd membership-constraint
   (implies (all-hyps)
	    (implies (in arbitrary-element (all-set))
		     (predicate arbitrary-element))))
)

(defthmd all-by-membership
  (implies (all-hyps)
	   (all (all-set))))

(defund subset-trigger (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (subset X Y))

(defthm pick-a-point-subset-strategy
  (implies (and (syntaxp (rewriting-goal-lit mfc state))
		(syntaxp (rewriting-conc-lit `(subset ,X ,Y) mfc state)))
	   (equal (subset X Y)
		  (subset-trigger X Y))))

(COMPUTED-HINTS::automate-instantiation
  :new-hint-name pick-a-point-subset-hint
  :generic-theorem all-by-membership
  :generic-predicate predicate
  :generic-hyps all-hyps
  :generic-collection all-set
  :generic-collection-predicate all
  :actual-collection-predicate subset
  :actual-trigger subset-trigger
  :predicate-rewrite (((predicate ?x ?y) (in ?x ?y)))
  :tagging-theorem pick-a-point-subset-strategy
)

(defthm double-containment
  (implies (and (setp X)
                (setp Y))
           (equal (equal X Y)
                  (and (subset X Y)
                       (subset Y X)))))



; -------------------------------------------------------------------
; Primitives Level Theorems

(defthm sets-are-true-lists
  (implies (setp X)
	   (true-listp X)))

(defthm tail-count
  (implies (not (empty X))
           (< (acl2-count (tail X)) (acl2-count X)))
  :rule-classes :linear)

(defthm head-count
  (implies (not (empty X))
           (< (acl2-count (head X)) (acl2-count X)))
  :rule-classes :linear)

(defthm insert-insert
  (equal (insert a (insert b X))
         (insert b (insert a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm sfix-produces-set
  (setp (sfix X)))

(defthm tail-produces-set
  (setp (tail X)))

(defthm insert-produces-set
  (setp (insert a X)))

(defthm insert-never-empty
  (not (empty (insert a X))))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

(defthm nonempty-means-set
  (implies (not (empty X)) (setp X)))

(defthm sfix-set-identity
  (implies (setp X) (equal (sfix X) X)))

(defthm empty-sfix-cancel
  (equal (empty (sfix X)) (empty X)))

(defthm head-sfix-cancel
  (equal (head (sfix X)) (head X)))

(defthm tail-sfix-cancel
  (equal (tail (sfix X)) (tail X)))

(defthm insert-head-tail
  (implies (not (empty X))
           (equal (insert (head X) (tail X)) X)))

(defthm repeated-insert
  (equal (insert a (insert a X))
         (insert a X)))

(defthm insert-sfix-cancel
  (equal (insert a (sfix X)) (insert a X)))

(defthm head-insert-empty
  (implies (empty X)
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
           (empty (tail (insert a X)))))




; -------------------------------------------------------------------
; Membership Level Theorems

(defthm not-in-self
  (not (in x x)))

(defthm in-sfix-cancel
  (equal (in a (sfix X)) (in a X)))

(defthm never-in-empty
  (implies (empty X) (not (in a X))))

(defthm in-set
  (implies (in a X) (setp X)))

(defthm in-tail
  (implies (in a (tail X)) (in a X)))

(defthm in-tail-or-head
  (implies (and (in a X) (not (in a (tail X))))
           (equal (head X) a)))

(defthm head-unique
  (not (in (head X) (tail X))))

(defthm insert-identity
  (implies (in a X) (equal (insert a X) X)))

(defthm in-insert
  (equal (in a (insert b X))
         (or (in a X)
             (equal a b))))

(defthm subset-transitive
  (implies (and (subset X Y) (subset Y Z))
           (subset X Z)))

(defthm subset-insert-X
  (equal (subset (insert a X) Y)
         (and (subset X Y)
              (in a Y))))

(defthm subset-sfix-cancel-X
  (equal (subset (sfix X) Y) (subset X Y)))

(defthm subset-sfix-cancel-Y
  (equal (subset X (sfix Y)) (subset X Y)))

(defthm subset-in
  (implies (and (subset X Y) (in a X))
           (in a Y)))

(defthm subset-in-2
  (implies (and (subset X Y) (not (in a Y)))
           (not (in a X))))

(defthm empty-subset
  (implies (empty X) (subset X Y)))

(defthm empty-subset-2
  (implies (empty Y)
	   (equal (subset X Y) (empty X))))

(defthm subset-reflexive
  (subset X X))

(defthm subset-insert
  (subset X (insert a X)))

(defthm subset-tail
  (subset (tail X) X)
  :rule-classes ((:rewrite)
		 (:forward-chaining :trigger-terms ((tail x)))))



; -------------------------------------------------------------------
; Weakly Inducting over Insertions

(defthm weak-insert-induction-helper-1
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (head (insert a X)) (head X))))

(defthm weak-insert-induction-helper-2
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (tail (insert a X)) (insert a (tail X)))))

(defthm weak-insert-induction-helper-3
  (implies (and (not (in a X))
                (equal (head (insert a X)) a))
           (equal (tail (insert a X)) (sfix X))))

(defun weak-insert-induction (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((in a X) nil)
        ((equal (head (insert a X)) a) nil)
        (t (list (weak-insert-induction a (tail X))))))

(defthm use-weak-insert-induction t
  :rule-classes ((:induction
                  :pattern (insert a X)
                  :scheme (weak-insert-induction a X))))




; -------------------------------------------------------------------
; Outer Level Theorems

(defthm delete-delete
  (equal (delete a (delete b X))
         (delete b (delete a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm delete-set
  (setp (delete a X)))

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



(defthm union-symmetric
  (equal (union X Y) (union Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

(defthm union-commutative
  (equal (union X (union Y Z))
         (union Y (union X Z)))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

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

(defthm union-subset-X
  (subset X (union X Y)))

(defthm union-subset-Y
  (subset Y (union X Y)))

(defthm union-self
  (equal (union X X) (sfix X)))

(defthm union-associative
  (equal (union (union X Y) Z)
         (union X (union Y Z))))

(defthm union-outer-cancel
  (equal (union X (union X Z))
         (union X Z)))



(defthm intersect-symmetric
  (equal (intersect X Y) (intersect Y X))
  :rule-classes ((:rewrite :loop-stopper ((X Y)))))

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

(defthm intersect-in
  (equal (in a (intersect X Y))
         (and (in a Y) (in a X))))

(defthm intersect-subset-X
  (subset (intersect X Y) X))

(defthm intersect-subset-Y
  (subset (intersect X Y) Y))

(defthm intersect-self
  (equal (intersect X X) (sfix X)))

(defthm intersect-associative
  (equal (intersect (intersect X Y) Z)
         (intersect X (intersect Y Z))))

(defthmd union-over-intersect
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

(defthm difference-in
  (equal (in a (difference X Y))
         (and (in a X)
              (not (in a Y)))))

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


(defthm cardinality-type
  (and (integerp (cardinality X))
       (<= 0 (cardinality X)))
  :rule-classes :type-prescription)

(defthm cardinality-zero-empty
  (equal (equal (cardinality x) 0)
	 (empty x)))

(defthm cardinality-sfix-cancel
  (equal (cardinality (sfix X)) (cardinality X)))

(defthm insert-cardinality
  (equal (cardinality (insert a X))
         (if (in a X)
             (cardinality X)
           (1+ (cardinality X)))))

(defthm delete-cardinality
  (equal (cardinality (delete a X))
         (if (in a X)
             (1- (cardinality X))
           (cardinality X))))

(defthm subset-cardinality
  (implies (subset X Y)
           (<= (cardinality X) (cardinality Y)))
  :rule-classes (:rewrite :linear))

(defthmd equal-cardinality-subset-is-equality
  (implies (and (setp X)
                (setp Y)
                (subset X Y)
                (equal (cardinality X) (cardinality Y)))
           (equal (equal X Y) t)))

(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y)) (cardinality X))
  :rule-classes :linear)

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y)) (cardinality Y))
  :rule-classes :linear)

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



; -------------------------------------------------------------------
; Mergesort Theorems

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

(defthm mergesort-set
  (setp (mergesort x)))

(defthm in-mergesort
  (equal (in a (mergesort x))
	 (in-list a x)))

(defthm mergesort-set-identity
  (implies (setp X)
	   (equal (mergesort X) X)))


