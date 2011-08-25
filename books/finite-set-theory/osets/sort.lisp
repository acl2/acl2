#|

   Fully Ordered Finite Sets, Version 0.91
   Copyright (C) 2003-2006 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.



 sort.lisp

   We implement a mergesort which can convert lists into sets more
   efficiencly than repeated insertion.  Logically, (mergesort x)
   is exactly the same as repeated insertion, so it is fairly easy
   to reason about.  But, under the hood, mergesort is implemented
   fairly efficiently using MBE.

   The sort we implement is probably not "blisteringly fast".  Most
   of the literature on the subject suggests using a bubblesort when
   we get down to some threshold, say 40 elements.  I'm not going to
   bother with any of that.  If you find that the mergesort's perfor-
   mance is inadequate, which is unlikely, you can work on making it
   faster.

   There are a few points of interest.  If you look at the actual
   sort code (mergesort-exec), you will see that it is actually using
   the set library's own union function to perform the union.  This
   is pretty slick because union is linear complexity, and yet is
   easy to reason about since we have already got a lot of theory in
   place about it.

   In any case, our strategy for proving the equality of this merge-
   sort with a simple insert-sort is the exact same trick we use
   everywhere else in the sets library.  We begin by showing that
   both produce sets, and then show that membership in either is
   true exactly when an element is member-equal in the original list.

|#

(in-package "SETS")
(include-book "outer")
(local (include-book "unicode/app" :dir :system))
(local (include-book "unicode/rev" :dir :system))
(set-verify-guards-eagerness 2)



(local (defthm app-of-cons-of-list-fix
         (equal (acl2::app x (cons a (acl2::list-fix y)))
                (acl2::app x (cons a y)))
         :hints(("Goal" :induct (len x)))))



; A List Membership Function
;
; The current member-equal function has weird semantics, returning a
; list rather than a boolean value.  We provide a convenient
; alternative which always returns t or nil instead.
;
; We don't try to develop a complete theory for this function here,
; but we will provide several useful utility theorems for relating in
; with the common list functions such as cons, append, and reverse.
; In the future we might want to expand this section to include more
; theorems.

;;; BOZO this is really gross.  We should get rid of in-list and just
;;; use member-equal, or memberp from somewhere else.

(defun in-list (a x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (or (equal a (car x))
	(in-list a (cdr x)))))

(defthm in-list-cons
  (equal (in-list a (cons b x))
	 (or (equal a b)
	     (in-list a x))))

(defthm in-list-append
  (equal (in-list a (append x y))
	 (or (in-list a x)
	     (in-list a y))))

(local (defthm in-list-list-fix
         (equal (in-list a (acl2::list-fix x))
                (in-list a x))))

(local (defthm in-list-app
         (equal (in-list a (acl2::app x y))
                (or (in-list a x)
                    (in-list a y)))))

(local (defthm in-list-rev
         (equal (in-list a (acl2::rev x))
                (in-list a x))))

(encapsulate nil

  (local (defthm lemma
	   (implies (in-list a acc)
		    (in-list a (revappend x acc)))))

  (defthm in-list-revappend
    (equal (in-list a (revappend x y))
	   (or (in-list a x)
	       (in-list a y))))
)

(defthm in-list-reverse
  (equal (in-list a (reverse x))
	 (in-list a x)))

(defthm in-list-on-set
  (implies (setp X)
	   (equal (in-list a X)
		  (in a X)))
  :hints(("Goal" :in-theory (enable sfix head tail empty setp))))




; Historic Notes.
;
; Originally I used the following function to split the list.
;
;  (defun split-list-old (x)
;    (declare (xargs :guard (true-listp x)))
;    (cond ((endp x) (mv nil nil))
;          ((endp (cdr x)) (mv (list (car x)) nil))
;          (t (mv-let (part1 part2)
;                     (split-list-old (cddr x))
;                     (mv (cons (car x) part1)
;                         (cons (cadr x) part2)))))))
;
; But David Rager noted that this was not tail recursive, and accordingly
; it ran into trouble on large data sets.  Accordingly, in Version 0.91,
; I rewrote this to be tail recursive:
;
;  (defun split-list (x acc acc2)
;   (declare (xargs :guard (true-listp x)))
;   (cond ((endp x)
;          (mv acc acc2))
;         ((endp (cdr x))
;          (mv (cons (car x) acc) acc2))
;         (t (split-list (cddr x)
;                        (cons (car x) acc)
;                        (cons (cadr x) acc2)))))
;
; Since then, I wrote the defsort/defsort library, which uses some tricks to
; provide a faster mergesort.  One key optimization is to take the first and
; second halves of the list, rather than splitting the list in terms of evens
; and odds.  This allows you to split the list with half as much consing.
;
; Defsort's approach uses a lot of arithmetic optimization.  I later wrote a
; mergesort for Milawa, where arithmetic is expensive.  Here, I implemented
; split-list by walking down "one cdr" and "two cdrs" at a time.  Below is a
; reimplementation of this strategy for osets.

(defund halve-list-aux (mid x acc)
  (declare (xargs :guard (<= (len x) (len mid))))

; We split the list by walking down it in a funny way; see halve-list.
; Initially, mid and x both point to the front of the list.  We walk down x
; taking two steps for every one step we take for mid; hence mid stays at the
; middle of the list.  As we traverse mid, we puts its members into acc, and
; when x runs out we return both acc and the rest of mid.  This effectively
; lets us split the list in two (1) without doing any arithmetic, which can be
; expensive since we can't use fixnum declarations, and (2) while consing only
; (1/2)n times, where n is the length of the list.  This splitting function
; performs well, handily beating the old osets split-list implementation on a
; large list of symbols which we used to test it.

  (if (or (atom x)
          (atom (cdr x)))
      (mv acc mid)
    (halve-list-aux (cdr mid)
                    (cdr (cdr x))
                    (cons (car mid) acc))))

(defund halve-list (x)
  (declare (xargs :guard t))
  (halve-list-aux x x nil))

(defthm halve-list-aux-when-not-consp
  (implies (not (consp x))
           (equal (halve-list-aux mid x acc)
                  (list acc mid)))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-aux-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (halve-list-aux mid x acc)
                  (list acc mid)))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-aux-len-1
  (implies (and (<= (len x) (len mid))
                (consp x)
                (consp (cdr x)))
           (< (len (car (halve-list-aux mid x acc)))
              (+ (len mid) (len acc))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(defthm halve-list-aux-len-2
  (implies (and (<= (len x) (len mid))
                (consp x)
                (consp (cdr x)))
           (< (len (second (halve-list-aux mid x acc)))
              (len mid)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable halve-list-aux))))

(local (defthm halve-list-aux-append-property
         (implies (<= (len x) (len mid))
                  (equal (acl2::app (acl2::rev (first (halve-list-aux mid x acc)))
                                    (second (halve-list-aux mid x acc)))
                         (acl2::app (acl2::rev acc)
                                    mid)))
         :hints(("Goal"
                 :in-theory (enable halve-list-aux)
                 :do-not '(generalize fertilize)))))

(local (defthm halve-list-correct
         (equal (acl2::app (acl2::rev (first (halve-list x)))
                           (second (halve-list x)))
                (acl2::list-fix x))
         :hints(("Goal" :in-theory (enable halve-list)))))

(defthm halve-list-len-1
  (implies (and (consp x)
                (consp (cdr x)))
           (< (len (first (halve-list x)))
              (len x)))
  :hints(("Goal"
          :in-theory (e/d (halve-list)
                          (halve-list-aux-len-1))
          :use ((:instance halve-list-aux-len-1
                           (mid x) (x x) (acc nil))))))

(defthm halve-list-len-2
  (implies (and (consp x)
                (consp (cdr x)))
           (< (len (second (halve-list x)))
              (len x)))
  :hints(("Goal" :in-theory (enable halve-list))))

(defthm halve-list-membership-property
  (equal (in-list a x)
         (or (in-list a (first (halve-list x)))
             (in-list a (second (halve-list x)))))
  :rule-classes nil
  :hints(("Goal"
          :in-theory (disable in-list-app)
          :use ((:instance in-list-app
                           (x (acl2::rev (first (halve-list x))))
                           (y (second (halve-list x))))))))

(defun mergesort-exec (x)
  (declare (xargs :guard t
                  :measure (len x)
                  :hints(("Goal"
                          :use ((:instance halve-list-len-1)
                                (:instance halve-list-len-2))))
                  :verify-guards nil))
  (cond ((atom x) nil)
        ((atom (cdr x))
         (mbe :logic (insert (car x) nil)
              :exec (list (car x))))
        (t (mv-let (part1 part2)
                   (halve-list x)
                   (fast-union (mergesort-exec part1)
                               (mergesort-exec part2)
                               nil)))))

(local (defthm fast-union-is-union
         (implies (and (setp x)
                       (setp y))
                  (equal (fast-union x y nil)
                         (union x y)))
         :hints(("Goal" :in-theory (enable fast-union-theory)))))

(local (defthm mergesort-exec-set
         (setp (mergesort-exec x))))

(local (defthm mergesort-membership-2
         (implies (in-list a x)
                  (in a (mergesort-exec x)))
         :hints(("Subgoal *1/3" :use (:instance halve-list-membership-property)))))

(local (defthm mergesort-membership-1
         (implies (in a (mergesort-exec x))
                  (in-list a x))
         :hints(("Subgoal *1/6" :use (:instance halve-list-membership-property))
                ("Subgoal *1/5" :use (:instance halve-list-membership-property))
                ("Subgoal *1/4" :use (:instance halve-list-membership-property)))))

(local (defthm mergesort-membership
         (iff (in a (mergesort-exec x))
              (in-list a x))))

(verify-guards mergesort-exec
               :hints(("Goal" :in-theory (e/d (primitives-theory)
                                              (mv-nth)))))


(defun mergesort (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (mbe :logic (if (endp x)
		  nil
		(insert (car x)
			(mergesort (cdr x))))
       :exec (mergesort-exec x)))

(defthm mergesort-set
  (setp (mergesort x)))

(defthm in-mergesort
  (equal (in a (mergesort x))
	 (in-list a x)))

(verify-guards mergesort)

(defthm mergesort-set-identity
  (implies (setp X)
	   (equal (mergesort X) X))
  :hints(("Goal" :in-theory (enable setp sfix head tail empty))))
