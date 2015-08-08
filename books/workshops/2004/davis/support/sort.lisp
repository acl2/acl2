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
; sort.lisp
;
; We implement a mergesort which can convert lists into sets more efficiencly
; than repeated insertion.  Logically, (mergesort x) is exactly the same as
; repeated insertion, so it is fairly easy to reason about.  But, under the
; hood, mergesort is implemented fairly efficiently using MBE.
;
; The sort we implement is probably not "blisteringly fast".  Most of the
; literature on the subject suggests using a bubblesort when we get down to
; some threshold, say 40 elements.  I'm not going to bother with any of that.
; If you find that the mergesort's perfor- mance is inadequate, which is
; unlikely, you can work on making it faster.
;
; There are a few points of interest.  If you look at the actual sort code
; (mergesort-exec), you will see that it is actually using the set library's
; own union function to perform the union.  This is pretty slick because union
; is linear complexity, and yet is easy to reason about since we have already
; got a lot of theory in place about it.
;
; In any case, our strategy for proving the equality of this merge- sort with a
; simple insert-sort is the exact same trick we use everywhere else in the sets
; library.  We begin by showing that both produce sets, and then show that
; membership in either is true exactly when an element is member-equal in the
; original list.

(in-package "SET")
(include-book "outer")
(set-verify-guards-eagerness 2)



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

; We now introduce a naive function to split a list into two.

(defun split-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) (mv nil nil))
        ((endp (cdr x)) (mv (list (car x)) nil))
        (t (mv-let (part1 part2)
                   (split-list (cddr x))
                   (mv (cons (car x) part1)
                       (cons (cadr x) part2))))))

(local (defthm split-list-membership
	 (equal (in-list a x)
		(or (in-list a (mv-nth 0 (split-list x)))
		    (in-list a (mv-nth 1 (split-list x)))))))

(local (defthm split-list-part1-truelist
	 (true-listp (mv-nth 0 (split-list x)))
	 :rule-classes :type-prescription))

(local (defthm split-list-part2-truelist
	 (true-listp (mv-nth 1 (split-list x)))
	 :rule-classes :type-prescription))

(local (defthm split-list-length-part1
	 (implies (consp (cdr x))
		  (equal (len (mv-nth 0 (split-list x)))
			 (+ 1 (len (mv-nth 0 (split-list (cddr x)))))))))

(local (defthm split-list-length-part2
	 (implies (consp (cdr x))
		  (equal (len (mv-nth 1 (split-list x)))
			 (+ 1 (len (mv-nth 1 (split-list (cddr x)))))))))

(local (defthm split-list-length-less-part1
	 (implies (consp (cdr x))
		  (< (len (mv-nth 0 (split-list x)))
		     (len x)))))

(local (defthm split-list-length-less-part2
	 (implies (consp (cdr x))
		  (< (len (mv-nth 1 (split-list x)))
		     (len x)))))

(local (in-theory (disable split-list-length-part1
			   split-list-length-part2)))

(defun mergesort-exec (x)
  (declare (xargs
    :guard (true-listp x)
    :measure (len x)
    :hints(("Goal" :use ((:instance split-list-length-less-part1)
                         (:instance split-list-length-less-part2))))
    :verify-guards nil))
  (cond ((endp x) nil)
	((endp (cdr x)) (insert (car x) nil))
        (t (mv-let (part1 part2)
		   (split-list x)
		   (union (mergesort-exec part1) (mergesort-exec part2))))))

(local (defthm mergesort-exec-set
	 (setp (mergesort-exec x))))

(local (in-theory (disable split-list-membership)))

(local (defthm mergesort-membership-2
	 (implies (in-list a x)
		  (in a (mergesort-exec x)))
	 :hints(("Subgoal *1/3" :use (:instance split-list-membership)))))

(local (defthm mergesort-membership-1
	 (implies (in a (mergesort-exec x))
		  (in-list a x))
	 :hints(("Subgoal *1/6" :use (:instance split-list-membership))
		("Subgoal *1/5" :use (:instance split-list-membership))
		("Subgoal *1/4" :use (:instance split-list-membership)))))

(local (defthm mergesort-membership
	 (iff (in a (mergesort-exec x))
	      (in-list a x))))

(verify-guards mergesort-exec
  :hints(("Goal" :in-theory (disable mv-nth))))


(defun mergesort (x)
  (declare (xargs :guard (true-listp x)
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
