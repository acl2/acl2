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


; sort.lisp -- a mergesort for constructing sets

(in-package "SET")
(include-book "union")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(set-verify-guards-eagerness 2)

(local (defthm member-of-append
         (iff (member a (append x y))
              (or (member a x)
                  (member a y)))))

(local (defthm member-of-list-fix
         (iff (member a (acl2::list-fix x))
              (member a x))))

(local (defthm member-of-rev
         (iff (member a (acl2::rev x))
              (member a x))))

(local (defthm append-assoc
         (equal (append (append x y) z)
                (append x (append y z)))))

(defsection halve-list
  :parents (mergesort)
  :short "How we split the list for mergesort."

  :long "<p>Originally I used the following function to split the list.</p>

@({
  (defun split-list-old (x)
    (declare (xargs :guard (true-listp x)))
    (cond ((endp x) (mv nil nil))
          ((endp (cdr x)) (mv (list (car x)) nil))
          (t (mv-let (part1 part2)
                     (split-list-old (cddr x))
                     (mv (cons (car x) part1)
                         (cons (cadr x) part2)))))))
})

<p>But David Rager noted that this was not tail recursive, and accordingly it
ran into trouble on large data sets.  Accordingly, in Version 0.91, I rewrote
this to be tail recursive:</p>

@({
 (defun split-list (x acc acc2)
   (declare (xargs :guard (true-listp x)))
   (cond ((endp x)
          (mv acc acc2))
         ((endp (cdr x))
          (mv (cons (car x) acc) acc2))
         (t (split-list (cddr x)
                        (cons (car x) acc)
                        (cons (cadr x) acc2)))))
})

<p>Since then, I wrote the @('defsort/defsort') library, which uses some tricks
to provide a faster mergesort.  One key optimization is to take the first and
second halves of the list, rather than splitting the list in terms of evens and
odds.  This allows you to split the list with half as much consing.</p>

<p>Defsort's approach uses a lot of arithmetic optimization.  I later wrote a
mergesort for Milawa, where arithmetic is expensive.  Here, I implemented
split-list by walking down \"one cdr\" and \"two cdrs\" at a time.  I now use
this same strategy in osets.</p>

<p>BOZO this strategy is still stupidly re-consing up half the list, when
really we could avoid that by just being a bit smarter, like in defsort.</p>"

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
    (halve-list-aux x x nil)))


(defsection halve-list-thms

  ;; Keep these in a separate section.  We don't want to try to include them in
  ;; the xdoc documentation, because they're not theorems that are going to be
  ;; included in sets/top.lisp.

  (local (in-theory (enable halve-list-aux)))

  (local (defthm halve-list-aux-when-not-consp
           (implies (not (consp x))
                    (equal (halve-list-aux mid x acc)
                           (list acc mid)))))

  (local (defthm halve-list-aux-when-not-consp-of-cdr
           (implies (not (consp (cdr x)))
                    (equal (halve-list-aux mid x acc)
                           (list acc mid)))))

  (local (defthm halve-list-aux-len-1
           (implies (and (<= (len x) (len mid))
                         (consp x)
                         (consp (cdr x)))
                    (< (len (mv-nth 0 (halve-list-aux mid x acc)))
                       (+ (len mid) (len acc))))
           :rule-classes ((:rewrite) (:linear))))

  (local (defthm halve-list-aux-len-2
           (implies (and (<= (len x) (len mid))
                         (consp x)
                         (consp (cdr x)))
                    (< (len (mv-nth 1 (halve-list-aux mid x acc)))
                       (len mid)))
           :rule-classes ((:rewrite) (:linear))))

  (local (defthm halve-list-aux-append-property
           (implies (<= (len x) (len mid))
                    (equal (append (acl2::rev (mv-nth 0 (halve-list-aux mid x acc)))
                                   (mv-nth 1 (halve-list-aux mid x acc)))
                           (append (acl2::rev acc)
                                   mid)))
           :hints(("Goal" :do-not '(generalize fertilize)))))

  (local (defthm halve-list-correct
           (equal (append (acl2::rev (mv-nth 0 (halve-list x)))
                          (mv-nth 1 (halve-list x)))
                  x)
           :hints(("Goal" :in-theory (enable halve-list)))))

  (defthm halve-list-len-1
    (implies (and (consp x)
                  (consp (cdr x)))
             (< (len (mv-nth 0 (halve-list x)))
                (len x)))
    :hints(("Goal"
            :in-theory (e/d (halve-list)
                            (halve-list-aux-len-1))
            :use ((:instance halve-list-aux-len-1
                             (mid x) (x x) (acc nil))))))

  (defthm halve-list-len-2
    (implies (and (consp x)
                  (consp (cdr x)))
             (< (len (mv-nth 1 (halve-list x)))
                (len x)))
    :hints(("Goal" :in-theory (enable halve-list))))

  (defthm halve-list-membership-property
    (iff (member a x)
         (or (member a (mv-nth 0 (halve-list x)))
             (member a (mv-nth 1 (halve-list x)))))
    :rule-classes nil
    :hints(("Goal"
            :do-not-induct t
            :in-theory (disable member-of-append)
            :use ((:instance member-of-append
                             (x (acl2::rev (mv-nth 0 (halve-list x))))
                             (y (mv-nth 1 (halve-list x)))))))))


(defsection mergesort-exec
  :parents (mergesort)
  :short "The implementation of mergesort."

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
                           nil))))))


(defsection mergesort-exec-thms

  ;; Keep this separate from mergesort-exec, for the same reason as in
  ;; halve-list-thms

  (local (in-theory (enable fast-union-set
                            fast-union-membership)))

  (defthm mergesort-exec-set
    (setp (mergesort-exec x)))

  (local (defthm mergesort-membership-2
           (implies (member a x)
                    (in a (mergesort-exec x)))
           :hints(("Subgoal *1/3" :use (:instance halve-list-membership-property)))))

  (local (defthm mergesort-membership-1
           (implies (in a (mergesort-exec x))
                    (member a x))
           :hints(("Subgoal *1/6" :use (:instance halve-list-membership-property))
                  ("Subgoal *1/5" :use (:instance halve-list-membership-property))
                  ("Subgoal *1/4" :use (:instance halve-list-membership-property)))))

  (defthm mergesort-exec-membership
    (iff (in a (mergesort-exec x))
         (member a x)))

  (verify-guards mergesort-exec
    :hints(("Goal" :in-theory (e/d ((:ruleset primitive-rules))
                                   (mv-nth))))))


(defsection mergesort
  :parents (std/osets)
  :short "@(call mergesort) converts the list @('X') into an ordered set."

  :long "<p>Logically, @('(mergesort x)') is exactly the same as repeated
insertion, so it is fairly easy to reason about.  But in the execution,
mergesort is implemented with a reasonably efficient sort with O(n log n)
performance instead of O(n^2) like repeated insertion.</p>

<p>Our implementation is probably not blisteringly fast.  Folklore says we
should switch to using a bubblesort when we get down to some threshold, say 40
elements.  I'm not going to bother with any of that.  If you find that the
mergesort's performance is inadequate, which is unlikely, you can work on
making it faster.</p>

<p>There are a few points of interest.  If you look at the actual sort code,
@(see mergesort-exec), you will see that it is actually using the set library's
own @(see union) function to perform the union.  This is pretty slick because
union is linear complexity, and yet is easy to reason about since we have
already got a lot of theory in place about it.</p>

<p>In any case, our strategy for proving the equality of this mergesort with a
simple insertion sort is the exact same trick we use everywhere else in the
sets library.  We begin by showing that both produce sets, and then show that
membership in either is true exactly when an element is @(see member-equal) in
the original list.</p>"

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
           (if (member a x)
               t
             nil)))

  (local (in-theory (enable subset)))

  (verify-guards mergesort)

  (defthm mergesort-set-identity
    (implies (setp X)
             (equal (mergesort X) X))
    :hints(("Goal" :in-theory (enable (:ruleset primitive-rules))))))
