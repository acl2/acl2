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


; top.lisp
;
; This is the top level file, which you should include to use the ordered set
; theory library.  Note that it does NOT include:
;
;   - The quantification extension for quantifying predicates over sets (i.e.,
;     for defining "typed" sets); see quantify.lisp instead, or
;
;   - The map extension for mapping/projecting a function across a set; see
;     map.lisp instead.
;
; The definitions in this file are redundant from the local include books.
; This approach has several advantages.
;
;  - it gives a better event order than simply including the books one by one
;
;  - this file is also faster to include than all of the local books below, and
;    allows the "ugliness" of auxilliary lemmas to be hidden away
;
;  - it makes clear that these theorems are public, and entirely prevents the
;    use of "internal" lemmas and theorems.

(in-package "SET")
(set-verify-guards-eagerness 2)

; We now directly use the total order from misc/total-order.
(include-book "misc/total-order" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)

; We need some program-mode definitions which are used in order to automate the
; pick-a-point strategies.
(include-book "computed-hints")

(local
 ;; Another part of the xdoc hack -- make sure this documentation doesn't
 ;; get inadvertently slurped in
 (include-book "std/lists/sets" :dir :system))
(local
 ;; xdoc hack part 1: throw away all current xdoc
 (table xdoc::xdoc 'xdoc::doc nil))

(local (include-book "primitives"))
(local (include-book "membership"))
(local (include-book "outer"))
(local (include-book "sort"))
(local (include-book "under-set-equiv"))

(make-event
 ;; xdoc hack part 2: take all the docs we got from the local includes and
 ;; stick them onto the proper doc
 (let ((slurped-docs (xdoc::get-xdoc-table (w state))))
   (acl2::value `(table xdoc::xdoc 'xdoc::doc
                        (union-equal ',slurped-docs (xdoc::get-xdoc-table acl2::world))))))

(defxdoc std/osets
  :parents (std)
  :short "A finite set theory implementation for ACL2 based on fully ordered
lists.  Some major features of this approach are that set equality is just
@(see equal), and set operations like @(see union), @(see intersect), and so
forth have O(n) implementations."

  :long "<p>Osets mostly hides the fact that sets are represented as ordered
lists.  You should not have to reason about the set order unless you are trying
to exploit it to make some function faster.  Instead, we generally try to
reason about sets with a membership-based approach, via @(see in) and @(see
subset).</p>

<p>The osets library offers some automation for pick-a-point style reasoning,
see for instance @(see all-by-membership), @(see pick-a-point-subset-strategy),
and @(see double-containment).</p>

<p>You can load the library with:</p>
@({
 (include-book \"std/osets/top\" :dir :system)
})

<p>The definitions of the main set-manipulation functions are disabled, but are
in a ruleset and may be enabled using:</p>
@({
 (in-theory (acl2::enable* set::definitions))
})

<p>Some potentially useful (but potentially expensive) rules are also left
disabled and may be enabled using:</p>
@({
 (in-theory (acl2::enable* set::expensive-rules))
})

<p>Besides this @(see xdoc::xdoc) documentation, you may be interested in the
2004 ACL2 workshop paper, <a
href='https://www.cs.utexas.edu/users/moore/acl2/workshop-2004/contrib/davis/set-theory.pdf'>Finite
Set Theory based on Fully Ordered Lists</a>, and see also the <a
href='https://www.cs.utexas.edu/users/moore/acl2/workshop-2004/contrib/davis/workshop-osets-slides.pdf'>slides</a>
from the accompanying talk.</p>")

; We begin with the definitions of the set theory functions and a few trivial
; type prescriptions.

(defund setp (X)
  (declare (xargs :guard t))
  (if (atom X)
      (null X)
    (or (null (cdr X))
        (and (consp (cdr X))
             (fast-<< (car X) (cadr X))
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
  (mbe :logic (cond ((empty X) (list a))
                    ((equal (head X) a) X)
                    ((<< a (head X)) (cons a X))
                    (t (cons (head X) (insert a (tail X)))))
       :exec
       (cond ((null X) (cons a nil))
             ((equal (car X) a) X)
             ((fast-lexorder a (car X)) (cons a X))
             ((null (cdr X)) (cons (car X) (cons a nil)))
             ((equal (cadr x) a) X)
             ((fast-lexorder a (cadr X)) (cons (car X) (cons a (cdr X))))
             (t (cons (car X) (cons (cadr X) (insert a (cddr X))))))))

(defun in (a X)
  (declare (xargs :guard (setp X)))
  (mbe :logic
       (and (not (empty X))
            (or (equal a (head X))
                (in a (tail X))))
       :exec
       (and x
            (or (equal a (car x))
                (and (cdr x)
                     (or (equal a (cadr x))
                         (in a (cddr x))))))))

(defthm in-type
  (or (equal (in a X) t)
      (equal (in a X) nil))
  :rule-classes :type-prescription)

(defund fast-subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic
       (cond ((empty X) t)
             ((empty Y) nil)
             ((<< (head X) (head Y)) nil)
             ((equal (head X) (head Y)) (fast-subset (tail X) (tail Y)))
             (t (fast-subset X (tail Y))))
       :exec
       (cond ((null X) t)
             ((null Y) nil)
             ((fast-lexorder (car X) (car Y))
              (and (equal (car X) (car Y))
                   (fast-subset (cdr X) (cdr Y))))
             (t
              (fast-subset X (cdr Y))))))

(defun subset (X Y)
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

(defun fast-union (x y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp x)
                              (setp y)
                              (true-listp acc))))
  (cond ((endp x) (revappend acc y))
        ((endp y) (revappend acc x))
        ((equal (car x) (car y))
         (fast-union (cdr x) (cdr y) (cons (car x) acc)))
        ((mbe :logic (<< (car x) (car y))
              :exec (fast-lexorder (car x) (car y)))
         (fast-union (cdr x) y (cons (car x) acc)))
        (t
         (fast-union x (cdr y) (cons (car y) acc)))))

(defun fast-intersect (X Y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X)
                              (setp Y)
                              (true-listp acc))))
  (cond ((endp X) (revappend acc nil))
        ((endp Y) (revappend acc nil))
        ((equal (car X) (car Y))
         (fast-intersect (cdr X) (cdr Y) (cons (car X) acc)))
        ((mbe :logic (<< (car X) (car Y))
              :exec (fast-lexorder (car X) (car Y)))
         (fast-intersect (cdr X) Y acc))
        (t
         (fast-intersect X (cdr Y) acc))))

(defun fast-intersectp (X Y)
  (declare (xargs :guard (and (setp X)
                              (setp Y))
                  :measure (fast-measure X Y)))
  (cond ((endp X) nil)
        ((endp Y) nil)
        ((equal (car X) (car Y))
         t)
        ((mbe :logic (<< (car X) (car y))
              :exec (fast-lexorder (car X) (car Y)))
         (fast-intersectp (cdr X) Y))
        (t
         (fast-intersectp X (cdr Y)))))

(defun fast-difference (X Y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X)
                              (setp Y)
                              (true-listp acc))))
  (cond ((endp X) (revappend acc nil))
        ((endp Y) (revappend acc X))
        ((equal (car X) (car Y))
         (fast-difference (cdr X) (cdr Y) acc))
        ((mbe :logic (<< (car X) (car Y))
              :exec (fast-lexorder (car X) (car Y)))
         (fast-difference (cdr X) Y (cons (car X) acc)))
        (t
         (fast-difference X (cdr Y) acc))))

(defun delete (a X)
  (declare (xargs :guard (setp X)))
  (mbe :logic
       (cond ((empty X) nil)
             ((equal a (head X)) (tail X))
             (t (insert (head X) (delete a (tail X)))))
       :exec
       (cond ((endp X) nil)
             ((equal a (car X)) (cdr X))
             (t (insert (car X) (delete a (cdr X)))))))

(defun union (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (if (empty X)
                  (sfix Y)
                (insert (head X) (union (tail X) Y)))
       :exec  (fast-union X Y nil)))

(defun intersect (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y)
                     (insert (head X) (intersect (tail X) Y)))
                    (t (intersect (tail X) Y)))
       :exec (fast-intersect X Y nil)))

(defun intersectp (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (not (empty (intersect X Y)))
       :exec (fast-intersectp X Y)))

(defun difference (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (mbe :logic (cond ((empty X) (sfix X))
                    ((in (head X) Y) (difference (tail X) Y))
                    (t (insert (head X) (difference (tail X) Y))))
       :exec (fast-difference X Y nil)))

(defun cardinality (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X)
                  0
                (1+ (cardinality (tail X))))
       :exec  (length (the list X))))

(defund halve-list-aux (mid x acc)
  (declare (xargs :guard (<= (len x) (len mid))))
  (if (or (atom x)
          (atom (cdr x)))
      (mv acc mid)
    (halve-list-aux (cdr mid)
                    (cdr (cdr x))
                    (cons (car mid) acc))))

(defund halve-list (x)
  (declare (xargs :guard t))
  (halve-list-aux x x nil))

(defun mergesort-exec (x)
  (declare (xargs :guard t
                  :measure (len x)))
  (cond ((atom x) nil)
        ((atom (cdr x))
         (mbe :logic (insert (car x) nil)
              :exec (list (car x))))
        (t (mv-let (part1 part2)
                   (halve-list x)
                   (fast-union (mergesort-exec part1)
                               (mergesort-exec part2)
                               nil)))))

(defun mergesort (x)
  (declare (xargs :guard t))
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
		     (predicate arbitrary-element)))))

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
  :tagging-theorem pick-a-point-subset-strategy)

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

(defthm double-containment
  (implies (and (setp X)
                (setp Y))
           (equal (equal X Y)
                  (and (subset X Y)
                       (subset Y X))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))



; -------------------------------------------------------------------
; Primitive Level Theorems

; Updated 9/2017 by Matt K. (following Eric Smith's suggestion after input from
; Alessandro Coglio and David Rager): The following rule usually stays
; disabled, as the ones below may be much cheaper.

(defthmd sets-are-true-lists
  (implies (setp X)
	   (true-listp X)))

(defthm sets-are-true-lists-compound-recognizer
       (implies (setp X)
                (true-listp X))
       :rule-classes :compound-recognizer)

; The following usually stays enabled.  The first try was with backchain-limit
; of 0 but (define vl-lucid-pp-multibits ...) failed in
; books/centaur/vl/lint/lucid.lisp, and (define vl-svex-keyvallist-vars ...)
; failed in books/centaur/sv/vl/expr.lisp.
(defthm sets-are-true-lists-cheap
  (implies (setp X)
           (true-listp X))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthm tail-count
  (implies (not (empty X))
           (< (acl2-count (tail X)) (acl2-count X)))
  :rule-classes ((:rewrite) (:linear)))

(defthm head-count
  (implies (not (empty X))
           (< (acl2-count (head X)) (acl2-count X)))
  :rule-classes ((:rewrite) (:linear)))

(defthm tail-count-built-in
  (implies (not (empty X))
           (o< (acl2-count (tail X)) (acl2-count X)))
  :rule-classes :built-in-clause)

(defthm head-count-built-in
  (implies (not (empty X))
           (o< (acl2-count (head X)) (acl2-count X)))
  :rule-classes :built-in-clause)

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

(defthm nonempty-means-set
  (implies (not (empty X))
           (setp X)))

(defthm sfix-set-identity
  (implies (setp X)
           (equal (sfix X)
                  X)))

(defthm empty-sfix-cancel
  (equal (empty (sfix X))
         (empty X)))

(defthm head-sfix-cancel
  (equal (head (sfix X))
         (head X)))

(defthm tail-sfix-cancel
  (equal (tail (sfix X))
         (tail X)))

(defthm insert-head
  (implies (not (empty X))
           (equal (insert (head X) X)
                  X)))

(defthm insert-head-tail
  (implies (not (empty X))
           (equal (insert (head X) (tail X))
                  X)))

(defthm repeated-insert
  (equal (insert a (insert a X))
         (insert a X)))

(defthm insert-sfix-cancel
  (equal (insert a (sfix X))
         (insert a X)))

(defthm head-when-empty
  (implies (empty X)
           (equal (head X)
                  nil)))

(defthm tail-when-empty
  (implies (empty X)
           (equal (tail X)
                  nil)))

(defthm insert-when-empty
  (implies (and (syntaxp (not (equal X ''nil)))
                (empty X))
           (equal (insert a X)
                  (insert a nil))))

(defthm head-of-insert-a-nil
  (equal (head (insert a nil))
         a))

(defthm tail-of-insert-a-nil
  (equal (tail (insert a nil))
         nil))

(defthm sfix-when-empty
  (implies (empty X)
           (equal (sfix X)
                  nil)))


; -------------------------------------------------------------------
; Membership Level Theorems

(defthm subset-membership-tail
  (implies (and (subset X Y)
                (in a (tail X)))
           (in a (tail Y))))

(defthm subset-membership-tail-2
  (implies (and (subset X Y)
                (not (in a (tail Y))))
           (not (in a (tail X)))))

(defthm not-in-self
  (not (in x x)))

(defthm in-sfix-cancel
  (equal (in a (sfix X))
         (in a X)))

(defthm never-in-empty
  (implies (empty X)
           (not (in a X))))

(defthm in-set
  (implies (in a X)
           (setp X)))

(defthm in-tail
  (implies (in a (tail X))
           (in a X)))

(defthm in-tail-or-head
  (implies (and (in a X)
                (not (in a (tail X))))
           (equal (head X)
                  a)))

(defthm in-head
  (equal (in (head X) X)
         (not (empty X))))

(defthm head-unique
  (not (in (head X) (tail X))))

(defthm insert-identity
  (implies (in a X)
           (equal (insert a X)
                  X)))

(defthm in-insert
  (equal (in a (insert b X))
         (or (in a X)
             (equal a b))))

(defthm subset-transitive
  (and (implies (and (subset X Y)
                     (subset Y Z))
                (subset X Z))
       (implies (and (subset Y Z)
                     (subset X Y))
                (subset X Z))))

(defthm subset-insert-X
  (equal (subset (insert a X) Y)
         (and (subset X Y)
              (in a Y))))

(defthm subset-sfix-cancel-X
  (equal (subset (sfix X) Y)
         (subset X Y)))

(defthm subset-sfix-cancel-Y
  (equal (subset X (sfix Y))
         (subset X Y)))

(defthm subset-in
  (and (implies (and (subset X Y)
                     (in a X))
                (in a Y))
       (implies (and (in a X)
                     (subset X Y))
                (in a Y))))

(defthm subset-in-2
  (and (implies (and (subset X Y)
                     (not (in a Y)))
                (not (in a X)))
       (implies (and (not (in a Y))
                     (subset X Y))
                (not (in a X)))))

(defthm empty-subset
  (implies (empty X)
           (subset X Y)))

(defthm empty-subset-2
  (implies (empty Y)
	   (equal (subset X Y)
                  (empty X))))

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

(defthm union-with-subset-left
  (implies (subset X Y)
           (equal (union X Y)
                  (sfix Y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm union-with-subset-right
  (implies (subset X Y)
           (equal (union Y X)
                  (sfix Y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

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

(defthm intersect-with-subset-left
  (implies (subset X Y)
           (equal (intersect X Y)
                  (sfix X)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm intersect-with-subset-right
  (implies (subset X Y)
           (equal (intersect Y X)
                  (sfix X)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

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

; i am here

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
  (equal (cardinality (sfix X))
         (cardinality X)))

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

(defthm proper-subset-cardinality
  (implies (and (subset X Y)
                (not (subset Y X)))
           (< (cardinality X) (cardinality Y)))
  :rule-classes (:rewrite :linear))

(defthmd equal-cardinality-subset-is-equality
  (implies (and (setp X)
                (setp Y)
                (subset X Y)
                (equal (cardinality X) (cardinality Y)))
           (equal (equal X Y) t)))

(defthm intersect-cardinality-X
  (<= (cardinality (intersect X Y))
      (cardinality X))
  :rule-classes (:rewrite :linear))

(defthm intersect-cardinality-Y
  (<= (cardinality (intersect X Y))
      (cardinality Y))
  :rule-classes (:rewrite :linear))

(defthm expand-cardinality-of-union
  (equal (cardinality (union X Y))
         (- (+ (cardinality X) (cardinality Y))
            (cardinality (intersect X Y)))))

(defthm expand-cardinality-of-difference
  (equal (cardinality (difference X Y))
         (- (cardinality X)
            (cardinality (intersect X Y)))))

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



; -------------------------------------------------------------------
; Mergesort Theorems

(defthm mergesort-set
  (setp (mergesort x)))

(defthm in-mergesort
  (equal (in a (mergesort x))
         (if (member a x)
             t
           nil)))

(defthm in-mergesort-under-iff
  (iff (in a (mergesort x))
       (member a x)))

(defthm mergesort-set-identity
  (implies (setp X)
	   (equal (mergesort X) X)))



; -------------------------------------------------------------------
; Rulesets for low level reasoning, generally not needed

(defthmd insert-induction-case
  (implies (and (not (<< a (head X)))
                (not (equal a (head X)))
                (not (empty X)))
           (equal (insert (head X) (insert a (tail X)))
                  (insert a X))))

(defthmd head-insert
  (equal (head (insert a X))
	 (cond ((empty X) a)
	       ((<< a (head X)) a)
	       (t (head X)))))

(defthmd tail-insert
  (equal (tail (insert a X))
	 (cond ((empty X) (sfix X))
	       ((<< a (head X)) (sfix X))
               ((equal a (head X)) (tail X))
               (t (insert a (tail X))))))

(defthmd head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthmd head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

(defthmd head-minimal
  (implies (<< a (head X))
           (not (in a X))))

(defthmd head-minimal-2
  (implies (in a X)
           (not (<< a (head X)))))

(defthmd setp-of-cons
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X)))))

(defthmd in-to-member
  (implies (setp X)
           (equal (in a X)
                  (if (member a x)
                      t
                    nil))))

(defthmd not-member-when-smaller
  (implies (and (<< a (car x))
                (setp x))
           (not (member a x))))

(defthmd subset-to-subsetp
  (implies (and (setp x)
                (setp y))
           (equal (subset x y)
                  (subsetp x y))))

(defthmd lexorder-<<-equiv
  (implies (not (equal a b))
           (equal (equal (<< a b) (lexorder a b))
                  t)))

(make-event
 (let* ((primitive-rules (acl2::get-ruleset 'primitive-rules (w state)))
        (order-rules     (acl2::get-ruleset 'order-rules (w state)))
        (low-level-rules (acl2::get-ruleset 'low-level-rules (w state))))
   (acl2::value `(progn
                   (def-ruleset! primitive-rules ',primitive-rules)
                   (def-ruleset! order-rules ',order-rules)
                   (def-ruleset! low-level-rules ',low-level-rules)))))




; -------------------------------------------------------------------
; Relation to acl2::set-equiv, for lightweight use of sets

(defthm insert-under-set-equiv
  (acl2::set-equiv (insert a x)
                   (cons a (sfix x))))

(defthm delete-under-set-equiv
  (acl2::set-equiv (delete a x)
                   (remove-equal a (sfix x))))

(defthm union-under-set-equiv
  (acl2::set-equiv (union x y)
                   (append (sfix x) (sfix y))))

(defthm intersect-under-set-equiv
  (acl2::set-equiv (intersect x y)
                   (intersection-equal (sfix x) (sfix y))))

(defthm difference-under-set-equiv
  (acl2::set-equiv (difference x y)
                   (set-difference-equal (sfix x) (sfix y))))

(defthm mergesort-under-set-equiv
  (acl2::set-equiv (mergesort x)
                   x))

(defcong acl2::set-equiv equal (mergesort x) 1
  :event-name set-equiv-implies-equal-mergesort-1)


;; This is the set of top-level recursive function definitions (as opposed to
;; fast- or auxiliary ones) that are enabled above this point but that we'll
;; disable shortly to make light set reasoning cheaper.  Note also that if a
;; non-recursive function is left enabled above (e.g. intersectp) then it's
;; treated as basically an abbreviation and we leave it enabled (and out of
;; this ruleset).
(def-ruleset! definitions
  '(in
    subset
    delete
    union
    intersect
    difference
    cardinality
    mergesort))


;; This is a set of rules defined (and left enabled) above that seem
;; potentially expensive.  The determination is somewhat subjective.
(def-ruleset! expensive-rules
  '(pick-a-point-subset-strategy
    double-containment
    subset-membership-tail
    subset-membership-tail-2
    subset-transitive
    subset-in
    subset-in-2
    union-symmetric
    union-commutative
    union-delete-x
    union-delete-y
    union-with-subset-left
    union-with-subset-right
    intersect-symmetric
    intersect-commutative
    intersect-insert-x
    intersect-insert-y
    intersect-with-subset-left
    intersect-with-subset-right
    intersect-over-union
    difference-over-union
    difference-over-intersect
    difference-insert-x
    difference-delete-y
    insert-cardinality
    delete-cardinality
    in-mergesort))


(in-theory (acl2::disable* definitions
                           expensive-rules))
