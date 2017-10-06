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


; primitives.lisp - setp, sfix, head, tail, etc.

(in-package "SET")
(include-book "misc/total-order" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/top" :dir :system)
(set-verify-guards-eagerness 2)


(defxdoc primitives
  :parents (std/osets)
  :short "Replacements for @('car'), @('cdr'), etc., that respect the
<i>non-set convention</i>."

  :long "<p>Since the osets library uses ordered lists as the underlying
representation of sets, at some point we have to use <b>list
primitives</b> (car, cdr, endp, cons) to operate on sets.  A problem with using
these functions directly is that they do not follow the non-set convention.</p>

<p>The <b>non-set convention</b> is: set operations should treat improper
sets (i.e., non-@('nil') atoms and lists that have duplicated or mis-ordered
elements) as the empty set.  We adopt this convention throughout the library.
It allows most of our rewrite rules to have no @(see setp) hypotheses.</p>

<p>The primitive list functions do follow the non-set convention.  For
instance:</p>

<ul>
 <li>@('(car '(1 1 1)) = 1'),            but @('(car nil) = nil')</li>
 <li>@('(cdr '(1 1 1)) = (1 1)'),        but @('(cdr nil) = nil')</li>
 <li>@('(cons 1 '(1 1 1)) = (1 1 1 1)'), but @('(cons 1 nil) = (1)')</li>
 <li>@('(endp '(1 1 1)) = nil'),         but @('(endp nil) = t')</li>
</ul>

<p>These behaviors make it harder to reason about set operations that are
written directly in terms of the list primitives.  When we try to do so, we
usually have to do lots of work to consider all the cases about whether the
inputs are ordered, etc.</p>

<p>To solve lots of these problems, we introduce new <b>set primitives</b> that
are mostly like the list primitives, except that they follow the non-set
convention.  These primitives are:</p>

<ul>
 <li>@('(head X)') - the first element of a set, nil for non/empty sets</li>
 <li>@('(tail X)') - all rest of the set, nil for non/empty sets</li>
 <li>@('(insert a X)') - ordered insert of @('a') into @('X')</li>
 <li>@('(empty X)') - recognizer for non/empty sets.</li>
</ul>

<p>The general idea is that set operations should be written in terms of these
set primitives instead of the list primitives, and the definitions of the set
primitives should be kept disabled to avoid having to reason about the low
level structure of sets.</p>")


(defsection setp
  :parents (primitives)
  :short "@(call setp) recognizes well-formed ordered sets."

  :long "<p>A proper ordered set is a @(see true-listp) whose elements are
fully ordered under @(see <<).  Note that this implicitly means that sets have
no duplicate elements.</p>

<p>Testing @('setp') is necessarily somewhat slow: we have to check that the
elements are in order.  Its cost is linear in the size of @('n').</p>"

  (defun setp (X)
    (declare (xargs :guard t :verify-guards nil))
    (if (atom X)
        (null X)
      (or (null (cdr X))
          (and (consp (cdr X))
               (fast-<< (car X) (cadr X))
               (setp (cdr X))))))

  (verify-guards setp
    :hints(("Goal" :in-theory (enable <<))))

  (defthm setp-type
    (or (equal (setp X) t)
        (equal (setp X) nil))
    :rule-classes :type-prescription)

   ;; Updated 9/2017 by Matt K. (Eric Smith's suggestion after input from
   ;; Alessandro Coglio and David Rager): The following rule usually stays
   ;; disabled, as the ones below may be much cheaper.
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
     :rule-classes ((:rewrite :backchain-limit-lst (1)))))

(defsection empty
  :parents (primitives)
  :short "@(call empty) recognizes empty sets."

  :long "<p>This function is like @(see endp) for lists, but it respects the
non-set convention and always returns true for ill-formed sets.</p>"

  (defun empty (X)
    (declare (xargs :guard (setp X)))
    (mbe :logic (or (null X)
                    (not (setp X)))
         :exec  (null X)))

  (defthm empty-type
    (or (equal (empty X) t)
        (equal (empty X) nil))
    :rule-classes :type-prescription)

  (defthm nonempty-means-set
    (implies (not (empty X))
             (setp X))))

(defthm empty-set-unique
  ;; BOZO probably expensive.  We don't export this from sets.lisp, and we keep
  ;; it out of the docs above.
  (implies (and (setp X)
                (setp Y)
                (empty X)
                (empty Y))
           (equal (equal X Y)
                  t)))



(defsection sfix
  :parents (primitives)
  :short "@(call sfix) is a fixing function for sets."

  :long "<p>We return any proper @(see setp) unchanged, but coerce any
non-@(see setp) into the empty set.</p>

<p>This does for sets what functions like @(see nfix) or @(see rfix) do for
numbers.  It is often useful to use @('sfix') in the base case of a set
operation to ensure that an ordered set is always produced.</p>"

  (defun sfix (X)
    (declare (xargs :guard (setp X)))
    (mbe :logic (if (empty X) nil X)
         :exec  X))

  (defthm sfix-produces-set
    (setp (sfix X)))

  (defthm sfix-set-identity
    (implies (setp X)
             (equal (sfix X)
                    X)))

  ;; I historically did this instead of sfix-when-empty, but now I think just
  ;; rewriting it to NIL is a lot nicer.
  ;;
  ;; (defthm sfix-empty-same
  ;;   (implies (and (empty X)
  ;;                 (empty Y))
  ;;            (equal (equal (sfix X) (sfix Y))
  ;;                   t)))

  (defthm sfix-when-empty
    (implies (empty X)
             (equal (sfix X)
                    nil))))


(defthm empty-sfix-cancel
  (equal (empty (sfix X))
         (empty X)))

(xdoc::xdoc-extend empty "@(def empty-sfix-cancel)")



(defsection head
  :parents (primitives)
  :short "@(call head) returns the smallest element in a set."

  :long "<p>This is like @(see car), but respects the non-set convention and
always returns @('nil') for ill-formed sets.</p>"

  (defun head (X)
    (declare (xargs :guard (and (setp X)
                                (not (empty X)))))
    (mbe :logic (car (sfix X))
         :exec  (car X)))

  (defthm head-count
    (implies (not (empty X))
             (< (acl2-count (head X)) (acl2-count X)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm head-count-built-in
    ;; BOZO probably should remove this
    (implies (not (empty X))
             (o< (acl2-count (head X)) (acl2-count X)))
    :rule-classes :built-in-clause)

  ;; I historically did this instead of head-when-empty, but now I think just
  ;; rewriting it to NIL is a lot nicer.
  ;;
  ;; (defthm head-empty-same
  ;;   (implies (and (empty X)
  ;;                 (empty Y))
  ;;            (equal (equal (head X) (head Y))
  ;;                   t)))

  (defthm head-when-empty
    (implies (empty X)
             (equal (head X)
                    nil)))

  (defthm head-sfix-cancel
    (equal (head (sfix X))
           (head X))))



(defsection tail
  :parents (primitives)
  :short "@(call tail) returns the remainder of a set after removing its @(see
head)."

  :long "<p>This is like @(see cdr), but respects the non-set convention and
always returns @('nil') for ill-formed sets.</p>"

  (defun tail (X)
    (declare (xargs :guard (and (setp X)
                                (not (empty X)))))
    (mbe :logic (cdr (sfix X))
         :exec  (cdr X)))

  (defthm tail-count
    (implies (not (empty X))
             (< (acl2-count (tail X)) (acl2-count X)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm tail-count-built-in
    ;; BOZO probably should remove this
    (implies (not (empty X))
             (o< (acl2-count (tail X)) (acl2-count X)))
    :rule-classes :built-in-clause)

  (defthm tail-produces-set
    (setp (tail X)))

  ;; I historically did this instead of tail-when-empty, but now I think just
  ;; rewriting it to NIL is a lot nicer.
  ;;
  ;; (defthm tail-empty-same
  ;;   (implies (and (empty X)
  ;;                 (empty Y))
  ;;            (equal (equal (tail X) (tail Y))
  ;;                   t)))

  ;; This was also subsumed by tail-when-empty:
  ;;
  ;; (defthm tail-preserves-empty
  ;;   (implies (empty X)
  ;;            (empty (tail X))))

  (defthm tail-when-empty
    (implies (empty X)
             (equal (tail X)
                    nil)))

  (defthm tail-sfix-cancel
    (equal (tail (sfix X))
           (tail X))))


(defthmd head-tail-same
  ;; BOZO probably expensive
  (implies (and (equal (head X) (head Y))
                (equal (tail X) (tail Y))
                (not (empty X))
                (not (empty Y)))
           (equal (equal X Y)
                  t)))

(defsection insert
  :parents (primitives)
  :short "@(call insert) adds the element @('a') to the set @('X')."

  :long "<p>This is the fundamental set constructor.  It is similar to @(see
cons) for lists, but of course performs an ordered insertion.  It respects the
non-set convention and treats any ill-formed input as the empty set.</p>

<p>Efficiency note.  Insert is @('O(n)').  It is very inefficient to call it
repeatedly.  Instead, consider building sets with @(see mergesort) or out of
other sets using @(see union).</p>

<p>The :exec version just inlines the set primitives and does one level of loop
unrolling.  On CCL, it runs about 1.65x faster than the :logic version on the
following loop:</p>

@({
 ;; 1.92 seconds :logic, 1.16 seconds :exec
 (let ((acc nil))
  (gc$)
  (time$ (loop for i fixnum from 1 to 10000 do
               (setq acc (set::insert i acc)))))
})"

  (local (in-theory (disable nonempty-means-set
                             empty-set-unique
                             head-when-empty
                             tail-when-empty
                             sfix-when-empty
                             default-car
                             default-cdr
                             )))

  (defun insert (a X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (mbe :logic
         (cond ((empty X) (list a))
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

  (verify-guards insert
    :hints(("Goal" :in-theory (e/d (<<)
                                   (<<-trichotomy
                                    <<-implies-lexorder)))))

  (defthm insert-produces-set
    (setp (insert a X)))

  (defthm insert-sfix-cancel
    (equal (insert a (sfix X))
           (insert a X)))

  (defthm insert-never-empty
    (not (empty (insert a X))))

  ;; I historically did this instead of insert-when-empty, but now I think that
  ;; canonicalizing bad inserts into (insert a NIL) seems nicer.
  ;;
  ;; (defthm insert-empty-same
  ;;   (implies (and (empty X)
  ;;                 (empty Y))
  ;;            (equal (equal (insert a X) (insert a Y))
  ;;                   t)))

  ;; The following also became unnecessary after switching to (insert a NIL).
  ;;
  ;; (defthm head-insert-empty
  ;;   (implies (empty X)
  ;;            (equal (head (insert a X)) a)))
  ;;
  ;; (defthm tail-insert-empty
  ;;   (implies (empty X)
  ;;  	      (empty (tail (insert a X)))))

  (defthm insert-when-empty
    (implies (and (syntaxp (not (equal X ''nil)))
                  (empty X))
             (equal (insert a X)
                    (insert a nil))))

  ;; These special cases can come up after insert-when-empty applies, so it's
  ;; nice to have rules to target them.

  (defthm head-of-insert-a-nil
    (equal (head (insert a nil))
           a))

  (defthm tail-of-insert-a-nil
    (equal (tail (insert a nil))
           nil))

  ;; Historic Note: We used to require that nil was "greater than" everything else
  ;; in our order.  This had the advantage that the following theorems could have
  ;; a combined case for (empty X) and (<< a (head X)).  Starting in Version 0.9,
  ;; we remove this restriction in order to be more flexible about our order.

  (defthm head-insert
    (equal (head (insert a X))
           (cond ((empty X) a)
                 ((<< a (head X)) a)
                 (t (head X)))))

  (defthm tail-insert
    (equal (tail (insert a X))
           (cond ((empty X) (sfix X))
                 ((<< a (head X)) (sfix X))
                 ((equal a (head X)) (tail X))
                 (t (insert a (tail X))))))

  (encapsulate
    ()
    (local (defthm l0
             (IMPLIES (AND (NOT (<< ACL2::Y ACL2::X))
                           (NOT (EQUAL ACL2::X ACL2::Y)))
                      (<< ACL2::X ACL2::Y))
             :rule-classes ((:rewrite :backchain-limit-lst 0))))

    (local (defthm l1
             (IMPLIES (<< x y)
                      (not (<< y x)))
             :rule-classes ((:rewrite :backchain-limit-lst 0))))

    (local (in-theory (disable sfix-set-identity
                               insert-when-empty
                               (:definition insert)
                               <<-trichotomy
                               <<-asymmetric)))

    (local (defthm l2
             (implies (and (<< b (car x))
                           (setp x))
                      (equal (cons b (insert (car x) x))
                             (insert b (insert (car x) x))))
             :rule-classes ((:rewrite :backchain-limit-lst 0))
             :hints(("Goal" :expand ((:free (x) (insert b x)))))))

    (local (defthm l3
             (implies (and (<< b (car l))
                           (not (equal b a))
                           (not (<< a b)))
                      (<< b (car (insert a l))))
             :rule-classes ((:rewrite :backchain-limit-lst 0))
             :hints(("goal" :expand (insert a l)))))

    (local (in-theory (disable head-insert
                               tail-insert)))

    (defthm repeated-insert
      (equal (insert a (insert a X))
             (insert a X))
      :hints(("Goal"
              :induct t
              :expand ((insert a nil)
                       (insert a x)
                       (insert (car x) x)
                       (:free (k1 k2) (insert a (cons k1 k2)))))))

    (defthm insert-insert
      (equal (insert a (insert b X))
             (insert b (insert a X)))
      :rule-classes ((:rewrite :loop-stopper ((a b))))
      :hints(("Goal"
              :induct t
              :expand ((insert a x)
                       (insert b x)
                       (:free (k1) (insert k1 nil))
                       (:free (k1 k2 k3) (insert k1 (cons k2 k3))))))))

  (defthm insert-head
    (implies (not (empty X))
             (equal (insert (head X) X)
                    X)))

  (defthm insert-head-tail
    (implies (not (empty X))
             (equal (insert (head X) (tail X))
                    X)))



  ;; Insert can be reasoned about in terms of induction, but its inductive case
  ;; contains a call to "cons", and we cannot let that escape into the wild.
  ;; Instead, we write a theorem to rephrase this cons into an insert.

  (defthm insert-induction-case
    (implies (and (not (<< a (head X)))
                  (not (equal a (head X)))
                  (not (empty X)))
             (equal (insert (head X) (insert a (tail X)))
                    (insert a X)))))



;; The last thing we really need to do is reason about element order.  The
;; following theorems are crucial for proofs in the membership level, which
;; must stricly use induction and arguments about the set elements' order for
;; proofs.  Since we are disabling all of the functions at the end of this
;; book, these are the only facts which membership.lisp will be able to use.

(defthm head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthm head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

(defthm head-not-head-tail
  (implies (not (empty (tail X)))
           (not (equal (head X) (head (tail X))))))



; And that concludes the theorems we need about the primitive set functions.
; Now we are interested in setting up theories and in disabling most of the
; potentially bad issues that might arise.
;
; You should never need to use primitive-theory unless you are using non-set
; functions, e.g. cons, to build sets.
;
; The primitive order theory is intended to be disabled for typical reasoning,
; but is needed for some theorems in the membership level.

(def-ruleset primitive-rules
  '(setp empty head tail sfix insert))

(def-ruleset order-rules
  '(<<-irreflexive
    <<-transitive
    <<-asymmetric
    <<-trichotomy
    <<-implies-lexorder
    (:induction insert)
    insert-induction-case
    head-insert
    tail-insert
    head-tail-order
    head-tail-order-contrapositive))

(in-theory (disable (:ruleset primitive-rules)
                    (:ruleset order-rules)))
