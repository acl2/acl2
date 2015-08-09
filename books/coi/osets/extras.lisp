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

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(in-package "SET")

(include-book "sets")
(include-book "set-order")
(include-book "conversions")
(include-book "../util/iff")

(include-book "misc/total-order" :dir :system) ;was is this not included by set-order?

(defthmd open-set2list
  (implies
   (not (empty set))
   (equal (2list set)
          (CONS (HEAD SET)
                (|2LIST| (TAIL SET))))))


(defthmd in-implications
  (implies
   (and
    (not (empty set))
    (in a set)
    (not (equal (head set) a)))
   (acl2::<< (head set) a))
  :hints (("Subgoal *1/4" :use (:instance
                                HEAD-TAIL-ORDER
                                (acl2::x set)))
          ("Subgoal *1/3" :use (:instance
                                HEAD-TAIL-ORDER
                                (acl2::x set)))))

(defthmd head-is-least-element
  (implies
   (and
    (not (empty set))
    (in a (tail set)))
   (acl2::<< (head set) a))
  :hints (("goal" :use in-implications)))

(defthm ordering-over-subset
  (implies
   (and
    (not (empty set1))
    (not (empty set2))
    (subset set2 (tail set1)))
   (acl2::<< (head set1) (head set2)))
  :hints (("goal" :use (:instance head-is-least-element
                                  (a (head set2))
                                  (set set1)))))

(defthm head-of-insert-under-subset
  (implies
   (and
    ;(not (empty set2))
    (not (empty set1))
    (subset set2 (tail set1)))
   (equal (head (insert (head set1) set2))
          (head set1)))
  :hints (("goal" :in-theory (enable HEAD-INSERT))))

(defthm not-empty-setp
  (implies
   (and
    (setp set)
    (empty set))
   (not set))
  :rule-classes (:forward-chaining)
  :hints (("goal" :in-theory (enable setp empty))))

(defthm tail-of-insert-under-subset
  (implies
   (and
    (setp set2)
    (not (empty set1))
    (subset set2 (tail set1)))
   (equal (tail (insert (head set1) set2))
          set2))
  :hints (("goal" :in-theory (enable tail-INSERT))))

(defthm consp-of-insert
  (consp (insert a s))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable empty insert setp))))

;; ;bzo drop because we have consp-of-insert?
;; (defthm iff-of-insert
;;   (iff (insert a s)
;;        t)
;;   :hints (("Goal" :in-theory (enable empty insert setp))))


;these mix car/cdr and insert and perhaps that should never happen.  but it seems to in practice...

;or do we want to just turn (insert a nil) into (list nil), or perhaps a new function called singleton applied to a?
(defthm cdr-insert-nil
  (equal (cdr (insert a nil))
         nil)
  :hints (("Goal" :in-theory (enable insert))))

(defthm car-insert-nil
  (equal (car (insert a nil))
         a)
  :hints (("Goal" :in-theory (enable insert))))

;handle this better?
(defthm subset-singletons-hack
  (subset (list x) (insert x nil))
  :hints (("Goal" :expand ((insert x nil)))))

(defthm setp-of-singleton
  (setp (list x))
  :hints (("Goal" :expand ((setp (list x))))))

(defthm in-of-singleton-hack
  (in a (list a))
  :hints (("Goal" :in-theory (enable tail
                                     head
                                     empty)
           :expand ((in a (list a))))))

(defthm empty-when-setp-means-nil
  (implies (setp x)
           (equal (EMPTY x)
                  (equal x nil)))
  :hints (("Goal" :in-theory (enable EMPTY))))

;bzo expensive?
(defthm empty-implies-not-sfix
  (implies (empty set)
           (not (sfix set)))
  :hints (("Goal" :in-theory (enable sfix))))

(defthm union-iff
  (iff (union x y)
       (or (not (empty x))
           (not (empty y)))))

(defthmd delete-of-union-push-into-both
  (equal (DELETE A (UNION x y))
         (UNION (DELETE A x)
                     (DELETE A y))))

(theory-invariant (incompatible (:rewrite delete-of-union-push-into-both) (:rewrite UNION-DELETE-X )))
(theory-invariant (incompatible (:rewrite delete-of-union-push-into-both) (:rewrite UNION-DELETE-y )))

(defthm subset-of-two-unions
  (implies (and (subset x x2)
                (subset y y2))
           (subset (union x y)
                        (union x2 y2))))

(defthm delete-of-insert-both
  (equal (delete a (insert b x))
         (if (equal a b)
             (delete a x)
           (insert b (delete a x)))))

;expensive?
(defthm head-when-empty
  (implies (empty x)
           (equal (head x)
                  (emptyset)))
  :hints (("Goal" :in-theory (enable head))))

(defthm delete-equal-self
  (equal (equal s (delete a s))
         (and (setp s)
              (not (in a s)))))

;may be expensive?
;use a congruence?
;trying disabled, since this sort of takes us out of the set world

;; [jared] something like this is now in std/osets
;; (defthmd insert-when-empty
;;   (implies (empty x)
;;            (equal (insert a x)
;;                   (list a)))
;;   :hints (("Goal" :in-theory (enable insert))))

;this sort of keeps us in the sets world (emptyset is a macro for nil - does that count as being in the sets world?)
(defthm insert-when-empty-2
  (implies (and (syntaxp (not (equal x ''nil))) ;prevents loops
                (empty x))
           (equal (insert a x)
                  (insert a (emptyset))))
  :hints (("Goal" :in-theory (enable insert))))


(defthm head-of-singleton
  (equal (head (list a))
         a)
  :hints (("Goal" :in-theory (enable head))))

(defthm tail-of-singleton
  (equal (tail (list a))
         nil)
  :hints (("Goal" :in-theory (enable tail))))

(encapsulate
 ()
 (local
  (defthm hacka
    (implies (and (in a s1)
                  (not (in a s2))
                  (setp s1)
                  (setp s2))
             (implies (equal s1 (insert a s2))
                      (equal (delete a s1) s2)))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
             :in-theory (e/d ( ;subset
                              pick-a-point-subset-strategy) (delete in))))))

 (local
  (defthm fw
    (implies (and (in a s1)
                  (not (in a s2))
                  (setp s1)
                  (setp s2))
             (implies (equal (delete a s1) s2)
                      (equal s1 (insert a s2))))
    :rule-classes nil
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
             :in-theory (e/d ( ;subset
                              pick-a-point-subset-strategy) (delete in))))))

;bzo prove the other one.  which way do we want to go?
 (defthm delete-equal-becomes-insert-equal
   (implies (and (in a s1)
                 (not (in a s2))
                 (setp s1)
                 (setp s2))
            (equal (equal (delete a s1) s2)
                   (equal s1 (insert a s2))))
   :hints (("Goal" :use (:instance fw)))
   ))

(defthm tail-of-singleton2
  (equal (TAIL (INSERT A NIL))
         (emptyset))
  :hints (("Goal" :in-theory (enable INSERT))))

;disable?
(defthmd subset-of-delete-helper
  (implies (and (not (subset (delete a x) y))
                (setp y))
           (not (subset x (insert a y)))))

(defthm subset-of-delete
  (implies (and (setp x)
                (setp y))
           (equal (subset (delete a x) y)
                  (if (in a x)
                      (if (in a y)
                          (subset x (insert a y))
                        (subset x (insert a y)))
                    (subset x y))))
  :hints (("Goal" :in-theory (enable subset-of-delete-helper))))

(defthm subset-of-insert-when-subset
  (implies (subset x y)
           (subset x (insert a y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm not-empty-of-singleton
  (not (empty (list a)))
  :hints (("Goal" :in-theory (enable empty))))

;may be expensive?
(defthm subset-delete-irrel-cheap
  (implies (not (in a x))
           (equal (subset x (delete a y))
                  (subset x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthmd subset-delete-irrel
  (implies (not (in a x))
           (equal (subset x (delete a y))
                  (subset x y))))

;may be expensive?
(defthm subset-of-insert-irrel-cheap
  (implies (not (in a x))
           (equal (subset x (insert a y))
                  (subset x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthmd subset-of-insert-irrel
  (implies (not (in a x))
           (equal (subset x (insert a y))
                  (subset x y))))

(defthmd subset-of-singleton
  (equal (subset x (insert a nil))
         (or (empty x)
             ;(equal x (insert a nil))
             (and (equal a (head x)) ;rephrasing...
                  (empty (tail x))))))

;Maybe restrict double-containment to not fire if either argument is a singleton?
;(theory-invariant (incompatible (:rewrite subset-of-singleton) (:rewrite double-containment)))

;semed to be expensive.
(defthmd empty-of-delete-rewrite
  (equal (empty (delete a s))
         (or (empty s)
             (equal s (insert a (emptyset))))))

;; [jared] something like this is now in std/osets/top
;; (defthmd tail-when-empty
;;   (implies (empty set)
;;            (equal (tail set)
;;                   (emptyset)))
;;   :hints (("Goal" :in-theory (enable tail))))

(defthm tail-when-empty-cheap
  (implies (empty set)
           (equal (tail set)
                  (emptyset)))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable tail-when-empty))))

(defthm delete-head-of-self
  (equal (delete (head set) set)
         (tail set)))

(defthmd tail-when-not-setp
  (implies (not (setp s))
           (equal (tail s)
                  nil))
  :hints (("Goal" :in-theory (enable tail))))

(defthm tail-when-not-setp-cheap
  (implies (not (setp s))
           (equal (tail s)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable tail-when-not-setp))))

(defthm not-empty-when-something-in
  (implies (in a x) ;a is a free variable
           (not (empty x))))
