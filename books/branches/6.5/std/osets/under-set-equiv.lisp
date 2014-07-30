; Fully Ordered Finite Sets
; Copyright (C) 2003-2013 Kookamara LLC
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

(in-package "SET")
(include-book "outer")
(include-book "sort")
(include-book "std/lists/sets" :dir :system)

(defun all-list (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      t
    (and (predicate (car x))
         (all-list (cdr x)))))

(encapsulate
  (((all-list-hyps) => *)
   ((all-list-list) => *))

  (local (defun all-list-hyps () nil))
  (local (defun all-list-list () nil))

  (defthmd list-membership-constraint
    (implies (all-list-hyps)
             (implies (member arbitrary-element (all-list-list))
                      (predicate arbitrary-element)))))

(encapsulate
  ()
  (local (defun all-list-badguy (x)
           (if (consp x)
               (if (predicate (car x))
                   (all-list-badguy (cdr x))
                 (list (car x)))
             nil)))

  (local (defthmd all-list-badguy-membership-property
           (implies (all-list-badguy x)
                    (and (member-equal (car (all-list-badguy x)) x)
                         (not (predicate (car (all-list-badguy x))))))
           :hints(("Goal" :induct (all-list-badguy x)))))

  (local (defthm all-list-badguy-under-iff
           (iff (all-list-badguy x)
                (not (all-list x)))
           :hints(("Goal" :in-theory (enable all-list)))))

  (defthmd all-list-by-membership
    (implies (all-list-hyps)
             (all-list (all-list-list)))
    :hints(("Goal"
            :in-theory (enable list-membership-constraint)
            :use ((:instance all-list-badguy-membership-property
                             (x (all-list-list))))))))

(defund subsetp-equal-trigger (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (subsetp-equal x y))

(defthm pick-a-point-subsetp-equal-strategy
  (implies (and (syntaxp (rewriting-goal-lit mfc state))
                (syntaxp (rewriting-conc-lit `(subsetp-equal ,x ,y) mfc state)))
           (equal (subsetp-equal x y)
                  (subsetp-equal-trigger x y)))
  :hints(("Goal" :in-theory (enable subsetp-equal-trigger))))

(COMPUTED-HINTS::automate-instantiation
 :new-hint-name pick-a-point-subsetp-equal-hint
 :generic-theorem all-list-by-membership
 :generic-predicate predicate
 :generic-hyps all-list-hyps
 :generic-collection all-list-list
 :generic-collection-predicate all-list
 :actual-collection-predicate subsetp-equal
 :actual-trigger subsetp-equal-trigger
 :predicate-rewrite (((predicate ?x ?y) (member-equal ?x ?y)))
 :tagging-theorem pick-a-point-subsetp-equal-strategy)



;; BOZO talk to sol about whether these should become defwitness nonsense

(local (defthm promote-member-to-in
         (implies (setp x)
                  (iff (member a x)
                       (in a x)))
         :hints(("Goal" :in-theory (enable in-to-member)))))

(local (in-theory (enable acl2::set-equiv)))

(defthm insert-under-set-equiv
  (acl2::set-equiv (insert a x)
                   (cons a (sfix x)))
  :hints(("Goal" :do-not-induct t)))

(defthm delete-under-set-equiv
  (acl2::set-equiv (delete a x)
                   (remove-equal a (sfix x))))

(encapsulate
  ()
  (local (defthm l0
           (subsetp (union x y)
                    (append (sfix x) (sfix y)))))

  (local (defthm l1
           (subsetp (append (sfix x) (sfix y))
                    (union x y))))

  (defthm union-under-set-equiv
    (acl2::set-equiv (union x y)
                     (append (sfix x) (sfix y)))
    :hints(("Goal" :do-not-induct t))))


(defthm intersect-under-set-equiv
  (acl2::set-equiv (intersect x y)
                   (intersection-equal (sfix x) (sfix y)))
  :hints(("Goal" :do-not-induct t)))

(defthm difference-under-set-equiv
  (acl2::set-equiv (difference x y)
                   (set-difference-equal (sfix x) (sfix y)))
  :hints(("Goal" :do-not-induct t)))

(defthm mergesort-under-set-equiv
  (acl2::set-equiv (mergesort x)
                   x)
  :hints(("Goal" :do-not-induct t)))

(encapsulate
  ()
  (local (defthm l0
           (implies (acl2::set-equiv x y)
                    (subsetp (mergesort x) (mergesort y)))))

  (local (defthm l1
           (implies (and (subsetp x y)
                         (member a x))
                    (member a y))))

  (defcong acl2::set-equiv equal (mergesort x) 1
    :event-name set-equiv-implies-equal-mergesort-1
    :hints(("Goal"
            :do-not-induct t
            :do-not '(generalize fertilize)
            :in-theory (enable acl2::set-equiv)))))



