; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/util/define" :dir :system)
(local (include-book "arithmetic"))


; Extended lemmas about intersectp-equal

(define empty-intersect-with-each-p ((a "A list")
                                     (x "A list of lists"))
  :verify-guards nil
  (or (atom x)
      (and (not (intersectp-equal a (car x)))
           (empty-intersect-with-each-p a (cdr x))))
  :parents (utilities)
  :short "@(call empty-intersect-with-each-p) checks whether @('a') is disjoint
from every member of @('x')."

  ///

  (defthm empty-intersect-with-each-p-when-atom
    (implies (atom x)
             (empty-intersect-with-each-p a x)))

  (defthm empty-intersect-with-each-p-of-cons
    (equal (empty-intersect-with-each-p a (cons b x))
           (and (not (intersectp-equal a b))
                (empty-intersect-with-each-p a x))))

  (defthm empty-intersect-with-each-p-of-cdr
    (implies (empty-intersect-with-each-p a x)
             (empty-intersect-with-each-p a (cdr x))))

  (defthm intersectp-equal-when-empty-intersect-with-each-p
    (implies (and (empty-intersect-with-each-p a x)
                  (member-equal b x))
             (equal (intersectp-equal a b)
                    nil))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (implies (and (member-equal b x)
                                           (empty-intersect-with-each-p a x))
                                      (equal (intersectp-equal a b)
                                             nil)))
                   (:rewrite :corollary
                             (implies (and (empty-intersect-with-each-p a x)
                                           (member-equal b x))
                                      (equal (intersectp-equal b a)
                                             nil)))
                   (:rewrite :corollary
                             (implies (and (member-equal b x)
                                           (empty-intersect-with-each-p a x))
                                      (equal (intersectp-equal b a)
                                             nil)))))

  (defthm empty-intersect-flatten-when-empty-intersect-with-each-p
    (implies (empty-intersect-with-each-p a x)
             (not (intersectp-equal a (flatten x))))))



; EMPTY-INTERSECT-BY-MEMBERSHIP
;
;   Functionally instantiate this to prove that (intersectp-equal x y) is NIL
;   because there are no common members of X and Y.

(encapsulate
  (((empty-intersect-hyp) => *)
   ((empty-intersect-lhs) => *)
   ((empty-intersect-rhs) => *))
  (local (defun empty-intersect-hyp () t))
  (local (defun empty-intersect-lhs () nil))
  (local (defun empty-intersect-rhs () nil))
  (defthm empty-intersect-by-membership-constraint
    (implies (empty-intersect-hyp)
             (not (and (member-equal a (empty-intersect-lhs))
                       (member-equal a (empty-intersect-rhs)))))
    :rule-classes nil))

(defsection empty-intersect-by-membership

  (local (defun badguy (x y)
           (cond ((atom x)
                  nil)
                 ((member-equal (car x) y)
                  (list (car x)))
                 (t
                  (badguy (cdr x) y)))))

  (local (defthm l0
           (equal (intersectp-equal x y)
                  (if (badguy x y)
                      t
                    nil))))

  (local (defthm l1
           (implies (and (member-equal a x)
                         (member-equal a y))
                    (badguy x y))))

  (local (defthm l2
           (implies (badguy x y)
                    (and (member-equal (car (badguy x y)) x)
                         (member-equal (car (badguy x y)) y)))))

  (defthm empty-intersect-by-membership
    (implies (empty-intersect-hyp)
             (not (intersectp-equal (empty-intersect-lhs)
                                    (empty-intersect-rhs))))
    :hints(("Goal"
            :use ((:instance empty-intersect-by-membership-constraint
                             (a (car (badguy (empty-intersect-lhs)
                                             (empty-intersect-rhs))))))))))



(defthm empty-intersect-of-subsets-when-empty-intersect
  (implies (and (not (intersectp-equal x y))
                (subsetp-equal a x)
                (subsetp-equal b y))
           (not (intersectp-equal a b)))
  :hints(("Goal"
          :use ((:functional-instance
                 empty-intersect-by-membership
                 (empty-intersect-hyp
                  (lambda () (and (not (intersectp-equal x y))
                                  (subsetp-equal a x)
                                  (subsetp-equal b y))))
                 (empty-intersect-lhs (lambda () a))
                 (empty-intersect-rhs (lambda () b))))

; Matt K. mod, 1/28/2017, to accommodate fix for soundness bug in functional
; instantiation:

          :in-theory (enable acl2::intersectp-member)
          :restrict ((acl2::intersectp-member ((acl2::a a-renamed0)))))))



(local (defun find-intersect1 (a x)
         ;; A is a list, X is a list of lists.
         (cond ((atom x)
                nil)
               ((intersectp-equal a (car x))
                (car x))
               (t
                (find-intersect1 a (cdr x))))))

(local (defthm find-intersect1-sound
         (implies (find-intersect1 a x)
                  (and (intersectp-equal a (find-intersect1 a x))
                       (member-equal (find-intersect1 a x) x)))))

(local (defthm find-intersect1-complete
         (implies (and (not (find-intersect1 a x))
                       (member-equal b x))
                  (not (intersectp-equal a b)))))

(local (defthm find-intersect1-when-atom
         (implies (atom a)
                  (not (find-intersect1 a x)))))

(local (defthm find-intersect1-consequence-for-flatten
         (implies (not (find-intersect1 a x))
                  (not (intersectp-equal a (flatten x))))))




; EMPTY-INTERSECT-OF-FLATTEN
;
;   Functionally instantiate this to prove that:
;
;      (intersectp-equal A (FLATTEN X))
;
;   Is NIL because A does not intersect with any member of X.

(encapsulate
  (((intersect-flatten-hyp) => *)
   ((intersect-flatten-lhs) => *)
   ((intersect-flatten-rhs) => *))
  (local (defun intersect-flatten-hyp () t))
  (local (defun intersect-flatten-lhs () t))
  (local (defun intersect-flatten-rhs () t))
  (defthmd empty-intersect-of-flatten-constraint
    (implies (and (intersect-flatten-hyp)
                  (member-equal a (intersect-flatten-rhs)))
             (not (intersectp-equal (intersect-flatten-lhs) a)))))

(defthm empty-intersect-of-flatten
  (implies (intersect-flatten-hyp)
           (not (intersectp-equal (intersect-flatten-lhs)
                                  (flatten (intersect-flatten-rhs)))))
  :hints(("Goal"
          :in-theory (disable find-intersect1-consequence-for-flatten)
          :use ((:instance find-intersect1-consequence-for-flatten
                           (a (intersect-flatten-lhs))
                           (x (intersect-flatten-rhs)))
                (:instance empty-intersect-of-flatten-constraint
                           (a (find-intersect1 (intersect-flatten-lhs)
                                               (intersect-flatten-rhs))))))))




(local (defun find-intersect2 (x y)
         ;; X and Y are lists of lists
         (cond ((atom x)
                nil)
               ((find-intersect1 (car x) y)
                (car x))
               (t
                (find-intersect2 (cdr x) y)))))

(local (defthm find-intersect2-sound
         (implies (find-intersect2 x y)
                  (let* ((a (find-intersect2 x y))
                         (b (find-intersect1 a y)))
                    (and (member-equal a x)
                         (member-equal b y)
                         (intersectp-equal a b))))))

(local (defthm find-intersect2-complete
         (implies (and (not (find-intersect2 x y))
                       (member-equal a x)
                       (member-equal b y))
                  (not (intersectp-equal a b)))
         :hints(("Goal" :do-not '(generalize fertilize)))))

(local (defthm find-intersect2-consequence-for-flatten
         (implies (not (find-intersect2 x y))
                  (not (intersectp-equal (flatten x) (flatten y))))
         :hints(("Goal"
                 :in-theory (enable flatten)
                 :induct (len x)))))





; EMPTY-INTERSECT-OF-TWO-FLATTENS
;
;   Functionally instantiate this to prove that:
;
;      (intersectp-equal (flatten X) (flatten Y))
;
;   Is NIL because no member of X intersects with any member of Y.

(encapsulate
  (((intersect-2flatten-hyp) => *)
   ((intersect-2flatten-lhs) => *)
   ((intersect-2flatten-rhs) => *))
  (local (defun intersect-2flatten-hyp () t))
  (local (defun intersect-2flatten-lhs () t))
  (local (defun intersect-2flatten-rhs () t))
  (defthmd empty-intersect-of-two-flattens-constraint
    (implies (and (intersect-2flatten-hyp)
                  (member-equal a (intersect-2flatten-lhs))
                  (member-equal b (intersect-2flatten-rhs)))
             (not (intersectp-equal a b)))))

(defthm empty-intersect-of-two-flattens
  (implies (intersect-2flatten-hyp)
           (not (intersectp-equal (flatten (intersect-2flatten-lhs))
                                  (flatten (intersect-2flatten-rhs)))))
  :hints(("Goal"
          :in-theory (disable find-intersect2-consequence-for-flatten)
          :use ((:instance find-intersect2-consequence-for-flatten
                           (x (intersect-2flatten-lhs))
                           (y (intersect-2flatten-rhs)))
                (:instance empty-intersect-of-two-flattens-constraint
                           (a (find-intersect2 (intersect-2flatten-lhs)
                                               (intersect-2flatten-rhs)))
                           (b (find-intersect1
                               (find-intersect2 (intersect-2flatten-lhs)
                                                (intersect-2flatten-rhs))
                               (intersect-2flatten-rhs))))))))
