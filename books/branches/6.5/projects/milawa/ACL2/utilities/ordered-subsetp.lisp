; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "MILAWA")
(include-book "utilities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; We say that x is an ordered subset of y when every member of x is also a
;; member of y, and the elements occur in the same order in x and y.

(defund ordered-subsetp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (if (equal (car x) (car y))
               (ordered-subsetp (cdr x) (cdr y))
             (ordered-subsetp x (cdr y))))
    t))

(defthm ordered-subsetp-when-not-consp-one
  (implies (not (consp x))
           (equal (ordered-subsetp x y)
                  t))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-when-not-consp-two
  (implies (not (consp y))
           (equal (ordered-subsetp x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-cons-and-cons
  (equal (ordered-subsetp (cons a x) (cons b y))
         (if (equal a b)
             (ordered-subsetp x y)
           (ordered-subsetp (cons a x) y)))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm booleanp-of-ordered-subsetp
  (equal (booleanp (ordered-subsetp x y))
         t)
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(encapsulate
 ()
 (local (defun my-induction (x y)
          (declare (xargs :export nil))
          (if (and (consp x)
                   (consp y))
              (list (my-induction x (cdr y))
                    (my-induction (cdr x) (cdr y)))
            nil)))

 (defthm ordered-subsetp-of-cdr-when-ordered-subsetp
   (implies (ordered-subsetp x y)
            (equal (ordered-subsetp (cdr x) y)
                   t))
   :hints(("Goal" :induct (my-induction x y)))))

(defthm ordered-subsetp-when-ordered-subsetp-of-cons
  (implies (ordered-subsetp (cons a x) y)
           (equal (ordered-subsetp x y)
                  t))
  :hints(("Goal" :use ((:instance ordered-subsetp-of-cdr-when-ordered-subsetp
                                  (x (cons a x))
                                  (y y))))))

(defthm ordered-subsetp-of-cons-when-ordered-subsetp
  (implies (ordered-subsetp x y)
           (equal (ordered-subsetp x (cons a y))
                  t))
  :hints(("Goal" :expand (ordered-subsetp x (cons a y)))))

(defthm ordered-subsetp-when-ordered-subsetp-of-cdr
  (implies (ordered-subsetp x (cdr y))
           (equal (ordered-subsetp x y)
                  t)))

(defthm ordered-subsetp-is-reflexive
  (equal (ordered-subsetp x x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(encapsulate
 ()
 (local (defun my-induction (x y z)
          (declare (xargs :measure (+ (rank x) (+ (rank y) (rank z)))
                          :export nil))
          (if (and (consp x)
                   (consp y)
                   (consp z))
              (list (my-induction (cdr x) (cdr y) (cdr z))
                    (my-induction (cdr x) (cdr y) z)
                    (my-induction x (cdr y) (cdr z))
                    (my-induction x y (cdr z)))
            nil)))

 (defthm ordered-subsetp-is-transitive
   (implies (and (ordered-subsetp x y)
                 (ordered-subsetp y z))
            (equal (ordered-subsetp x z)
                   t))
   :hints(("Goal" :induct (my-induction x y z)))))

(defthm ordered-subsetp-of-list-fix-one
  (equal (ordered-subsetp (list-fix x) y)
         (ordered-subsetp x y))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-list-fix-two
  (equal (ordered-subsetp x (list-fix y))
         (ordered-subsetp x y))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-app-when-ordered-subsetp-one
  (implies (ordered-subsetp x y)
           (ordered-subsetp x (app y z)))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-app-one
  (equal (ordered-subsetp x (app x y))
         t))

(defthm ordered-subsetp-of-app-two
  (equal (ordered-subsetp x (app y x))
         t)
  :hints(("Goal" :induct (cdr-induction y))))

(defthm ordered-subsetp-of-app-when-ordered-subsetp-two
  (implies (ordered-subsetp x y)
           (ordered-subsetp x (app z y)))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm subsetp-when-ordered-subsetp
  (implies (ordered-subsetp x y)
           (equal (subsetp x y)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-remove-duplicates
  (equal (ordered-subsetp (remove-duplicates x) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordered-subsetp-of-remove-all
  (equal (ordered-subsetp (remove-all a x) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordered-subsetp-of-difference
  (equal (ordered-subsetp (difference x y) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

