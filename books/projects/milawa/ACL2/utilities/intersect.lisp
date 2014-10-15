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

(defund intersect (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (memberp (car x) y)
          (cons (car x)
                (intersect (cdr x) y))
        (intersect (cdr x) y))
    nil))

(defthm intersect-when-not-consp-one
  (implies (not (consp x))
           (equal (intersect x y)
                  nil))
  :hints(("Goal" :in-theory (enable intersect))))

(defthm intersect-of-cons-one
  (equal (intersect (cons a x) y)
         (if (memberp a y)
             (cons a (intersect x y))
           (intersect x y)))
  :hints(("Goal" :in-theory (enable intersect))))

(defthm intersect-when-not-consp-two
  (implies (not (consp y))
           (equal (intersect x y)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-under-iff
  (iff (intersect x y)
       (not (disjointp x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-intersect
  (equal (true-listp (intersect x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-list-fix-one
  (equal (intersect (list-fix x) y)
         (intersect x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-list-fix-two
  (equal (intersect x (list-fix y))
         (intersect x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-app-one
  (equal (intersect (app x y) z)
         (app (intersect x z)
              (intersect y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-intersect
  (equal (rev (intersect x y))
         (intersect (rev x) y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-rev-two
  (equal (intersect x (rev y))
         (intersect x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-intersect-one
  (equal (subsetp (intersect x y) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-intersect-two
  (equal (subsetp (intersect x y) y)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-when-subsetp
  (implies (subsetp x y)
           (equal (intersect x y)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-with-self
  (equal (intersect x x)
         (list-fix x)))
