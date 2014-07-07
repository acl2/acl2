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
(include-book "deflist")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; (cons-onto-ranges a x)
;;
;; X is a map.  We produce a new map whose entries are (key . (a . value))
;; for every (key . value) pair in x.

;; BOZO tail recursive version?

;; BOZO more complete theory?

(defund cons-onto-ranges (a x)
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (cons (car (car x))
                  (cons a (cdr (car x))))
            (cons-onto-ranges a (cdr x)))
    nil))

(defthm cons-onto-ranges-when-not-consp
  (implies (not (consp x))
           (equal (cons-onto-ranges a x)
                  nil))
  :hints(("Goal" :in-theory (enable cons-onto-ranges))))

(defthm cons-onto-ranges-of-cons
  (equal (cons-onto-ranges a (cons b x))
         (cons (cons (car b) (cons a (cdr b)))
               (cons-onto-ranges a x)))
  :hints(("Goal" :in-theory (enable cons-onto-ranges))))

(defthm cons-onto-ranges-of-list-fix
  (equal (cons-onto-ranges a (list-fix x))
         (cons-onto-ranges a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-cons-onto-ranges
  (equal (true-listp (cons-onto-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-onto-ranges-of-app
  (equal (cons-onto-ranges a (app x y))
         (app (cons-onto-ranges a x)
              (cons-onto-ranges a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mapp-of-cons-onto-ranges
  (equal (mapp (cons-onto-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-cons-onto-ranges
  (equal (domain (cons-onto-ranges a x))
         (domain x))
  :hints(("Goal" :induct (cdr-induction x))))

