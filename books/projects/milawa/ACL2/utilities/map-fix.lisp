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
(include-book "cons-listp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; NOTE: this isn't actually included in top.lisp yet, because I don't want
;; to wait an hour for everything to recertify.

(defund map-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (cons-fix (car x))
            (map-fix (cdr x)))
    nil))

(defthm map-fix-when-not-consp
  (implies (not (consp x))
           (equal (map-fix x)
                  nil))
  :hints(("Goal" :in-theory (enable map-fix))))

(defthm map-fix-of-cons
  (equal (map-fix (cons a x))
         (cons (cons-fix a)
               (map-fix x)))
  :hints(("Goal" :in-theory (enable map-fix))))

(defthm map-fix-under-iff
  (iff (map-fix x)
       (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-map-fix
  (equal (consp (map-fix x))
         (consp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mapp-of-map-fix
  (equal (mapp (map-fix x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-map-fix
  (equal (true-listp (map-fix x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm map-fix-of-list-fix
  (equal (map-fix (list-fix x))
         (map-fix x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm map-fix-of-map-fix
  (equal (map-fix (map-fix x))
         (map-fix x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm map-fix-when-mapp
  (implies (mapp x)
           (equal (map-fix x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm map-fix-of-app
  (equal (map-fix (app x y))
         (app (map-fix x)
              (map-fix y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm map-fix-of-rev
  (equal (map-fix (rev x))
         (rev (map-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm lookup-of-map-fix
  (equal (lookup a (map-fix x))
         (lookup a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-map-fix
  (equal (domain (map-fix x))
         (domain x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm range-of-map-fix
  (equal (range (map-fix x))
         (range x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm submapp1-of-map-fix-left
  (equal (submapp1 domain (map-fix x) y)
         (submapp1 domain x y))
  :hints(("Goal" :induct (cdr-induction domain))))

(defthm submapp1-of-map-fix-right
  (equal (submapp1 domain x (map-fix y))
         (submapp1 domain x y))
  :hints(("Goal" :induct (cdr-induction domain))))

(defthm submapp-of-map-fix-left
  (equal (submapp (map-fix x) y)
         (submapp x y))
  :hints(("Goal" :in-theory (enable submapp))))

(defthm submapp-of-map-fix-right
  (equal (submapp (map-fix x) y)
         (submapp x y))
  :hints(("Goal" :in-theory (enable submapp))))

(defthm cons-listp-of-map-fix
  (equal (cons-listp (map-fix x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-map-fix-when-memberp
  (implies (memberp a x)
           (equal (memberp a (map-fix x))
                  (consp a)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-map-fix-when-subsetp
  (implies (subsetp x y)
           (equal (subsetp x (map-fix y))
                  (cons-listp x)))
  :hints(("Goal" :induct (cdr-induction x))))
