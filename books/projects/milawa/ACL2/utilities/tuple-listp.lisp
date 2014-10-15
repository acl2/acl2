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
(include-book "strip-firsts")
(include-book "strip-seconds")
(include-book "strip-lens")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; BOZO this doesn't really belong here
(deflist true-list-listp (x)
  (true-listp x)
  :elementp-of-nil t)



(deflist tuple-listp (n x)
  (tuplep n x)
  :guard (natp n))

(defthm rank-of-strip-firsts-when-tuple-listp-2
  (implies (and (tuple-listp 2 x)
                (consp x))
           (equal (< (rank (strip-firsts x)) (rank x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rank-of-strip-seconds-when-tuple-listp-2
  (implies (and (tuple-listp 2 x)
                (consp x))
           (equal (< (rank (strip-seconds x)) (rank x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm strip-lens-when-tuple-listp
  (implies (tuple-listp n x)
           (equal (strip-lens x)
                  (repeat (nfix n) (len x))))
  :hints(("Goal" :induct (cdr-induction x))))





(defund list2-list (x y)
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp y))
      (cons (list (car x) (car y))
            (list2-list (cdr x) (cdr y)))
    nil))

(defthm list2-list-when-not-consp-one
  (implies (not (consp x))
           (equal (list2-list x y)
                  nil))
  :hints(("Goal" :in-theory (enable list2-list))))

(defthm list2-list-when-not-consp-two
  (implies (not (consp y))
           (equal (list2-list x y)
                  nil))
  :hints(("Goal" :in-theory (enable list2-list))))

(defthm list2-list-of-cons-and-cons
  (equal (list2-list (cons a x) (cons b y))
         (cons (list a b)
               (list2-list x y)))
  :hints(("Goal" :in-theory (enable list2-list))))

(defthm true-listp-of-list2-list
  (equal (true-listp (list2-list x y))
         t)
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm true-listp-list-of-list2-list
  (equal (true-list-listp (list2-list x y))
         t)
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm list2-list-of-list-fix-one
  (equal (list2-list (list-fix x) y)
         (list2-list x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm list2-list-of-list-fix-two
  (equal (list2-list x (list-fix y))
         (list2-list x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm len-of-list2-list
  (equal (len (list2-list x y))
         (min (len x) (len y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm strip-lens-of-list2-list
  (equal (strip-lens (list2-list x y))
         (repeat 2 (min (len x) (len y))))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))


(defthm tuple-listp-of-list2-list
  (equal (tuple-listp n (list2-list x y))
         (or (not (consp x))
             (not (consp y))
             (equal n 2)))
  :hints(("Goal" :in-theory (enable list2-list)))) ;; yuck

(defthm forcing-strip-firsts-of-list2-list
  (implies (force (equal (len x) (len y)))
           (equal (strip-firsts (list2-list x y))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-strip-seconds-of-list2-list
  (implies (force (equal (len x) (len y)))
           (equal (strip-seconds (list2-list x y))
                  (list-fix y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))
