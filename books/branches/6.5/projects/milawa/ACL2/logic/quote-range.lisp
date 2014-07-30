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
(include-book "groundp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Walk through a map, quoting every element in the range.

(defund logic.quote-range (x)
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (cons (car (car x))
                  (list 'quote (cdr (car x))))
            (logic.quote-range (cdr x)))
    nil))

(defthm logic.quote-range-when-not-consp
  (implies (not (consp x))
           (equal (logic.quote-range x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.quote-range))))

(defthm logic.quote-range-of-cons
  (equal (logic.quote-range (cons a x))
         (cons (cons (car a) (list 'quote (cdr a)))
               (logic.quote-range x)))
  :hints(("Goal" :in-theory (enable logic.quote-range))))

(defthm true-listp-of-logic.quote-range
  (equal (true-listp (logic.quote-range x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.quote-range-of-list-fix
  (equal (logic.quote-range (list-fix x))
         (logic.quote-range x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-logic.quote-range
  (equal (len (logic.quote-range x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.quote-range-of-app
  (equal (logic.quote-range (app x y))
         (app (logic.quote-range x)
              (logic.quote-range y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.sigmap-of-logic.quote-range
  (implies (force (logic.sigmap x))
           (equal (logic.sigmap (logic.quote-range x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.sigma-atblp-of-logic.quote-range
  (implies (force (logic.variable-listp (domain sigma)))
           (equal (logic.sigma-atblp (logic.quote-range sigma) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction sigma))))

(defthm forcing-logic.constant-listp-of-range-of-logic.quote-range
  (implies (force (logic.sigmap x))
           (equal (logic.constant-listp (range (logic.quote-range x)))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.ground-listp-of-range-of-logic.quote-range
  (implies (force (logic.sigmap x))
           (equal (logic.ground-listp (range (logic.quote-range x)))
                  t)))

(defthm forcing-domain-of-logic.quote-range
  (equal (domain (logic.quote-range x))
         (domain x))
  :hints(("Goal" :induct (cdr-induction x))))

