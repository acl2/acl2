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
(include-book "substitute-formula")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; We sometimes think of a term, A, as if it were the formula A != nil.  We now
;; provide some functions to transform terms into these formulas.


(definlined logic.term-formula (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.pnot (logic.pequal x ''nil)))

(defthm forcing-logic.formulap-of-logic.term-formula
  (implies (force (logic.termp x))
           (equal (logic.formulap (logic.term-formula x))
                  t))
  :hints(("Goal" :in-theory (enable logic.term-formula))))

(defthm forcing-logic.formula-atblp-of-logic.term-formula
  (implies (force (logic.term-atblp x atbl))
           (equal (logic.formula-atblp (logic.term-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.term-formula))))

(defthm logic.substitute-formula-of-logic.term-formula
  (equal (logic.substitute-formula (logic.term-formula x) sigma)
         (logic.term-formula (logic.substitute x sigma)))
  :hints(("Goal" :in-theory (enable logic.term-formula))))




(defprojection :list (logic.term-list-formulas x)
               :element (logic.term-formula x)
               :guard (logic.term-listp x))

(defthmd redefinition-of-logic.term-list-formulas
  (equal (logic.term-list-formulas x)
         (logic.negate-formulas (logic.pequal-list x (repeat ''nil (len x)))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))

(defthm forcing-logic.formula-listp-of-logic.term-list-formulas
  (implies (force (logic.term-listp x))
           (equal (logic.formula-listp (logic.term-list-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-logic.term-list-formulas
  (implies (force (logic.term-list-atblp x atbl))
           (equal (logic.formula-list-atblp (logic.term-list-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-logic.term-formula-and-logic.term-list-formulas
  (equal (memberp (logic.term-formula a) (logic.term-list-formulas x))
         (memberp a x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))

(defthm memberp-of-logic.pnot-of-logic.pequal-nil-in-logic.term-list-formulas
  (equal (memberp (logic.pnot (logic.pequal a ''nil)) (logic.term-list-formulas x))
         (memberp a x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))

(defthm subsetp-of-logic.term-list-formulas-and-logic.term-list-formulas
  (equal (subsetp (logic.term-list-formulas x) (logic.term-list-formulas y))
         (subsetp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-of-logic.term-list-formulas
  (equal (logic.substitute-formula-list (logic.term-list-formulas x) sigma)
         (logic.term-list-formulas (logic.substitute-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection :list (logic.term-list-list-formulas x)
               :element (logic.term-list-formulas x)
               :guard (logic.term-list-listp x))

(defthm forcing-logic.formula-list-listp-of-logic.term-list-list-formulas
  (implies (force (logic.term-list-listp x))
           (equal (logic.formula-list-listp (logic.term-list-list-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-list-atblp-of-logic.term-list-list-formulas
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (logic.formula-list-list-atblp (logic.term-list-list-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-logic.term-list-list-formulas
  (equal (cons-listp (logic.term-list-list-formulas x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm supserset-of-somep-of-logic.term-list-formulas-and-logic.term-list-list-formulas
  (equal (superset-of-somep (logic.term-list-formulas a) (logic.term-list-list-formulas x))
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-logic.term-list-list-formulas
  (equal (all-superset-of-somep (logic.term-list-list-formulas x) (logic.term-list-list-formulas y))
         (all-superset-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-list-formulas-of-list-list-fix
  (equal (logic.term-list-list-formulas (list-list-fix x))
         (logic.term-list-list-formulas x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-list-of-logic.term-list-list-formulas
  (equal (logic.substitute-formula-list-list (logic.term-list-list-formulas x) sigma)
         (logic.term-list-list-formulas (logic.substitute-list-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-list-formulas-of-listify-each
  (implies (force (logic.term-listp x))
           (equal (logic.term-list-list-formulas (listify-each x))
                  (listify-each (logic.negate-formulas (logic.pequal-list x (repeat ''nil (len x)))))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))
