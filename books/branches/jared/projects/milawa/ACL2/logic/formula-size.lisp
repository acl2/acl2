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
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund logic.formula-size (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cond ((equal (car x) 'por*)
             (+ 1
                (+ (if (consp (cdr x))
                       (logic.formula-size (second x))
                     1)
                   (if (and (consp (cdr x))
                            (consp (cdr (cdr x))))
                       (logic.formula-size (third x))
                     1))))
            ((equal (car x) 'pnot*)
             (+ 1
                (if (consp (cdr x))
                    (logic.formula-size (second x))
                  1)))
            (t
             (+ 1
                (+ (if (consp (cdr x))
                       (logic.formula-size (second x))
                     1)
                   (if (and (consp (cdr x))
                            (consp (cdr (cdr x))))
                       (logic.formula-size (third x))
                     1)))))
    1))

(defthm natp-of-logic.formula-size
  (natp (logic.formula-size x))
  :hints(("Goal" :in-theory (e/d (logic.formula-size)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm logic.formula-size-nonzero
  (equal (equal (logic.formula-size x) 0)
         nil)
  :hints(("Goal" :in-theory (enable logic.formula-size))))

(defthm ordp-of-logic.formula-size
  (equal (ordp (logic.formula-size x))
         t))

(defthm forcing-logic.formula-size-of-logic.=lhs
  (implies (force (equal (logic.fmtype x) 'pequal*))
           (equal (< (logic.formula-size (logic.=lhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.=lhs))))

(defthm forcing-logic.formula-size-of-logic.=rhs
  (implies (force (equal (logic.fmtype x) 'pequal*))
           (equal (< (logic.formula-size (logic.=rhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.=rhs))))

(defthm forcing-logic.formula-size-of-logic.~arg
  (implies (force (equal (logic.fmtype x) 'pnot*))
           (equal (< (logic.formula-size (logic.~arg x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.~arg))))

(defthm forcing-logic.formula-size-of-logic.vlhs
  (implies (force (equal (logic.fmtype x) 'por*))
           (equal (< (logic.formula-size (logic.vlhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vlhs))))

(defthm forcing-logic.formula-size-of-logic.vrhs
  (implies (force (equal (logic.fmtype x) 'por*))
           (equal (< (logic.formula-size (logic.vrhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vrhs))))

(defthm logic.formula-size-of-logic.pnot
  (equal (logic.formula-size (logic.pnot x))
         (+ 1 (logic.formula-size x)))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.pnot))))

(defthm logic.formula-size-of-logic.por
  (equal (logic.formula-size (logic.por x y))
         (+ 1 (+ (logic.formula-size x) (logic.formula-size y))))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.por))))

(defthm logic.formula-size-of-pequal
  (equal (logic.formula-size (logic.pequal x y))
         (+ 1 (+ (logic.formula-size x) (logic.formula-size y))))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.pequal))))



(defund logic.formula-list-size (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ (logic.formula-size (car x))
         (logic.formula-list-size (cdr x)))
    0))

(defthm logic.formula-list-size-when-not-consp
  (implies (not (consp x))
           (equal (logic.formula-list-size x)
                  0))
  :hints(("Goal" :in-theory (enable logic.formula-list-size))))

(defthm logic.formula-list-size-of-cons
  (equal (logic.formula-list-size (cons a x))
         (+ (logic.formula-size a)
            (logic.formula-list-size x)))
  :hints(("Goal" :in-theory (enable logic.formula-list-size))))

(defthm natp-of-logic.formula-list-size
  (equal (natp (logic.formula-list-size x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordp-of-logic.formula-list-size
  (equal (ordp (logic.formula-list-size x))
         t))
