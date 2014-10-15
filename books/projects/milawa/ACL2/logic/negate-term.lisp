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
(include-book "substitute-term")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund logic.negate-term (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.function 'not (list x)))

(defthm forcing-logic.termp-of-logic.negate-term
  (implies (force (logic.termp x))
           (equal (logic.termp (logic.negate-term x))
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term))))

(defthm forcing-logic.term-atblp-of-logic.negate-term
  (implies (force (and (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-atblp (logic.negate-term x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term))))



(defprojection :list (logic.negate-term-list x)
               :element (logic.negate-term x)
               :guard (logic.term-listp x))

(defthm forcing-logic.term-listp-of-logic.negate-term-list
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (logic.negate-term-list x))
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term-list))))

(defthm forcing-logic.term-list-atblp-of-logic.negate-term-list
  (implies (force (and (logic.term-list-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-atblp (logic.negate-term-list x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term-list))))



(defthm logic.substitute-of-logic.negate-term
  (equal (logic.substitute (logic.negate-term x) sigma)
         (logic.negate-term (logic.substitute x sigma)))
  :hints(("Goal" :in-theory (enable logic.negate-term))))

(defthm logic.substitute-list-of-logic.negate-term-list
  (equal (logic.substitute-list (logic.negate-term-list x) sigma)
         (logic.negate-term-list (logic.substitute-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))