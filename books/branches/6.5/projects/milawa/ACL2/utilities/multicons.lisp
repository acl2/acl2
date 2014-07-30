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
(include-book "cons-listp")
(include-book "mutually-disjoint")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund multicons (e x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (cons e (car x))
            (multicons e (cdr x)))
    nil))

;; BOZO the macro isn't proving this on its own??
(defthm car-of-multicons
  (equal (car (multicons e x))
         (if (consp x) (cons e (car x)) nil))
  :hints(("Goal" :in-theory (enable multicons))))

(defprojection
  :list (multicons e x)
  :element (cons e x))

(defthm cons-listp-of-multicons
  (equal (cons-listp (multicons e x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-multicons
  (equal (disjoint-from-nonep e (multicons a x))
         (or (memberp a e)
             (disjoint-from-nonep e x)))
  :hints(("Goal" :induct (cdr-induction x))))
