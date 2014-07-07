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
(include-book "eqtracep")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




(defund rw.weakening-eqtrace (x)
  ;; Infer (iff lhs rhs) from (equiv lhs rhs).
  (declare (xargs :guard (rw.eqtracep x)))
  (rw.eqtrace 'weakening t (rw.eqtrace->lhs x) (rw.eqtrace->rhs x) (list x)))

(encapsulate
 ()
 (local (in-theory (enable rw.weakening-eqtrace)))

 (defthm forcing-rw.eqtrace->method-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->method (rw.weakening-eqtrace x))
          'weakening))

 (defthm forcing-rw.eqtrace->iffp-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->iffp (rw.weakening-eqtrace x))
          t))

 (defthm forcing-rw.eqtrace->lhs-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->lhs (rw.weakening-eqtrace x))
          (rw.eqtrace->lhs x)))

 (defthm forcing-rw.eqtrace->rhs-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->rhs (rw.weakening-eqtrace x))
          (rw.eqtrace->rhs x)))

 (defthm forcing-rw.eqtrace->subtraces-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->subtraces (rw.weakening-eqtrace x))
          (list x)))

 (defthm forcing-rw.eqtracep-of-rw.weakening-eqtrace
   (implies (force (rw.eqtracep x))
            (equal (rw.eqtracep (rw.weakening-eqtrace x))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.weakening-eqtrace
   (implies (force (rw.eqtrace-atblp x atbl))
            (equal (rw.eqtrace-atblp (rw.weakening-eqtrace x) atbl)
                   t))))



(defund rw.weakening-eqtrace-okp (x)
  ;; Check if any nhyp in the hypbox would generate this weakening eqtrace.
  (declare (xargs :guard (and (rw.eqtracep x))))
  (let ((method    (rw.eqtrace->method x))
        (iffp      (rw.eqtrace->iffp x))
        (lhs       (rw.eqtrace->lhs x))
        (rhs       (rw.eqtrace->rhs x))
        (subtraces (rw.eqtrace->subtraces x)))
    (and (equal method 'weakening)
         (equal iffp t)
         (equal (len subtraces) 1)
         (equal lhs (rw.eqtrace->lhs (first subtraces)))
         (equal rhs (rw.eqtrace->rhs (first subtraces))))))

(defthm booleanp-of-rw.weakening-eqtrace-okp
  (equal (booleanp (rw.weakening-eqtrace-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.weakening-eqtrace-okp)
                                 (forcing-booleanp-of-rw.eqtrace->iffp)))))

(defthm forcing-rw.weakening-eqtrace-okp-of-rw.weakening-eqtrace
  (equal (rw.weakening-eqtrace-okp (rw.weakening-eqtrace x))
         t)
  :hints(("Goal" :in-theory (enable rw.weakening-eqtrace rw.weakening-eqtrace-okp))))
