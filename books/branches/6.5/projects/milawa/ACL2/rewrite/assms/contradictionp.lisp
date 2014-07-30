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
(include-book "eqtrace-okp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.eqtrace-contradictionp (x)
  ;; We recognize traces of the following forms as contradictions:
  ;;  -- (equal c1 c2) = t
  ;;       Where c1,c2 are unequal constants
  ;;  -- (equal x (not* x)) = t
  ;;       By the term order, this also checks (equal (not* x) x) = t
  ;;  -- (iff nil t) = t
  ;;       By the term order, this also checks (iff t nil) = t
  ;;       By the canonicalization of constants, this also checks for all other
  ;;       non-nil constants besides t
  ;;  -- (iff x (not* x)) = t
  ;;       By the term order, this also checks (iff (not* x) x) = t
  (declare (xargs :guard (rw.eqtracep x)))
  (let ((lhs  (rw.eqtrace->lhs x))
        (rhs  (rw.eqtrace->rhs x))
        (iffp (rw.eqtrace->iffp x)))
    (or ;; Perhaps there is a contradiction from a constant
        (if iffp
            (and (equal lhs ''nil)
                 (equal rhs ''t))
          (and (logic.constantp lhs)
               (logic.constantp rhs)
               (not (equal lhs rhs))))
        ;; Perhaps there is a contradiction from (equiv x (not* x))
        (and (clause.negative-termp rhs)
             (equal (clause.negative-term-guts rhs) lhs)))))

(defthm booleanp-of-rw.eqtrace-contradictionp
  (equal (booleanp (rw.eqtrace-contradictionp x))
         t)
  :hints(("Goal" :in-theory (enable rw.eqtrace-contradictionp))))



(defund rw.find-eqtrace-contradiction (x)
  (declare (xargs :guard (rw.eqtrace-listp x)))
  (if (consp x)
      (if (rw.eqtrace-contradictionp (car x))
          (car x)
        (rw.find-eqtrace-contradiction (cdr x)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.find-eqtrace-contradiction)))

 (defthm forcing-rw.eqtracep-of-rw.find-eqtrace-contradiction
   (implies (and (rw.find-eqtrace-contradiction x)
                 (force (rw.eqtrace-listp x)))
            (equal (rw.eqtracep (rw.find-eqtrace-contradiction x))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.find-eqtrace-contradiction
   (implies (and (rw.find-eqtrace-contradiction x)
                 (force (rw.eqtrace-list-atblp x atbl)))
            (equal (rw.eqtrace-atblp (rw.find-eqtrace-contradiction x) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.find-eqtrace-contradiction
   (implies (and (rw.find-eqtrace-contradiction x)
                 (force (rw.eqtrace-list-okp x box)))
            (equal (rw.eqtrace-okp (rw.find-eqtrace-contradiction x) box)
                   t)))

 (defthm forcing-rw.eqtrace-contradictionp-of-rw.find-eqtrace-contradiction
   (implies (rw.find-eqtrace-contradiction x)
            (equal (rw.eqtrace-contradictionp (rw.find-eqtrace-contradiction x))
                   t))))
