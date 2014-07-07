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
(include-book "assms/eqtrace-arities")
(include-book "traces/trace-arities")
(include-book "ccsteps")
(set-verify-guards-eagerness 2)
(set-measure-function rank)
(set-well-founded-relation ord<)
(set-case-split-limitations nil)



(defund rw.faster-ccstepp (x)
  (declare (xargs :guard t))
  (let ((term (car (car x)))
        (hypbox (cdr (car x)))
        (contradiction (car (cdr x)))
        (trace (cdr (cdr x))))
    (and (logic.termp term)
         (rw.faster-hypboxp hypbox)
         (if contradiction
             (and (rw.eqtracep contradiction)
                  (rw.eqtrace-contradictionp contradiction)
                  (rw.eqtrace-okp contradiction hypbox)
                  (not trace))
           (and (rw.faster-tracep trace hypbox)
                (rw.trace->iffp trace)
                (equal (rw.trace->hypbox trace) hypbox)
                (equal (rw.trace->lhs trace) term))))))

(defthm rw.faster-ccstep-removal
  (equal (rw.faster-ccstepp x)
         (rw.ccstepp x))
  :hints(("Goal" :in-theory (enable rw.ccstepp rw.faster-ccstepp))))

(defund rw.faster-ccstep-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (rw.faster-ccstepp (car x))
           (rw.faster-ccstep-listp (cdr x)))
    t))

(defthm rw.faster-ccstep-list-removal
  (equal (rw.faster-ccstep-listp x)
         (rw.ccstep-listp x))
  :hints(("Goal" :in-theory (enable rw.faster-ccstep-listp))))




(defund rw.slow-ccstep-arities (x)
  (declare (xargs :guard (rw.ccstepp x)))
  (let* ((term          (rw.ccstep->term x))
         (hypbox        (rw.ccstep->hypbox x))
         (contradiction (rw.ccstep->contradiction x))
         (acc           (logic.slow-term-arities term))
         (acc           (app (rw.slow-hypbox-arities hypbox) acc)))
    (if contradiction
        (app (rw.slow-eqtrace-arities contradiction) acc)
      (app (rw.slow-faster-trace-arities (rw.ccstep->trace x) hypbox) acc))))

(defthm rw.slow-ccsteps-arities-correct
  (implies (force (rw.ccstepp x))
           (equal (logic.arities-okp (rw.slow-ccstep-arities x) atbl)
                  (and (logic.term-atblp (rw.ccstep->term x) atbl)
                       (rw.hypbox-atblp (rw.ccstep->hypbox x) atbl)
                       (if (rw.ccstep->contradiction x)
                           (rw.eqtrace-atblp (rw.ccstep->contradiction x) atbl)
                         (rw.trace-atblp (rw.ccstep->trace x) atbl)))))
  :hints(("Goal" :in-theory (e/d (rw.slow-ccstep-arities)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.ccstep-arities (x acc)
  (declare (xargs :guard (and (rw.ccstepp x)
                              (true-listp acc))))
  (let* ((term          (rw.ccstep->term x))
         (hypbox        (rw.ccstep->hypbox x))
         (contradiction (rw.ccstep->contradiction x))
         (acc           (logic.term-arities term acc))
         (acc           (rw.hypbox-arities hypbox acc)))
    (if contradiction
        (rw.eqtrace-arities contradiction acc)
      (rw.faster-flag-trace-arities 'term (rw.ccstep->trace x) hypbox acc))))

(defthm rw.cstep-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.ccstep-arities x acc)
                  (app (rw.slow-ccstep-arities x) acc)))
  :hints(("Goal"
          :in-theory (enable rw.ccstep-arities rw.slow-ccstep-arities))))



(defund rw.slow-ccstep-list-arities (x)
  (declare (xargs :guard (rw.ccstep-listp x)))
  (if (consp x)
      (app (rw.slow-ccstep-arities (car x))
           (rw.slow-ccstep-list-arities (cdr x)))
    nil))

(defthm rw.slow-ccstep-list-arities-correct
  (implies (force (rw.ccstep-listp x))
           (equal (logic.arities-okp (rw.slow-ccstep-list-arities x) atbl)
                  (and (logic.term-list-atblp (rw.ccstep-list-terms x) atbl)
                       (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes x) atbl)
                       (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions x) atbl)
                       (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.slow-ccstep-list-arities x)))))



(defund rw.ccstep-list-arities (x acc)
  (declare (xargs :guard (and (rw.ccstep-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.ccstep-arities (car x)
                         (rw.ccstep-list-arities (cdr x) acc))
    acc))

(defthm true-listp-of-rw.ccstep-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.ccstep-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-arities))))

(defthm rw.ccstep-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.ccstep-list-arities x acc)
                  (app (rw.slow-ccstep-list-arities x) acc)))
  :hints(("Goal"
          :in-theory (enable rw.slow-ccstep-list-arities
                             rw.ccstep-list-arities))))
