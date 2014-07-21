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
(include-book "trans1-eqtrace-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund rw.weakening-eqtrace-bldr (x box proofs)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.weakening-eqtrace-okp x)
                              (rw.eqtrace-okp x box)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box)))
                  :verify-guards nil)
           (ignore box))
  (if (rw.eqtrace->iffp (first (rw.eqtrace->subtraces x)))
      (logic.appeal-identity (first proofs))
    (build.disjoined-iff-from-equal (first proofs))))

(defobligations rw.weakening-eqtrace-bldr
  (build.disjoined-iff-from-equal))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-formula
                           rw.weakening-eqtrace-bldr
                           rw.weakening-eqtrace-okp
                           lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                           lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)))

 (defthm forcing-rw.weakening-eqtrace-bldr-under-iff
   (iff (rw.weakening-eqtrace-bldr x box proofs)
        t))

 (defthm forcing-logic.appealp-of-rw.weakening-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.weakening-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.appealp (rw.weakening-eqtrace-bldr x box proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.weakening-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.weakening-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.conclusion (rw.weakening-eqtrace-bldr x box proofs))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.weakening-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.weakening-eqtrace-okp x)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))
                        ;; ---
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.weakening-eqtrace-bldr)))
            (equal (logic.proofp (rw.weakening-eqtrace-bldr x box proofs) axioms thms atbl)
                   t)))

 (verify-guards rw.weakening-eqtrace-bldr))

