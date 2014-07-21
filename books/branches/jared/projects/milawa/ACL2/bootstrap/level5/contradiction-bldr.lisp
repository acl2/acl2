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
(include-book "contradictionp")
(include-book "eqtrace-compiler")
(%interactive)


(%deftheorem theorem-inequality-of-not-x-and-x)
(%deftheorem theorem-not-x-and-x-under-iff)
(%deftheorem rw.eqtrace-contradiction-lemma1)

(defsection rw.eqtrace-contradiction-lemma2
  (%autoadmit rw.eqtrace-contradiction-lemma2)
  (local (%enable default
                  rw.eqtrace-contradiction-lemma2
                  theorem-not-x-and-x-under-iff
                  theorem-symmetry-of-iff))
  (%autoprove rw.eqtrace-contradiction-lemma2-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.eqtrace-contradiction-lemma2)
  (%autoprove forcing-logic.conclusion-of-rw.eqtrace-contradiction-lemma2)
  (%autoprove forcing-logic.proofp-of-rw.eqtrace-contradiction-lemma2))

(%defderiv rw.eqtrace-contradiction-bldr-lemma3a :omit-okp t)
(%defderiv rw.eqtrace-contradiction-bldr-lemma3 :omit-okp t)


(defsection rw.eqtrace-contradiction-bldr
  (%autoadmit rw.eqtrace-contradiction-bldr)
  (local (%enable default
                  rw.eqtrace-contradictionp
                  rw.eqtrace-contradiction-bldr
                  rw.eqtrace-formula
                  rw.eqtrace-contradiction-lemma1
                  theorem-inequality-of-not-x-and-x))
  (%autoprove rw.eqtrace-contradiction-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.eqtrace-contradiction-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.eqtrace-contradiction-bldr)
  (%autoprove forcing-logic.proofp-of-rw.eqtrace-contradiction-bldr))

(%autoadmit rw.eqtrace-contradiction-bldr-okp)

(%autoadmit rw.eqtrace-contradiction-bldr-high)

(defsection rw.eqtrace-contradiction-bldr-okp
  (local (%enable default rw.eqtrace-contradiction-bldr-okp))
  (%autoprove booleanp-of-rw.eqtrace-contradiction-bldr-okp)
  (%autoprove rw.eqtrace-contradiction-bldr-okp-of-logic.appeal-identity)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free
                   forcing-logic.term-list-atblp-of-logic.function-args))
  (%autoprove lemma-1-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
  (%autoprove forcing-soundness-of-rw.eqtrace-contradiction-bldr-okp
              (%enable default
                       lemma-1-for-soundness-of-rw.eqtrace-contradiction-bldr-okp
                       lemma-2-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.eqtrace-contradiction-bldr (first (logic.extras x))
                                                                 (second (logic.extras x))))))))


