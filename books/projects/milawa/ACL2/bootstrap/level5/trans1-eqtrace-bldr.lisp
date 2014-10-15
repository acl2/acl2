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
(%interactive)

(%autoprove lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)
(%autoprove lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
            (%enable default lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr))
(%autoprove lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)
(%autoprove lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)

(defsection rw.trans1-eqtrace-bldr
  (%autoadmit rw.trans1-eqtrace-bldr)
  (local (%enable default
                  rw.eqtrace-formula
                  rw.trans1-eqtrace-bldr
                  rw.trans1-eqtrace-okp
                  lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                  lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                  lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                  lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr))

  ;; Originally I didn't have this, but later changes to the rewriter exposed some
  ;; kind of loop caused by this rule, which was horribly problematic.

  (local (%disable default RW.EQTRACE->RHS-OF-SUB1-WHEN-RW.TRANS1-EQTRACE-OKP))
  (%autoprove forcing-rw.trans1-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.trans1-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.trans1-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/trans1-eqtrace-bldr")



