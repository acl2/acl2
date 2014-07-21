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

(%defderiv rw.direct-iff-eqtrace-nhyp-bldr-lemma-1 :omit-okp t)
(%defderiv rw.direct-iff-eqtrace-nhyp-bldr-lemma-2 :omit-okp t)

(defsection rw.direct-iff-eqtrace-nhyp-bldr
  (%autoadmit rw.direct-iff-eqtrace-nhyp-bldr)
  (local (%enable default
                  rw.direct-iff-eqtrace
                  rw.direct-iff-eqtrace-nhyp-bldr
                  theorem-not-when-nil
                  logic.term-formula))
  (local (%enable default
                  forcing-equal-of-logic.pequal-rewrite-two
                  forcing-equal-of-logic.pequal-rewrite
                  forcing-equal-of-logic.por-rewrite-two
                  forcing-equal-of-logic.por-rewrite
                  forcing-equal-of-logic.pnot-rewrite-two
                  forcing-equal-of-logic.pnot-rewrite))
  (%autoprove rw.direct-iff-eqtrace-nhyp-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.direct-iff-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.direct-iff-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.proofp-of-rw.direct-iff-eqtrace-nhyp-bldr))

(defsection rw.direct-iff-eqtrace-bldr
  (%autoadmit rw.direct-iff-eqtrace-bldr)
  (local (%enable default
                  rw.direct-iff-eqtrace-bldr
                  rw.direct-iff-eqtrace-okp
                  rw.hypbox-formula
                  rw.eqtrace-formula))
  (%autoprove rw.direct-iff-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.direct-iff-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.direct-iff-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.direct-iff-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/direct-iff-eqtrace-bldr"
                                         booleanp-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp-of-logic.appeal-identity
                                         lemma-1-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         lemma-2-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         forcing-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         booleanp-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp
                                         rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp-of-logic.appeal-identity
                                         lemma-1-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp
                                         lemma-2-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp
                                         forcing-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp)

