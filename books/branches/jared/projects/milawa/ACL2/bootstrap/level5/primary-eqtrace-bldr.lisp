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

(%defderiv rw.primary-eqtrace-nhyp-bldr-lemma-1 :omit-okp t)
(%defderiv rw.primary-eqtrace-nhyp-bldr-lemma-2 :omit-okp t)

(defsection rw.primary-eqtrace-nhyp-bldr
  (%autoadmit rw.primary-eqtrace-nhyp-bldr)
  (local (%disable default
                   forcing-equal-of-logic.pequal-rewrite-two
                   forcing-equal-of-logic.pequal-rewrite
                   forcing-equal-of-logic.por-rewrite-two
                   forcing-equal-of-logic.por-rewrite
                   forcing-equal-of-logic.pnot-rewrite-two
                   forcing-equal-of-logic.pnot-rewrite))
  (local (%enable default
                  rw.primary-eqtrace
                  rw.primary-eqtrace-nhyp-bldr
                  theorem-not-when-nil
                  logic.term-formula))
  (%autoprove rw.primary-eqtrace-nhyp-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.primary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.primary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.proofp-of-rw.primary-eqtrace-nhyp-bldr))

(defsection rw.primary-eqtrace-bldr
  (%autoadmit rw.primary-eqtrace-bldr)
  (local (%enable default
                  rw.primary-eqtrace-bldr
                  rw.primary-eqtrace-okp
                  rw.hypbox-formula
                  rw.eqtrace-formula))
  (%autoprove rw.primary-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.primary-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.primary-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.primary-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/primary-eqtrace-bldr"

                                         BOOLEANP-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP
                                         RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP-OF-LOGIC.APPEAL-IDENTITY
                                         LEMMA-1-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP
                                         LEMMA-2-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP
                                         FORCING-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP

                                         BOOLEANP-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP
                                         RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP-OF-LOGIC.APPEAL-IDENTITY
                                         LEMMA-1-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP
                                         LEMMA-2-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP
                                         FORCING-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP)
