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

(defsection rw.secondary-eqtrace-nhyp-bldr
  (%autoadmit rw.secondary-eqtrace-nhyp-bldr)
  (local (%enable default
                  rw.secondary-eqtrace
                  rw.secondary-eqtrace-nhyp-bldr
                  logic.term-formula))
  (local (%enable default
                  forcing-equal-of-logic.pequal-rewrite-two
                  forcing-equal-of-logic.pequal-rewrite
                  forcing-equal-of-logic.por-rewrite-two
                  forcing-equal-of-logic.por-rewrite
                  forcing-equal-of-logic.pnot-rewrite-two
                  forcing-equal-of-logic.pnot-rewrite))
  (%autoprove rw.secondary-eqtrace-nhyp-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.secondary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.secondary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.proofp-of-rw.secondary-eqtrace-nhyp-bldr))

(defsection rw.secondary-eqtrace-bldr
  (%autoadmit rw.secondary-eqtrace-bldr)
  (local (%enable default
                  rw.secondary-eqtrace-bldr
                  rw.secondary-eqtrace-okp
                  rw.hypbox-formula
                  rw.eqtrace-formula))
  (%autoprove rw.secondary-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.secondary-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.secondary-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.secondary-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/secondary-eqtrace-bldr")

