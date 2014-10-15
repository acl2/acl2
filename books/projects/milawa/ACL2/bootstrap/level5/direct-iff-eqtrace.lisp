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
(%interactive)

(defsection rw.direct-iff-eqtrace
  (%autoadmit rw.direct-iff-eqtrace)
  (local (%enable default rw.direct-iff-eqtrace))
  (%autoprove forcing-rw.eqtrace->method-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtrace->iffp-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtrace->subtraces-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.direct-iff-eqtrace)
  (%autoprove rw.direct-iff-eqtrace-normalize-okp-1)
  (%autoprove rw.direct-iff-eqtrace-normalize-okp-2)
  (%autoprove rw.direct-iff-eqtrace-normalize-okp-3))


(defsection rw.find-nhyp-for-direct-iff-eqtracep
  (%autoadmit rw.find-nhyp-for-direct-iff-eqtracep)
  (local (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps 'nhyps)))
  (%autoprove rw.find-nhyp-for-direct-iff-eqtracep-of-nil
              (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps ''nil)))
  (%autoprove forcing-logic.termp-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-logic.term-atblp-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-memberp-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-rw.direct-iff-eqtrace-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps)))

(defsection rw.direct-iff-eqtrace-okp
  (%autoadmit rw.direct-iff-eqtrace-okp)
  (local (%enable default rw.direct-iff-eqtrace-okp))
  (%autoprove booleanp-of-rw.direct-iff-eqtrace-okp)
  (%autoprove lemma-for-forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace
              (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps 'nhyps))
              (%cdr-induction nhyps))
  (%autoprove forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace
              (%enable default lemma-for-forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace)
              (%disable default rw.direct-iff-eqtrace-normalize-okp-1)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/direct-iff-eqtrace")

