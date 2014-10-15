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

(defsection rw.secondary-eqtrace
  (%autoadmit rw.secondary-eqtrace)
  (local (%enable default rw.secondary-eqtrace))
  (local (%disable default forcing-booleanp-of-rw.eqtrace->iffp))
  (%autoprove forcing-rw.eqtrace->method-of-rw.secondary-eqtrace)
  (%autoprove forcing-rw.eqtrace->iffp-of-rw.secondary-eqtrace)
  (%autoprove forcing-rw.eqtrace->subtraces-of-rw.secondary-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.secondary-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.secondary-eqtrace)
  (%autoprove rw.secondary-eqtrace-normalize-okp-1)
  (%autoprove rw.secondary-eqtrace-normalize-okp-2)
  (%autoprove rw.secondary-eqtrace-normalize-okp-3))


(defsection rw.find-nhyp-for-secondary-eqtracep
  (%autoadmit rw.find-nhyp-for-secondary-eqtracep)
  (local (%restrict default rw.find-nhyp-for-secondary-eqtracep (equal nhyps 'nhyps)))
  (%autoprove rw.find-nhyp-for-secondary-eqtracep-of-nil
              (%restrict default rw.find-nhyp-for-secondary-eqtracep (equal nhyps ''nil)))
  (%autoprove forcing-logic.termp-of-rw.find-nhyp-for-secondary-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-logic.term-atblp-of-rw.find-nhyp-for-secondary-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-memberp-of-rw.find-nhyp-for-secondary-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-rw.secondary-eqtrace-of-rw.find-nhyp-for-secondary-eqtracep
              (%cdr-induction nhyps)))

(defsection rw.secondary-eqtrace-okp
  (%autoadmit rw.secondary-eqtrace-okp)
  (local (%enable default rw.secondary-eqtrace-okp))
  (%autoprove booleanp-of-rw.secondary-eqtrace-okp)
  (%autoprove lemma-1-for-forcing-rw.secondary-eqtrace-okp-rw.secondary-eqtrace
              (%enable default
                       rw.secondary-eqtrace-okp
                       rw.secondary-eqtrace
                       rw.eqtrace))
  (%autoprove lemma-2-for-forcing-rw.secondary-eqtrace-okp-rw.secondary-eqtrace
              (%cdr-induction nhyps)
              (%restrict default rw.find-nhyp-for-secondary-eqtracep (equal nhyps 'nhyps))
              (%noexec rw.secondary-eqtrace))
  (%autoprove forcing-rw.secondary-eqtrace-okp-rw.secondary-eqtrace
              (%enable default
                       lemma-1-for-forcing-rw.secondary-eqtrace-okp-rw.secondary-eqtrace
                       lemma-2-for-forcing-rw.secondary-eqtrace-okp-rw.secondary-eqtrace)
              (%disable default rw.secondary-eqtrace-normalize-okp-1)
              ))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/secondary-eqtrace")

