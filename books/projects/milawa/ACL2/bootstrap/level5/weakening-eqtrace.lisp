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

(defsection rw.weakening-eqtrace
  (%autoadmit rw.weakening-eqtrace)
  (local (%enable default rw.weakening-eqtrace))
  (%autoprove forcing-rw.eqtrace->method-of-rw.weakening-eqtrace)
  (%autoprove forcing-rw.eqtrace->iffp-of-rw.weakening-eqtrace)
  (%autoprove forcing-rw.eqtrace->lhs-of-rw.weakening-eqtrace)
  (%autoprove forcing-rw.eqtrace->rhs-of-rw.weakening-eqtrace)
  (%autoprove forcing-rw.eqtrace->subtraces-of-rw.weakening-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.weakening-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.weakening-eqtrace))

(defsection rw.weakening-eqtrace-okp
  (%autoadmit rw.weakening-eqtrace-okp)
  (local (%enable default rw.weakening-eqtrace-okp))
  (%autoprove booleanp-of-rw.weakening-eqtrace-okp)
  (%autoprove forcing-rw.weakening-eqtrace-okp-of-rw.weakening-eqtrace
              (%enable default rw.weakening-eqtrace)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/weakening-eqtrace")