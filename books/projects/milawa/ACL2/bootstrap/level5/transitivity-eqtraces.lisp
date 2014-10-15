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

(defsection rw.trans1-eqtrace-okp
  (%autoadmit rw.trans1-eqtrace-okp)
  (%enable default rw.trans1-eqtrace-okp)
  (%autoprove booleanp-of-rw.trans1-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub1-when-rw.trans1-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub1-when-rw.trans1-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub2-when-rw.trans1-eqtrace-okp))

(defsection rw.trans1-eqtrace
  (%autoadmit rw.trans1-eqtrace)
  (local (%enable default rw.trans1-eqtrace))
  (%autoprove rw.eqtrace->method-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->iffp-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->lhs-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->rhs-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->subtraces-of-rw.trans1-eqtrace)
  (%autoprove lemma-for-forcing-rw.eqtracep-of-rw.trans1-eqtrace
              (%disable default forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs)
              (%use (%instance (%thm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs) (x x)))
              (%use (%instance (%thm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs) (x y))))
  (%autoprove forcing-rw.eqtracep-of-rw.trans1-eqtrace
              (%enable default lemma-for-forcing-rw.eqtracep-of-rw.trans1-eqtrace))
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.trans1-eqtrace)
  (%autoprove forcing-rw.trans1-eqtrace-okp-of-rw.trans1-eqtrace))

(defsection rw.trans2-eqtrace-okp
  (%autoadmit rw.trans2-eqtrace-okp)
  (local (%enable default rw.trans2-eqtrace-okp))
  (%autoprove booleanp-of-rw.trans2-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub1-when-rw.trans2-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub1-when-rw.trans2-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub2-when-rw.trans2-eqtrace-okp))

(defsection rw.trans2-eqtrace
  (%autoadmit rw.trans2-eqtrace)
  (local (%enable default rw.trans2-eqtrace))
  (%autoprove rw.eqtrace->method-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->iffp-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->lhs-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->rhs-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->subtraces-of-rw.trans2-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.trans2-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.trans2-eqtrace)
  (%autoprove forcing-rw.trans2-eqtrace-okp-of-rw.trans2-eqtrace
              (%enable default rw.trans2-eqtrace-okp)))

(defsection rw.trans3-eqtrace-okp
  (%autoadmit rw.trans3-eqtrace-okp)
  (local (%enable default rw.trans3-eqtrace-okp))
  (%autoprove booleanp-of-rw.trans3-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub1-when-rw.trans3-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub1-when-rw.trans3-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub2-when-rw.trans3-eqtrace-okp))

(defsection rw.trans3-eqtrace
  (%autoadmit rw.trans3-eqtrace)
  (local (%enable default rw.trans3-eqtrace))
  (%autoprove rw.eqtrace->method-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->iffp-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->lhs-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->rhs-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->subtraces-of-rw.trans3-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.trans3-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.trans3-eqtrace)
  (%autoprove forcing-rw.trans3-eqtrace-okp-of-rw.trans3-eqtrace
              (%enable default rw.trans3-eqtrace-okp)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/transitivity-eqtraces")