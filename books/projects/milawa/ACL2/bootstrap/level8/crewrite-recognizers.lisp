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
(include-book "tracep")
(%interactive)


(%autoadmit rw.crewrite-if-specialcase-same-tracep)

(%autoprove booleanp-of-rw.crewrite-if-specialcase-same-tracep
            (%enable default rw.crewrite-if-specialcase-same-tracep))


(%autoadmit rw.crewrite-if-generalcase-tracep)

(%autoprove booleanp-of-rw.crewrite-if-generalcase-tracep
            (%enable default rw.crewrite-if-generalcase-tracep))



(%autoadmit rw.crewrite-rule-tracep)

(%autoprove booleanp-of-rw.crewrite-rule-tracep
            (%enable default rw.crewrite-rule-tracep))



(%autoadmit rw.crewrite-rule-trace-env-okp)

(%autoprove booleanp-of-rw.crewrite-rule-trace-env-okp
            (%enable default rw.crewrite-rule-trace-env-okp))



(%autoadmit rw.assumptions-tracep)

(%autoprove booleanp-of-rw.assumptions-tracep
            (%enable default rw.assumptions-tracep))



(%autoadmit rw.force-tracep)

(%autoprove booleanp-of-rw.force-tracep
            (%enable default rw.force-tracep))



(%autoadmit rw.weakening-tracep)

(%autoprove booleanp-of-rw.weakening-tracep
            (%enable default rw.weakening-tracep))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/crewrite-recognizers")
