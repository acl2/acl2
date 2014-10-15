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
(include-book "evaluator-bldr-2")
(%interactive)


(%autoadmit rw.fail-tracep)

(%autoprove booleanp-of-rw.fail-tracep
            (%enable default rw.fail-tracep))


(%autoadmit rw.transitivity-tracep)

(%autoprove booleanp-of-rw.transitivity-tracep
            (%enable default rw.transitivity-tracep))


(%autoadmit rw.equiv-by-args-tracep)

(%autoprove booleanp-of-rw.equiv-by-args-tracep
            (%enable default rw.equiv-by-args-tracep))



(%autoadmit rw.lambda-equiv-by-args-tracep)

(%autoprove booleanp-of-rw.lambda-equiv-by-args-tracep
            (%enable default rw.lambda-equiv-by-args-tracep))



(%autoadmit rw.beta-reduction-tracep)

(%autoprove booleanp-of-rw.beta-reduction-tracep
            (%enable default rw.beta-reduction-tracep))



(%autoadmit rw.ground-tracep)

(%autoprove booleanp-of-rw.ground-tracep
            (%enable default rw.ground-tracep))


(%autoadmit rw.if-specialcase-nil-tracep)

(%autoprove booleanp-of-rw.if-specialcase-nil-tracep
            (%enable default rw.if-specialcase-nil-tracep))



(%autoadmit rw.if-specialcase-t-tracep)

(%autoprove booleanp-of-rw.if-specialcase-t-tracep
            (%enable default rw.if-specialcase-t-tracep))



(%autoadmit rw.not-tracep)

(%autoprove booleanp-of-rw.not-tracep
            (%enable default rw.not-tracep))


(%autoadmit rw.negative-if-tracep)

(%autoprove booleanp-of-rw.negative-if-tracep
            (%enable default rw.negative-if-tracep))


(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/basic-recognizers")