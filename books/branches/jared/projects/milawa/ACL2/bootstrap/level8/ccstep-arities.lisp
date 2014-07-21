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
(include-book "trace-arities")
(include-book "ccsteps")
(%interactive)


(%autoadmit rw.faster-ccstepp)

(%autoprove rw.faster-ccstep-removal
            (%enable default rw.ccstepp rw.faster-ccstepp))

(%autoadmit rw.faster-ccstep-listp)

(%autoprove rw.faster-ccstep-list-removal
            (%cdr-induction x)
            (%restrict default rw.faster-ccstep-listp (equal x 'x)))


(%autoadmit rw.slow-ccstep-arities)

(%autoprove rw.slow-ccsteps-arities-correct
            (%enable default rw.slow-ccstep-arities))

(%autoadmit rw.ccstep-arities)

(%autoprove rw.cstep-arities-removal
            (%enable default rw.ccstep-arities rw.slow-ccstep-arities))


(%autoadmit rw.slow-ccstep-list-arities)

(%autoprove rw.slow-ccstep-list-arities-correct
            (%cdr-induction x)
            (%restrict default rw.slow-ccstep-list-arities (equal x 'x)))


(%autoadmit rw.ccstep-list-arities)

(%autoprove true-listp-of-rw.ccstep-list-arities
            (%autoinduct rw.ccstep-list-arities x acc)
            (%restrict default rw.ccstep-list-arities (equal x 'x)))

(%autoprove rw.ccstep-list-arities-removal
            (%autoinduct rw.ccstep-list-arities x acc)
            (%restrict default rw.ccstep-list-arities (equal x 'x))
            (%restrict default rw.slow-ccstep-list-arities (equal x 'x)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/ccstep-arities")

