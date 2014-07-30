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
(include-book "hypboxp")
(%interactive)

(%autoadmit rw.slow-hypbox-arities)
(%autoadmit rw.hypbox-arities)

(%autoprove true-listp-of-rw.hypbox-arities
            (%enable default rw.hypbox-arities))

(%autoprove rw.hypbox-arities-removal
            (%enable default rw.hypbox-arities rw.slow-hypbox-arities))

(%autoprove rw.slow-hypbox-arities-correct
            (%forcingp nil)
            (%enable default
                     rw.hypbox-arities
                     rw.slow-hypbox-arities
                     rw.hypbox-atblp))

(%autoadmit rw.fast-hypbox-atblp)

(%autoprove rw.fast-hypbox-atblp-removal
            (%enable default rw.fast-hypbox-atblp))



(%autoadmit rw.slow-hypbox-list-arities)
(%autoadmit rw.hypbox-list-arities)

(%autoprove true-listp-of-rw.hypbox-list-arities
            (%autoinduct rw.hypbox-list-arities)
            (%restrict default rw.hypbox-list-arities (equal x 'x)))

(%autoprove rw.hypbox-list-arities-removal
            (%autoinduct rw.hypbox-list-arities)
            (%restrict default rw.hypbox-list-arities (equal x 'x))
            (%restrict default rw.slow-hypbox-list-arities (equal x 'x)))

(%autoprove rw.slow-hypbox-list-arities-correct
            (%cdr-induction x)
            (%restrict default rw.slow-hypbox-list-arities (equal x 'x)))



(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/hypbox-arities")