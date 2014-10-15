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
(include-book "urewrite")
(include-book "fast-traces")
(%interactive)

(%autoadmit rw.fast-flag-urewrite)
(%autoadmit rw.fast-urewrite)
(%autoadmit rw.fast-urewrite-list)

(%autoprove definition-of-rw.fast-urewrite
            (%enable default rw.fast-urewrite rw.fast-urewrite-list)
            (%restrict default rw.fast-flag-urewrite (equal x 'x)))

(%autoprove definition-of-rw.fast-urewrite-list
            (%enable default rw.fast-urewrite rw.fast-urewrite-list)
            (%restrict default rw.fast-flag-urewrite (equal x 'x)))

(%autoprove rw.fast-flag-urewrite-of-term
            (%enable default rw.fast-urewrite))

(%autoprove rw.fast-flag-urewrite-of-list
            (%enable default rw.fast-urewrite-list))

(%autoprove rw.fast-urewrite-under-iff
            (%restrict default definition-of-rw.fast-urewrite (equal x 'x)))

(%autoprove len-of-rw.ftraces->rhses-of-rw.fast-urewrite-list
            (%cdr-induction x)
            (%restrict default definition-of-rw.fast-urewrite-list (equal x 'x)))




(%autoprove lemma-for-forcing-rw.ftracep-of-rw.fast-urewrite
            (%autoinduct rw.fast-flag-urewrite)
            (%splitlimit 10)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      expensive-term/formula-inference
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      formula-decomposition)
            (%auto)
            (%restrict default definition-of-rw.fast-urewrite (equal x 'x))
            (%restrict default definition-of-rw.fast-urewrite-list (memberp x '(x (cons x1 x2))))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.ftracep-of-rw.fast-urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.fast-urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.ftrace-listp-of-rw.fast-urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.fast-urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace-fast-image-of-rw.urewrite
            (%autoinduct rw.fast-flag-urewrite)
            (%splitlimit 10)
            (%enable default rw.trace-fast-image-equivalence-lemmas)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      expensive-term/formula-inference
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      formula-decomposition)
            (%auto)
            (%restrict default definition-of-rw.fast-urewrite (equal x 'x))
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%restrict default definition-of-rw.fast-urewrite-list (memberp x '(x (cons x1 x2))))
            (%restrict default definition-of-rw.urewrite-list (memberp x '(x (cons x1 x2))))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.trace-fast-image-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-fast-image-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-fast-image-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-fast-image-of-rw.urewrite)
                             (flag 'list))))



(%autoprove forcing-rw.ftrace->rhs-of-rw.fast-urewrite
            (%disable default forcing-rw.trace-fast-image-of-rw.urewrite)
            (%use (%thm forcing-rw.trace-fast-image-of-rw.urewrite)))

(%autoprove forcing-rw.ftraces->rhses-of-rw.fast-urewrite-list
            (%disable default forcing-rw.trace-list-fast-image-of-rw.urewrite-list)
            (%use (%thm forcing-rw.trace-list-fast-image-of-rw.urewrite-list)))

(%autoprove forcing-rw.ftrace->fgoals-of-rw.fast-urewrite
            (%disable default forcing-rw.trace-fast-image-of-rw.urewrite)
            (%use (%thm forcing-rw.trace-fast-image-of-rw.urewrite)))

(%autoprove forcing-rw.ftraces->fgoals-of-rw.fast-urewrite-list
            (%disable default forcing-rw.trace-list-fast-image-of-rw.urewrite-list)
            (%use (%thm forcing-rw.trace-list-fast-image-of-rw.urewrite-list)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/fast-urewrite")

