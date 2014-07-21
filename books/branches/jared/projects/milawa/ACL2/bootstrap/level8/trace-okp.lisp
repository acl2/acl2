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
(include-book "basic-recognizers")
(include-book "urewrite-recognizers")
(include-book "crewrite-recognizers")
(%interactive)


(%autoadmit rw.trace-step-okp)

(%autoadmit rw.trace-step-env-okp)

(%autoprove booleanp-of-rw.trace-step-okp
            (%enable default rw.trace-step-okp))

(%autoprove booleanp-of-rw.trace-step-env-okp
            (%enable default rw.trace-step-env-okp))



(%autoadmit rw.flag-trace-okp)

(%autoadmit rw.trace-okp)

(%autoadmit rw.trace-list-okp)

(%autoprove definition-of-rw.trace-okp
            (%restrict default rw.flag-trace-okp (equal x 'x))
            (%enable default rw.trace-okp rw.trace-list-okp))

(%autoprove definition-of-rw.trace-list-okp
            (%restrict default rw.flag-trace-okp (equal x 'x))
            (%enable default rw.trace-okp rw.trace-list-okp))


(%autoprove rw.trace-step-okp-of-nil
            (%enable default rw.trace-step-okp))

(%autoprove rw.trace-okp-of-nil
            (%restrict default definition-of-rw.trace-okp (equal x ''nil)))

(%autoprove rw.trace-list-okp-when-not-consp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-list-okp (equal x 'x)))

(%autoprove rw.trace-list-okp-of-cons
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-list-okp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-rw.trace-okp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-okp (equal x 'x)))

(%autoprove booleanp-of-rw.trace-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-okp)
                             (flag 'term))))

(%autoprove booleanp-of-rw.trace-list-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-okp)
                             (flag 'list))))


(%deflist rw.trace-list-okp (x)
          (rw.trace-okp x))

(%autoprove rw.trace-step-okp-when-rw.trace-okp
            (%restrict default definition-of-rw.trace-okp (equal x 'x)))

(%autoprove rw.trace-list-okp-of-rw.trace->subtraces-when-rw.trace-okp
            (%restrict default definition-of-rw.trace-okp (equal x 'x)))





(%autoadmit rw.flag-trace-env-okp)

(%autoadmit rw.trace-env-okp)

(%autoadmit rw.trace-list-env-okp)

(%autoprove definition-of-rw.trace-env-okp
            (%restrict default rw.flag-trace-env-okp (equal x 'x))
            (%enable default rw.trace-env-okp rw.trace-list-env-okp))

(%autoprove definition-of-rw.trace-list-env-okp
            (%restrict default rw.flag-trace-env-okp (equal x 'x))
            (%enable default rw.trace-env-okp rw.trace-list-env-okp))

(%autoprove rw.trace-list-env-okp-when-not-consp
            (%restrict default definition-of-rw.trace-list-env-okp (equal x 'x)))

(%autoprove rw.trace-list-env-okp-of-cons
            (%restrict default definition-of-rw.trace-list-env-okp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-rw.trace-env-okp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-env-okp (equal x 'x)))

(%autoprove booleanp-of-rw.trace-env-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-env-okp)
                             (flag 'term))))

(%autoprove booleanp-of-rw.trace-list-env-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-env-okp)
                             (flag 'list))))

(%autoprove rw.trace-step-env-okp-of-nil
            (%enable default rw.trace-step-env-okp))

(%autoprove rw.trace-env-okp-of-nil
            (%restrict default definition-of-rw.trace-env-okp (equal x ''nil)))

(%deflist rw.trace-list-env-okp (x axioms thms atbl)
          (rw.trace-env-okp x axioms thms atbl))

(%autoprove rw.trace-step-env-okp-when-rw.trace-env-okp
            (%restrict default definition-of-rw.trace-env-okp (equal x 'x)))

(%autoprove rw.trace-list-env-okp-of-rw.trace->subtraces-when-rw.trace-env-okp
            (%restrict default definition-of-rw.trace-env-okp (equal x 'x)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/trace-okp")



