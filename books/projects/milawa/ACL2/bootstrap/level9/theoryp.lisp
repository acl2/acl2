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
(include-book "theoryp-aux")
(%interactive)


(%autoadmit rw.slow-hyp-arities)
(%autoadmit rw.hyp-arities)

(%autoprove true-listp-of-rw.hyp-arities
            (%enable default rw.hyp-arities))

(%autoprove rw.hyp-arities-removal
            (%enable default rw.hyp-arities rw.slow-hyp-arities))

(%autoprove logic.slow-hyp-arities-correct
            (%forcingp nil)
            (%enable default rw.hyp-atblp rw.slow-hyp-arities))


(%autoadmit rw.slow-hyp-list-arities)
(%autoadmit rw.hyp-list-arities)

(%autoprove true-listp-of-rw.hyp-list-arities
            (%autoinduct rw.hyp-list-arities)
            (%restrict default rw.hyp-list-arities (equal x 'x)))

(%autoprove rw.hyp-list-arities-removal
            (%autoinduct rw.hyp-list-arities)
            (%restrict default rw.hyp-list-arities (equal x 'x))
            (%restrict default rw.slow-hyp-list-arities (equal x 'x)))

(%autoprove rw.slow-hyp-list-arities-correct
            (%cdr-induction x)
            (%forcingp nil)
            (%restrict default rw.hyp-list-atblp (equal x 'x))
            (%restrict default rw.slow-hyp-list-arities (equal x 'x)))



(%autoadmit rw.slow-rule-arities)
(%autoadmit rw.rule-arities)

(%autoprove true-listp-of-rw.rule-arities
            (%enable default rw.rule-arities))

(%autoprove rw.rule-arities-removal
            (%enable default rw.rule-arities rw.slow-rule-arities))

(%autoprove rw.slow-rule-arities-correct
            (%forcingp nil)
            (%enable default rw.slow-rule-arities rw.rule-atblp))



(%autoadmit rw.slow-rule-list-arities)
(%autoadmit rw.rule-list-arities)

(%autoprove true-listp-of-rw.rule-list-arities
            (%autoinduct rw.rule-list-arities)
            (%restrict default rw.rule-list-arities (equal x 'x)))

(%autoprove rw.rule-list-arities-removal
            (%autoinduct rw.rule-list-arities)
            (%restrict default rw.rule-list-arities (equal x 'x))
            (%restrict default rw.slow-rule-list-arities (equal x 'x)))

(%autoprove rw.slow-rule-list-arities-correct
            (%cdr-induction x)
            (%forcingp nil)
            (%restrict default rw.rule-list-atblp (equal x 'x))
            (%restrict default rw.slow-rule-list-arities (equal x 'x)))


(%autoadmit rw.slow-rule-list-list-arities)
(%autoadmit rw.rule-list-list-arities)

(%autoprove true-listp-of-rw.rule-list-list-arities
            (%autoinduct rw.rule-list-list-arities)
            (%restrict default rw.rule-list-list-arities (equal x 'x)))

(%autoprove rw.rule-list-list-arities-removal
            (%autoinduct rw.rule-list-list-arities)
            (%restrict default rw.rule-list-list-arities (equal x 'x))
            (%restrict default rw.slow-rule-list-list-arities (equal x 'x)))

(%autoprove rw.slow-rule-list-list-arities-correct
            (%cdr-induction x)
            (%forcingp nil)
            (%restrict default rw.slow-rule-list-list-arities (equal x 'x))
            (%restrict default rw.rule-list-list-atblp (equal x 'x)))



(%autoadmit rw.slow-typed-rulemap-arities)
(%autoadmit rw.typed-rulemap-arities)

(%autoprove true-listp-of-rw.typed-rulemap-arities
            (%autoinduct rw.typed-rulemap-arities)
            (%restrict default rw.typed-rulemap-arities (equal x 'x)))

(%autoprove rw.typed-rulemap-arities-removal
            (%autoinduct rw.typed-rulemap-arities)
            (%restrict default rw.typed-rulemap-arities (equal x 'x))
            (%restrict default rw.slow-typed-rulemap-arities (equal x 'x)))

(%autoprove rw.slow-typed-rulemap-arities-correct
            (%cdr-induction x)
            (%restrict default rw.slow-typed-rulemap-arities (equal x 'x)))


(%autoadmit rw.slow-theory-arities)
(%autoadmit rw.theory-arities)

(%autoprove true-listp-of-rw.theory-arities
            (%autoinduct rw.theory-arities)
            (%restrict default rw.theory-arities (equal x 'x)))

(%autoprove rw.theory-arities-removal
            (%autoinduct rw.theory-arities)
            (%restrict default rw.theory-arities (equal x 'x))
            (%restrict default rw.slow-theory-arities (equal x 'x)))

(%autoprove rw.slow-theory-arities-correct
            (%autoinduct rw.slow-theory-arities)
            (%forcingp nil)
            (%restrict default rw.slow-theory-arities (equal x 'x))
            (%restrict default rw.theory-atblp (equal x 'x)))


(%autoadmit rw.slow-theory-map-arities)
(%autoadmit rw.theory-map-arities)

(%autoprove true-listp-of-rw.theory-map-arities
            (%autoinduct rw.theory-map-arities)
            (%restrict default rw.theory-map-arities (equal x 'x)))

(%autoprove rw.theory-map-arities-removal
            (%autoinduct rw.theory-map-arities)
            (%restrict default rw.theory-map-arities (equal x 'x))
            (%restrict default rw.slow-theory-map-arities (equal x 'x)))

(%autoprove rw.slow-theory-map-arities-correct
            (%autoinduct rw.slow-theory-map-arities)
            (%restrict default rw.slow-theory-map-arities (equal x 'x)))

(%autoadmit rw.slow-rule-list-thms)
(%autoadmit rw.rule-list-thms)

(%autoprove true-listp-of-rw.rule-list-thms
            (%autoinduct rw.rule-list-thms)
            (%restrict default rw.rule-list-thms (equal x 'x)))

(%autoprove rw.rule-list-thms-removal
            (%autoinduct rw.rule-list-thms)
            (%restrict default rw.rule-list-thms (equal x 'x))
            (%restrict default rw.slow-rule-list-thms (equal x 'x)))

(%autoprove rw.slow-rule-list-thms-correct
            (%cdr-induction x)
            (%restrict default rw.slow-rule-list-thms (equal x 'x))
            (%restrict default rw.rule-list-env-okp (equal x 'x))
            (%enable default rw.rule-env-okp))



(%autoadmit rw.slow-rule-list-list-thms)
(%autoadmit rw.rule-list-list-thms)

(%autoprove true-listp-of-rw.rule-list-list-thms
            (%autoinduct rw.rule-list-list-thms)
            (%restrict default rw.rule-list-list-thms (equal x 'x)))

(%autoprove rw.rule-list-list-thms-removal
            (%autoinduct rw.rule-list-list-thms)
            (%restrict default rw.rule-list-list-thms (equal x 'x))
            (%restrict default rw.slow-rule-list-list-thms (equal x 'x)))

(%autoprove rw.slow-rule-list-list-thms-correct
            (%cdr-induction x)
            (%restrict default rw.slow-rule-list-list-thms (equal x 'x))
            (%restrict default rw.rule-list-list-env-okp (equal x 'x)))


(%autoadmit rw.slow-typed-rulemap-thms)
(%autoadmit rw.typed-rulemap-thms)

(%autoprove true-listp-of-rw.typed-rulemap-thms
            (%autoinduct rw.typed-rulemap-thms)
            (%restrict default rw.typed-rulemap-thms (equal x 'x)))

(%autoprove rw.typed-rulemap-thms-removal
            (%autoinduct rw.typed-rulemap-thms)
            (%restrict default rw.typed-rulemap-thms (equal x 'x))
            (%restrict default rw.slow-typed-rulemap-thms (equal x 'x)))

(%autoprove rw.slow-typed-rulemap-thms-correct
            (%cdr-induction x)
            (%restrict default rw.slow-typed-rulemap-thms (equal x 'x)))


(%autoadmit rw.slow-theory-thms)
(%autoadmit rw.theory-thms)

(%autoprove true-listp-of-rw.theory-thms
            (%autoinduct rw.theory-thms)
            (%restrict default rw.theory-thms (equal x 'x)))

(%autoprove rw.theory-thms-removal
            (%autoinduct rw.theory-thms)
            (%restrict default rw.theory-thms (equal x 'x))
            (%restrict default rw.slow-theory-thms (equal x 'x)))

(%autoprove rw.slow-theory-thms-correct
            (%autoinduct rw.slow-theory-thms)
            (%forcingp nil)
            (%restrict default rw.slow-theory-thms (equal x 'x))
            (%restrict default rw.theory-env-okp (equal x 'x)))


(%autoadmit rw.slow-theory-list-thms)
(%autoadmit rw.theory-list-thms)

(%autoprove true-listp-of-rw.theory-list-thms
            (%autoinduct rw.theory-list-thms)
            (%restrict default rw.theory-list-thms (equal x 'x)))

(%autoprove rw.theory-list-thms-removal
            (%autoinduct rw.theory-list-thms)
            (%restrict default rw.theory-list-thms (equal x 'x))
            (%restrict default rw.slow-theory-list-thms (equal x 'x)))

(%autoprove rw.slow-theory-list-thms-correct
            (%cdr-induction x)
            (%restrict default rw.slow-theory-list-thms (equal x 'x)))


(%autoadmit rw.slow-theory-map-thms)
(%autoadmit rw.theory-map-thms)

(%autoprove true-listp-of-rw.theory-map-thms
            (%autoinduct rw.theory-map-thms)
            (%restrict default rw.theory-map-thms (equal x 'x)))

(%autoprove rw.theory-map-thms-removal
            (%autoinduct rw.theory-map-thms)
            (%restrict default rw.theory-map-thms (equal x 'x))
            (%restrict default rw.slow-theory-map-thms (equal x 'x)))

(%autoprove rw.slow-theory-map-thms-correct
            (%cdr-induction x)
            (%restrict default rw.slow-theory-map-thms (equal x 'x)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/theoryp"
                                         ;; we probably just shouldn't even introduce a :induction rule for
                                         ;; this.  there's no milawa equivalent.
                                         induction-for-rw.theory-allrules)
