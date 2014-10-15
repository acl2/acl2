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
(include-book "urewrite-builders")
(%interactive)

(%autoadmit rw.empty-hypbox)

(%autoadmit rw.flag-urewrite)
(%autoadmit rw.urewrite)
(%autoadmit rw.urewrite-list)

(%autoprove definition-of-rw.urewrite
            (%enable default rw.urewrite rw.urewrite-list)
            (%restrict default rw.flag-urewrite (equal x 'x)))

(%autoprove definition-of-rw.urewrite-list
            (%enable default rw.urewrite rw.urewrite-list)
            (%restrict default rw.flag-urewrite (equal x 'x)))

(%autoprove rw.flag-urewrite-of-term
            (%enable default rw.urewrite))

(%autoprove rw.flag-urewrite-of-list
            (%enable default rw.urewrite-list))


(%autoprove rw.urewrite-list-when-not-consp
            (%restrict default definition-of-rw.urewrite-list (equal x 'x)))

(%autoprove rw.urewrite-list-of-cons
            (%restrict default definition-of-rw.urewrite-list (equal x '(cons a x))))

(%defprojection :list (rw.urewrite-list x iffp control n)
                :element (rw.urewrite x iffp control n))

(local (%disable default
                 formula-decomposition
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 unusual-memberp-rules
                 unusual-subsetp-rules
                 same-length-prefixes-equal-cheap
                 forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                 minus-when-not-less
                 rw.tracep-when-memberp-of-rw.trace-listp
                 rw.trace-list-rhses-when-not-consp))

(local (%splitlimit 10))

(%autoprove lemma-for-forcing-rw.tracep-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split cleanup urewrite))
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%enable default expensive-term/formula-inference)
            (%auto))

(%autoprove forcing-rw.tracep-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-listp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.urewrite)
                             (flag 'list))))



;; BOZO probably just take this out of our disables from above.
(local (%enable default expensive-arithmetic-rules-two))


(%autoprove lemma-for-forcing-rw.trace->iffp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split cleanup urewrite))
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.trace->iffp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-iffps-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace->lhs-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split cleanup urewrite))
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition))

(%autoprove forcing-rw.trace->lhs-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-lhses-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace->nhyps-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split urewrite crewrite))
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition))

(%autoprove forcing-rw.trace->nhyps-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace->nhyps-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-nhyps-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->nhyps-of-rw.urewrite)
                             (flag 'list))))




(%autoprove lemma-for-forcing-rw.trace-atblp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x)))

(%autoprove forcing-rw.trace-atblp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-atblp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-atblp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-atblp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace-env-okp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x)))

(%autoprove forcing-rw.trace-env-okp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-env-okp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace-okp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.trace-okp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-okp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.collect-forced-goals-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x)))

(%autoprove forcing-rw.collect-forced-goals-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.collect-forced-goals-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.collect-forced-goals-list-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.collect-forced-goals-of-rw.urewrite)
                             (flag 'list))))



(%autoprove forcing-rw.trace-list-formulas-of-rw.urewrite-list
            (%use (%instance (%thm rw.trace-list-formulas-when-all-equalp-of-rw.trace-list-hypboxes)
                             (hypbox (rw.empty-hypbox))
                             (x (rw.urewrite-list x iffp control n)))))

(%autoprove forcing-rw.trace-list-conclusion-formulas-of-rw.urewrite-list
            (%cdr-induction x)
            (%restrict default rw.trace-list-conclusion-formulas (equal x 'x))
            (%enable default rw.trace-conclusion-formula))



(%defprojection :list (rw.urewrite-list-list x iffp control n)
                :element (rw.urewrite-list x iffp control n))

(%autoprove cons-listp-of-rw.urewrite-list-list
            (%cdr-induction x))

(%autoprove forcing-rw.trace-list-listp-of-rw.urewrite-list-list
            (%cdr-induction x))

(%autoprove forcing-rw.collect-forced-goals-list-list-of-rw.urewrite-list-list
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../rewrite/urewrite")

