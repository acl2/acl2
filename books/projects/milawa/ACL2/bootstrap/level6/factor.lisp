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
(include-book "simple-termp")
(%interactive)


(%autoadmit clause.flag-factor)
(%disable default clause.flag-factor)


(%autoadmit clause.factor)
(%autoadmit clause.factor-list)

(%autoprove definition-of-clause.factor
            (%enable default clause.factor clause.factor-list)
            (%restrict default clause.flag-factor (equal x 'x)))

(%autoprove definition-of-clause.factor-list
            (%enable default clause.factor clause.factor-list)
            (%restrict default clause.flag-factor (equal x 'x)))

(%autoprove clause.flag-factor-of-term-removal
            (%enable default clause.factor))

(%autoprove clause.flag-factor-of-list-removal
            (%enable default clause.factor-list))

(%autoprove clause.factor-list-when-not-consp
            (%restrict default definition-of-clause.factor-list (equal x 'x)))

(%autoprove clause.factor-list-of-cons
            (%restrict default definition-of-clause.factor-list (equal x '(cons a x))))

(%defprojection :list (clause.factor-list x assignment)
                :element (clause.factor x assignment))

(%autoprove clause.factor-list-when-len-three)

(%autoprove clause.factor-when-logic.constantp
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-logic.variablep
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-non-if-logic.functionp
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-if-expression
            (%forcingp nil)
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-logic.lambdap
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-degenerate
            (%restrict default definition-of-clause.factor (equal x 'x)))


(%autoprove lemma-for-forcing-logic.termp-of-clause.factor
            (%clause.simple-term-induction flag x)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      forcing-logic.functionp-when-logic.base-evaluablep
                      not-equal-when-less
                      trichotomy-of-<
                      logic.formulap-when-not-consp))

(%autoprove forcing-logic.termp-of-clause.factor
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-clause.factor)
                             (flag 'term))))

(%autoprove forcing-logic.term-listp-of-clause.factor-list
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-clause.factor)
                             (flag 'list))))


(%autoprove lemma-for-forcing-logic.term-atblp-of-clause.factor
            (%clause.simple-term-induction flag x)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      forcing-logic.functionp-when-logic.base-evaluablep
                      not-equal-when-less
                      trichotomy-of-<
                      logic.formulap-when-not-consp))

(%autoprove forcing-logic.term-atblp-of-clause.factor
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-clause.factor)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-clause.factor-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-clause.factor)
                             (flag 'list))))


(%autoprove lemma-for-clause.factor-when-not-consp-of-assignment
            (%clause.simple-term-induction flag x)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      forcing-logic.functionp-when-logic.base-evaluablep
                      not-equal-when-less
                      trichotomy-of-<
                      logic.formulap-when-not-consp))

(%autoprove clause.factor-when-not-consp-of-assignment
            (%use (%instance (%thm lemma-for-clause.factor-when-not-consp-of-assignment)
                             (flag 'term))))

(%autoprove clause.factor-list-when-not-consp-of-assignment
            (%use (%instance (%thm lemma-for-clause.factor-when-not-consp-of-assignment)
                             (flag 'list))))


(%defprojection :list (clause.multifactor term x)
                :element (clause.factor term x))

(%autoprove forcing-logic.term-listp-of-clause.multifactor
            (%cdr-induction assignments))


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/factor")