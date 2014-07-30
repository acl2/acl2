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
(include-book "terms")
(%interactive)



(%autoadmit logic.flag-subtermp)
(%autoadmit logic.subtermp)
(%autoadmit logic.subterm-of-somep)


(%autoprove definition-of-logic.subtermp
            (%enable default logic.subtermp logic.subterm-of-somep)
            (%restrict default logic.flag-subtermp (equal y 'y)))

(%autoprove definition-of-logic.subterm-of-somep
            (%enable default logic.subtermp logic.subterm-of-somep)
            (%restrict default logic.flag-subtermp (equal y 'y)))

(%autoprove logic.subterm-of-somep-when-not-consp
            (%restrict default definition-of-logic.subterm-of-somep (equal y 'x)))

(%autoprove logic.subterm-of-somep-of-cons
            (%restrict default definition-of-logic.subterm-of-somep (equal y '(cons b y))))

(%autoprove lemma-for-booleanp-of-logic.subtermp
            (%logic.term-induction flag y)
            (%restrict default definition-of-logic.subtermp (equal y 'y))
            (%disable default
                      forcing-true-listp-of-logic.function-args
                      forcing-true-listp-of-logic.lambda-actuals))


(%autoprove booleanp-of-logic.subtermp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.subtermp)
                             (flag 'term))))

(%autoprove booleanp-of-logic.subterm-of-somep
            (%use (%instance (%thm lemma-for-booleanp-of-logic.subtermp)
                             (flag 'list))))


(%autoprove logic.subterm-of-somep-when-memberp-is-logic.subtermp
            (%cdr-induction x))

(%autoprove logic.subterm-of-somep-when-memberp-is-logic.subtermp-alt)

(%autoprove logic.subtermp-is-reflexive
            (%restrict default definition-of-logic.subtermp (equal x 'x)))

(%autoprove lemma-for-logic.subtermp-is-transitive
            (%logic.term-induction flag z)
            (%disable default
                      forcing-true-listp-of-logic.function-args
                      forcing-true-listp-of-logic.lambda-actuals)
            (%auto)
            (%restrict default definition-of-logic.subtermp (memberp y '(y z)))
            ;; strategy reduces from 650M to 200M
            (%auto :strategy (cleanup split crewrite elim)))

(%autoprove logic.subtermp-is-transitive
            (%use (%instance (%thm lemma-for-logic.subtermp-is-transitive)
                             (flag 'term))))

(%autoprove logic.subtermp-is-transitive-two)

(%autoprove logic.subterm-of-somep-when-logic.subtermp-and-logic.subterm-of-somep
            (%use (%instance (%thm lemma-for-logic.subtermp-is-transitive)
                             (flag 'list))))

(%autoprove logic.subterm-of-somep-when-logic.subtermp-and-logic.subterm-of-somep-alt)



(%autoprove lemma-for-rank-when-logic.subtermp-weak
            (%logic.term-induction flag y)
            (%disable default
                      forcing-true-listp-of-logic.function-args
                      forcing-true-listp-of-logic.lambda-actuals)
            (%auto)
            (%restrict default definition-of-logic.subtermp (equal y 'y)))

(%autoprove rank-when-logic.subtermp-weak
            (%use (%instance (%thm lemma-for-rank-when-logic.subtermp-weak)
                             (flag 'term))))

(%autoprove rank-when-logic.subterm-of-somep
            (%use (%instance (%thm lemma-for-rank-when-logic.subtermp-weak)
                             (flag 'list))))

(%autoprove rank-when-logic.subterm-of-somep-weak)

(%autoprove rank-when-logic.subtermp
            (%restrict default definition-of-logic.subtermp (equal y 'y))
            (%auto)
            (%disable default rank-when-logic.subterm-of-somep)
            (%use (%instance (%thm rank-when-logic.subterm-of-somep) (x x) (y (logic.function-args y))))
            (%auto)
            (%use (%instance (%thm rank-when-logic.subterm-of-somep) (x x) (y (logic.lambda-actuals y)))))

(%autoprove logic.subtermp-is-weakly-antisymmetric
            (%disable default rank-when-logic.subtermp)
            (%use (%instance (%thm rank-when-logic.subtermp))))

(%autoprove logic.subtermp-of-logic.functionp
            (%restrict default definition-of-logic.subtermp (equal y '(logic.function fn args))))

(%autoprove logic.subtermp-of-logic.lambda
            (%restrict default definition-of-logic.subtermp (equal y '(logic.lambda xs b ts))))

(%autoprove logic.subterm-of-somep-of-list-fix (%cdr-induction x))
(%autoprove logic.subterm-of-somep-of-app      (%cdr-induction x))
(%autoprove logic.subterm-of-somep-of-rev      (%cdr-induction x))




(%deflist logic.all-subterm-of-somep (x others)
          (logic.subterm-of-somep x others))

(%autoprove logic.all-subterm-of-somep-when-not-consp-two (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-of-cons-two        (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-of-list-fix-two    (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-of-app-two         (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-of-app-two-alt     (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-of-rev-two         (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-is-reflexive       (%cdr-induction x))

(%autoprove logic.subterm-of-somep-when-subterm-and-logic.all-subterm-of-somep (%cdr-induction x))
(%autoprove logic.subterm-of-somep-when-subterm-and-logic.all-subterm-of-somep-alt)

(%autoprove logic.all-subterm-of-somep-is-transitive (%cdr-induction x))
(%autoprove logic.all-subterm-of-somep-is-transitive-alt)


(%ensure-exactly-these-rules-are-missing "../../logic/subtermp")

