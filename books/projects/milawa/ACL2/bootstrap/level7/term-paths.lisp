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
(include-book "term-tests")
(%interactive)


;; (clause.term-paths x)
;;
;; We walk down the term and create lists of all the if expressions we
;; encounter along the way.  I.e., these paths show you each set of choices you
;; would need to make in order to get to every tip of a term.

(%autoadmit clause.flag-term-paths)
(%autoadmit clause.term-paths)
(%autoadmit clause.term-paths-list)

(%autoprove definition-of-clause.term-paths
            (%restrict default clause.flag-term-paths (equal x 'x))
            (%enable default clause.term-paths clause.term-paths-list))

(%autoprove definition-of-clause.term-paths-list
            (%restrict default clause.flag-term-paths (equal x 'x))
            (%enable default clause.term-paths clause.term-paths-list))

(%autoprove clause.flag-term-paths-of-term-removal
            (%enable default clause.term-paths))

(%autoprove clause.flag-term-paths-of-list-removal
            (%enable default clause.term-paths-list))



(%autoprove clause.term-paths-when-logic.constantp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-logic.variablep
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-non-if-logic.functionp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-if-logic.functionp
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-logic.lambdap
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-when-degenerate
            (%restrict default definition-of-clause.term-paths (equal x 'x)))

(%autoprove clause.term-paths-list-when-not-consp
            (%restrict default definition-of-clause.term-paths-list (equal x 'x)))

(%autoprove clause.term-paths-list-of-cons
            (%restrict default definition-of-clause.term-paths-list (equal x '(cons a x))))

(%autoprove clause.term-paths-list-when-len-three)




(%create-theory clause.term-paths-openers)
(%enable clause.term-paths-openers
         clause.term-paths-when-logic.constantp
         clause.term-paths-when-logic.variablep
         clause.term-paths-when-non-if-logic.functionp
         clause.term-paths-when-bad-args-logic.functionp
         clause.term-paths-when-if-logic.functionp
         clause.term-paths-when-logic.lambdap
         clause.term-paths-when-degenerate
         clause.term-paths-list-when-not-consp
         clause.term-paths-list-of-cons
         clause.term-paths-list-when-len-three)



(%autoprove lemma-for-clause.term-paths-when-clause.simple-termp
            (%clause.simple-term-induction flag x))

(%autoprove clause.term-paths-when-clause.simple-termp
            (%use (%instance (%thm lemma-for-clause.term-paths-when-clause.simple-termp)
                             (flag 'term))))

(%autoprove clause.term-paths-list-when-clause.simple-term-listp
            (%use (%instance (%thm lemma-for-clause.term-paths-when-clause.simple-termp)
                             (flag 'list))))



(local (%create-theory common-disables))
(local (%enable common-disables
                expensive-arithmetic-rules
                expensive-arithmetic-rules-two
                type-set-like-rules
                formula-decomposition
                expensive-term/formula-inference
                unusual-subsetp-rules
                unusual-memberp-rules
                unusual-consp-rules
                usual-consp-rules
                same-length-prefixes-equal-cheap
                clause.term-paths-openers
                subsetp-when-not-consp-two
                subsetp-when-not-consp
                app-when-not-consp-two
                app-when-not-consp
                logic.term-list-listp-when-not-consp
                clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                logic.term-listp-when-subset-of-somep-alt
                logic.term-list-listp-when-all-superset-of-somep-alt))

(%autoprove lemma-for-forcing-logic.term-list-listp-of-clause.term-paths
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-paths-openers
                     unusual-consp-rules))

(%autoprove forcing-logic.term-list-listp-of-clause.term-paths
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-listp-of-clause.term-paths)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-listp-of-clause.term-paths-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-list-listp-of-clause.term-paths)
                             (flag 'list))))




(%autoprove lemma-for-forcing-consp-of-clause.term-paths
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-paths-openers
                     unusual-consp-rules))

(%autoprove forcing-consp-of-clause.term-paths
            (%use (%instance (%thm lemma-for-forcing-consp-of-clause.term-paths)
                             (flag 'term))))

(%autoprove forcing-consp-of-clause.term-paths-list
            (%use (%instance (%thm lemma-for-forcing-consp-of-clause.term-paths)
                             (flag 'list))))



(%autoprove disjoint-from-nonep-of-clause.term-paths-when-memberp
            (%cdr-induction x)
            (%disable default common-disables))


(%autoprove lemma-for-disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths
            (%clause.simple-term-induction flag x)
            (%disable default common-disables)
            (%auto)
            (%enable default
                     clause.term-paths-openers
                     unusual-consp-rules))

(%autoprove disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths
            (%use (%instance (%thm lemma-for-disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths)
                             (flag 'term))))

(%autoprove disjoint-from-nonep-of-clause.simple-tests-list-and-clause.term-paths-list
            (%use (%instance (%thm lemma-for-disjoint-from-nonep-of-clause.simple-tests-and-clause.term-paths)
                             (flag 'list))))

