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
(include-book "depth-3-special")
(%interactive)

(%autoprove lemma-for-consp-of-clause.simple-tests
            (%clause.simple-term-induction flag x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))

(%autoprove consp-of-clause.simple-tests
            (%use (%instance (%thm lemma-for-consp-of-clause.simple-tests)
                             (flag 'term))))

(%autoprove consp-of-clause.simple-tests-list
            (%use (%instance (%thm lemma-for-consp-of-clause.simple-tests)
                             (flag 'list))))


(%autoprove lemma-for-clause.simple-tests-when-not-clause.simple-termp-under-iff
            (%clause.simple-term-induction flag x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))

(%autoprove clause.simple-tests-when-not-clause.simple-termp-under-iff
            (%use (%instance (%thm lemma-for-clause.simple-tests-when-not-clause.simple-termp-under-iff)
                             (flag 'term))))

(%autoprove clause.simple-tests-list-when-not-clause.simple-term-listp-under-iff
            (%use (%instance (%thm lemma-for-clause.simple-tests-when-not-clause.simple-termp-under-iff)
                             (flag 'list))))



(%autoprove forcing-logic.term-listp-of-firstn)

(%autoprove forcing-logic.term-list-atblp-of-firstn)





(%autoadmit clause.limlift-term1)

(%autoprove forcing-logic.termp-of-car-of-clause.limlift-term1
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove forcing-natp-of-cdr-of-clause.limlift-term1
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-car-of-clause.lift1
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove car-of-clause.lift1-when-clause.lifted-termp
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.lift1-when-clause.lifted-termp
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.limlift-term1-never-increases
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.limlift-term1-stays-at-zero
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))

(%autoprove cdr-of-clause.limlift-term1-usually-decreases
            (%autoinduct clause.limlift-term1 x k)
            (%restrict default clause.limlift-term1 (equal x 'x)))





(%autoadmit clause.limlift-term)

(%autoprove forcing-logic.termp-of-clause.limlift-term
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal k 'k)))

(%autoprove forcing-logic.term-atblp-of-clause.limlift-term
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal k 'k)))

(%autoprove clause.limlift-term-when-clause.simple-termp
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal k 'k)))



(%defprojection :list (clause.limlift-term-list x k)
                :element (clause.limlift-term x k))

(%autoprove forcing-logic.term-listp-of-clause.limlift-term-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.limlift-term-list
            (%cdr-induction x))

(%autoprove clause.limlift-term-list-when-clause.simple-term-listp
            (%cdr-induction x))



(%defprojection :list (clause.limlift-term-list-list x k)
                :element (clause.limlift-term-list x k))

(%autoprove forcing-logic.term-list-listp-of-clause.limlift-term-list-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.limlift-term-list-list
            (%cdr-induction x))

(%autoprove clause.limlift-term-list-list-when-clause.simple-term-list-listp
            (%cdr-induction x))

(%autoprove cons-listp-of-clause.limlift-term-list-list
            (%cdr-induction x))
