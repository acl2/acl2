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
(include-book "depth-2-deepest")
(%interactive)

(%autoadmit clause.special-assignment)

(%autoprove clause.special-assignment-when-not-consp
            (%restrict default clause.special-assignment (equal assignments 'assignments)))

(%autoprove clause.special-assignment-of-cons
            (%restrict default clause.special-assignment (equal assignments '(cons a assignments))))

(%autoprove memberp-of-clause.special-assignment
            (%cdr-induction assignments))

(%autoprove forcing-logic.termp-of-clause.deepest
            (%cdr-induction x))

(%autoprove clause.special-assignment-of-clause.multifactor
            (%cdr-induction assignments)
            (%enable default clause.depth-list-redefinition)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      same-length-prefixes-equal-cheap)
            (%cheapen default
                      clause.depth-when-clause.simple-termp
                      clause.depth-list-when-clause.simple-term-listp
                      clause.simple-termp-when-memberp-of-clause.simple-term-listp
                      clause.simple-term-listp-of-cdr-when-clause.simple-term-listp
                      clause.simple-termp-of-car-when-clause.simple-term-listp)
            (%auto)
            (%enable default
                     expensive-arithmetic-rules-two
                     expensive-arithmetic-rules
                     type-set-like-rules))



(%autoadmit clause.deepest-after-factoring)

(%autoprove clause.deepest-after-factoring-when-not-consp
            (%restrict default clause.deepest-after-factoring (equal x 'x)))

(%autoprove clause.deepest-after-factoring-of-cons
            (%restrict default clause.deepest-after-factoring (equal x '(cons a x))))

(%autoprove forcing-logic.termp-of-clause.deepest-after-factoring
            (%cdr-induction x))

(%autoprove memberp-of-clause.deepest-after-factoring
            (%cdr-induction x))

(%autoprove clause.deepest-of-clause.factor-list
            (%cdr-induction x)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))

(%autoprove disjoint-from-nonep-of-clause.term-paths-of-clause.deepest-after-factoring
            (%disable default disjoint-from-nonep-of-clause.term-paths-when-memberp)
            (%use (%instance (%thm disjoint-from-nonep-of-clause.term-paths-when-memberp)
                             (a (clause.deepest-after-factoring x assignment))
                             (x x))))


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/depth")
