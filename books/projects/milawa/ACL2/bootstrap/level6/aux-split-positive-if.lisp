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
(include-book "aux-split")
(%interactive)

;; speed hint
(local (%disable default
                 AGGRESSIVE-EQUAL-OF-LOGIC.PNOTS
                 AGGRESSIVE-EQUAL-OF-LOGIC.PEQUALS
                 AGGRESSIVE-EQUAL-OF-LOGIC.PORS
                 FORCING-LOGIC.FUNCTION-OF-LOGIC.FUNCTION-NAME-AND-LOGIC.FUNCTION-ARGS-FREE
                 LOGIC.TERM-LISTP-OF-SUBSETP-WHEN-LOGIC.TERM-LISTP
                 LOGIC.TERM-LISTP-WHEN-LOGIC.VARIABLE-LISTP-CHEAP
                 FORCING-LOGIC.DISJOIN-FORMULAS-OF-TWO-ELEMENT-LIST
                 LOGIC.DISJOIN-FORMULAS-WHEN-NOT-CONSP

                 CONSP-WHEN-LOGIC.LAMBDAP-CHEAP
                 LOGIC.FUNCTIONP-WHEN-LOGIC.LAMBDAP-CHEAP
                 LOGIC.TERMP-WHEN-INVALID-MAYBE-EXPENSIVE

                 logic.termp-when-logic.formulap
                 same-length-prefixes-equal-cheap
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 unusual-subsetp-rules
                 car-when-not-consp
                 cdr-when-not-consp
                 type-set-like-rules
                 unusual-memberp-rules
                 ))

(%autoadmit clause.aux-split-positive-if)

(%autoprove forcing-logic.appealp-of-clause.aux-split-positive-if
            (%enable default
                     logic.term-formula
                     clause.aux-split-goal
                     clause.aux-split-positive-if))

(%autoprove forcing-logic.conclusion-of-clause.aux-split-positive-if
            (%enable default
                     logic.term-formula
                     clause.aux-split-goal
                     clause.aux-split-positive-if))

(%autoprove forcing-logic.proofp-of-clause.aux-split-positive-if
            (%enable default
                     logic.term-formula
                     clause.aux-split-goal
                     clause.aux-split-positive-if))

