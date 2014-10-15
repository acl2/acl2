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
(include-book "factor-bldr")
(%interactive)

(%autoadmit logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas)

(%autoprove logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas-removal
            (%cdr-induction x)
            (%restrict default logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas (equal x 'x))
            (%forcingp nil))



(%autoadmit clause.factor-bldr-okp)

(%autoadmit clause.factor-bldr-high)

(local (%enable default clause.factor-bldr-okp))

(%autoprove booleanp-of-clause.factor-bldr-okp)

(%autoprove clause.factor-bldr-okp-of-logic.appeal-identity)

(%autoprove lemma-1-for-soundness-of-clause.factor-bldr-okp)

(%autoprove lemma-2-for-soundness-of-clause.factor-bldr-okp)

(%autoprove forcing-soundness-of-clause.factor-bldr-okp
            (%enable default
                     lemma-1-for-soundness-of-clause.factor-bldr-okp
                     lemma-2-for-soundness-of-clause.factor-bldr-okp)
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (clause.factor-bldr (first (logic.extras x))
                                                    (second (logic.extras x)))))))

(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/factor-bldr")