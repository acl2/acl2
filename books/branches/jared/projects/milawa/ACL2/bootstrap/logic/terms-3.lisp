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
(include-book "terms-2")
(include-book "terms-3-functionp")
(include-book "terms-3-lambdap")
(include-book "terms-3-term-vars")
(include-book "terms-3-term-list-listp")
(include-book "terms-3-arity-tablep")
(%interactive)



(%autoprove logic.functionp-when-logic.lambdap-cheap
            (%enable default logic.lambdap logic.functionp))

(%autoprove logic.lambdap-when-logic.functionp-cheap)

(%autoprove logic.functionp-of-logic.lambda)

(%autoprove logic.function-namep-of-car-when-logic.termp-and-not-logic.variablep
            (%enable default logic.functionp logic.constantp)
            (%restrict default definition-of-logic.termp (equal x 'x)))

(%autoprove logic.lambdap-when-not-anything-else-maybe-expensive
            (%enable default logic.lambdap logic.functionp)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil))

(%autoprove logic.termp-when-invalid-maybe-expensive)

(%autoprove logic.functionp-when-not-other-stuff-cheap
            (%enable default logic.lambdap logic.functionp)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil))

(%autoprove logic.lambdap-when-not-other-stuff-cheap)



(%autoprove logic.term-vars-when-function-call
            (%enable default logic.function-args)
            (%restrict default definition-of-logic.term-vars (equal x 'x))
            (%betamode nil))

(%autoprove logic.term-vars-when-logic.lambda
            (%enable default logic.lambdap logic.lambda-actuals)
            (%restrict default definition-of-logic.term-vars (equal x 'x))
            (%betamode nil))


(%autoprove lemma-for-forcing-logic.variable-listp-of-logic.term-vars
            (%logic.term-induction flag x)
            ;; This rule is really expensive, taking 716 frames/try when it's enabled
            (local (%disable default logic.variable-listp-of-subsetp-when-logic.variable-listp))
            ;; These rules cause problems with forcing
            (local (%disable default
                             FORCING-TRUE-LISTP-OF-LOGIC.FUNCTION-ARGS
                             FORCING-LOGIC.TERMP-OF-LOGIC.LAMBDA-BODY
                             FORCING-TRUE-LISTP-OF-LOGIC.LAMBDA-ACTUALS))
            (%auto :strategy (cleanup split crewrite elim)))

(%autoprove forcing-logic.variable-listp-of-logic.term-vars
            (%use (%instance (%thm lemma-for-forcing-logic.variable-listp-of-logic.term-vars) (flag 'term))))

(%autoprove forcing-logic.variable-listp-of-logic.term-list-vars
            (%use (%instance (%thm lemma-for-forcing-logic.variable-listp-of-logic.term-vars) (flag 'list))))



(%autoprove logic.term-listp-when-subset-of-somep
            (%cdr-induction x))

(%autoprove logic.term-listp-when-subset-of-somep-alt)

(%autoprove logic.term-list-listp-when-all-superset-of-somep
            (%cdr-induction x))

(%autoprove logic.term-list-listp-when-all-superset-of-somep-alt)

(%autoprove forcing-logic.term-list-listp-of-remove-supersets1
            (%autoinduct remove-supersets1))

(%autoprove forcing-logic.term-list-listp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove forcing-logic.term-list-listp-of-remove-duplicates-list
            (%cdr-induction x))



(%autoadmit logic.term-list-list-vars)

(%autoprove definition-of-logic.term-list-list-vars
            (%enable default logic.term-list-list-vars)
            (%restrict default logic.fast-term-list-list-vars (equal x 'x)))

(%autoprove logic.term-list-list-vars-when-not-consp
            (%restrict default definition-of-logic.term-list-list-vars (equal x 'x)))

(%autoprove logic.term-list-list-vars-of-cons
            (%restrict default definition-of-logic.term-list-list-vars (equal x '(cons a x))))

(%autoprove true-listp-of-logic.term-list-list-vars
            (%cdr-induction x))

(%autoprove forcing-logic.variable-listp-of-logic.term-list-list-vars
            (%cdr-induction x))
