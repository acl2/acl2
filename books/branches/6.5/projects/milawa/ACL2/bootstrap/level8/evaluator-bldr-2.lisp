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
(include-book "evaluator-bldr")
(%interactive)

(local (%enable default lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr))

(encapsulate
 ()
 (local (%max-proof-size 600000000))
 (%autoprove lemma-for-forcing-logic.proofp-of-generic-evaluator-bldr
             (%flag-generic-evaluator-induction flag x defs n)
             (%disable default
                       formula-decomposition
                       expensive-term/formula-inference
                       expensive-arithmetic-rules
                       expensive-arithmetic-rules-two
                       expensive-subsetp-rules
                       type-set-like-rules
                       forcing-logic.function-of-logic.function-name-and-logic.function-args
                       forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                       forcing-lookup-of-logic.function-name
                       same-length-prefixes-equal-cheap
                       definitionp-when-memberp-of-definition-listp
                       definition-list-lookup-when-not-consp)
             (%auto :strategy (split urewrite))
             (%forcingp nil)
             (%crewrite default)
             (%restrict default definition-of-generic-evaluator (equal x 'x))
             (%restrict default definition-of-generic-evaluator-bldr (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list-bldr (equal x 'x))
             (%auto :strategy (split urewrite))
             (%crewrite default)
             (%forcingp t)
             (%enable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules
                      forcing-lookup-of-logic.function-name)
             (%disable default
                       logic.termp-when-logic.formulap
                       logic.termp-when-invalid-maybe-expensive
                       logic.formulap-when-logic.termp
                       logic.formula-listp-when-definition-listp
                       consp-when-logic.lambdap-cheap
                       consp-when-logic.functionp-cheap
                       consp-of-car-when-none-consp
                       consp-of-car-when-cons-listp
                       logic.substitute-when-malformed-cheap
                       logic.lambdap-when-not-anything-else-maybe-expensive)
             (%cheapen default
                       logic.substitute-when-logic.constantp
                       logic.substitute-when-logic.variablep
                       logic.constantp-when-logic.variablep
                       logic.variablep-when-logic.constantp
                       logic.constantp-when-logic.functionp)
             (%auto :strategy (split cleanup urewrite crewrite elim))))

(%autoprove forcing-logic.proofp-of-generic-evaluator-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-generic-evaluator-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.proof-listp-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-generic-evaluator-bldr)
                             (flag 'list))))
