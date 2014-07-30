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
(include-book "proofp")
(%interactive)


(%autoadmit logic.appeal-identity)

(%autoprove logic.appeal-identity-under-iff
            (%enable default logic.appeal-identity))

(%autoprove logic.method-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.method))

(%autoprove logic.conclusion-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.conclusion))

(%autoprove logic.subproofs-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.subproofs))

(%autoprove logic.extras-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.extras))

(local (%disable default forcing-true-listp-of-logic.subproofs))

(%autoprove logic.axiom-okp-of-logic.appeal-identity
            (%enable default logic.axiom-okp))

(%autoprove logic.theorem-okp-of-logic.appeal-identity
            (%enable default logic.theorem-okp))

(%autoprove logic.propositional-schema-okp-of-logic.appeal-identity
            (%enable default logic.propositional-schema-okp))

(%autoprove logic.functional-equality-okp-of-logic.appeal-identity
            (%enable default logic.functional-equality-okp))

(%autoprove logic.expansion-okp-of-logic.appeal-identity
            (%enable default logic.expansion-okp))

(%autoprove logic.contraction-okp-of-logic.appeal-identity
            (%enable default logic.contraction-okp))

(%autoprove logic.associativity-okp-of-logic.appeal-identity
            (%enable default logic.associativity-okp))

(%autoprove logic.cut-okp-of-logic.appeal-identity
            (%enable default logic.cut-okp))

(%autoprove logic.instantiation-okp-of-logic.appeal-identity
            (%enable default logic.instantiation-okp))

(%autoprove logic.beta-reduction-okp-of-logic.appeal-identity
            (%enable default logic.beta-reduction-okp))

(%autoprove logic.induction-okp-of-logic.appeal-identity
            (%enable default logic.induction-okp))

(%autoprove logic.base-eval-okp-of-logic.appeal-identity
            (%enable default logic.base-eval-okp))

(%autoprove logic.appeal-step-okp-of-logic.appeal-identity
            (%enable default logic.appeal-step-okp))

(%autoprove logic.appealp-of-logic.appeal-identity
            (%restrict default definition-of-logic.appealp (equal x 'x))
            (%enable default logic.appeal-identity))

(%autoprove logic.proofp-of-logic.appeal-identity
            (%restrict default definition-of-logic.proofp (or (equal x '(logic.appeal-identity x))
                                                              (equal x 'x))))

(%ensure-exactly-these-rules-are-missing "../../logic/appeal-identity"
                                         logic.skip-okp-of-logic.appeal-identity)


