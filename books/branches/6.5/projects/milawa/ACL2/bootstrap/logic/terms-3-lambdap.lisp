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
(%interactive)


(%autoadmit logic.lambdap)
(%autoadmit logic.lambda)
(%autoadmit logic.lambda-formals)
(%autoadmit logic.lambda-body)
(%autoadmit logic.lambda-actuals)


(%autoprove booleanp-of-logic.lambdap
            (%enable default logic.lambdap))

(%autoprove consp-when-logic.lambdap-cheap
            (%enable default logic.lambdap))

(%autoprove logic.variablep-when-logic.lambdap-cheap
            (%enable default logic.lambdap logic.variablep))

(%autoprove logic.constantp-when-logic.lambdap-cheap
            (%enable default logic.lambdap logic.constantp))

(%noexec logic.lambda)

(%autoprove consp-of-logic.lambda
            (%enable default logic.lambda))

(%autoprove logic.lambda-under-iff
            (%enable default logic.lambda))

(%autoprove logic.constantp-of-logic.lambda
            (%enable default logic.lambda logic.constantp))

(%autoprove logic.variablep-of-logic.lambda
            (%enable default logic.lambda logic.variablep))

(%autoprove forcing-logic.termp-of-logic.lambda
            (%enable default logic.lambda)
            (%restrict default definition-of-logic.termp (equal x '(cons (cons 'lambda (cons formals (cons body 'nil))) actuals)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambdap-of-logic.lambda
            (%enable default logic.lambdap logic.lambda))

(%autoprove equal-of-logic.lambda-and-logic.lambda
            (%enable default logic.lambda))

(%autoprove forcing-true-listp-of-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.variable-listp-of-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-uniquep-of-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambda-formals-of-logic.lambda
            (%enable default logic.lambda-formals logic.lambda))





(%autoprove forcing-logic.termp-of-logic.lambda-body
            (%enable default logic.lambdap logic.lambda-body)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambda-body-of-logic.lambda
            (%enable default logic.lambda-body logic.lambda))

(%autoprove rank-of-logic.lambda-body
            (%enable default logic.lambda-body))

(%autoprove forcing-subsetp-of-logic.term-vars-of-logic.lambda-body-with-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-body logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-true-listp-of-logic.lambda-actuals
            (%enable default logic.lambdap logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.term-listp-of-logic.lambda-actuals
            (%enable default logic.lambdap logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambda-actuals-of-logic.lambda
            (%enable default logic.lambda-actuals logic.lambda))






(%autoprove forcing-equal-lens-of-logic.lambda-formals-and-logic.lambda-actuals
            (%enable default logic.lambdap logic.lambda-formals logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.lambda-of-logic.lambda-formals-body-and-actuals
            (%enable default logic.lambdap logic.lambda logic.lambda-formals logic.lambda-body logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%restrict default tuplep (or (equal n ''3) (equal n ''2) (equal n ''1) (equal n ''0)))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.lambda-of-logic.lambda-formals-body-and-actuals-free)

(%autoprove rank-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove rank-of-first-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove rank-of-second-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove rank-of-third-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove logic.lambdap-when-consp-of-car-cheap
            (%enable default logic.lambdap))

