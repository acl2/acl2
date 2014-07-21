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

(%autoadmit logic.flag-substitute)
(%autoadmit logic.substitute)
(%autoadmit logic.substitute-list)


(%autoprove definition-of-logic.substitute
            (%enable default logic.substitute logic.substitute-list)
            (%restrict default logic.flag-substitute (equal x 'x)))

(%autoprove definition-of-logic.substitute-list
            (%enable default logic.substitute logic.substitute-list)
            (%restrict default logic.flag-substitute (equal x 'x)))

(%autoprove logic.flag-substitute-of-term
            (%enable default logic.substitute))

(%autoprove logic.flag-substitute-of-term-list
            (%enable default logic.substitute-list))

(%autoprove logic.substitute-when-malformed-cheap
            ;; BOZO this rule says it's cheap, but it doesn't have any backchain limits here or
            ;; in the ACL2 model!
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-list-when-not-consp
            (%restrict default definition-of-logic.substitute-list (equal x 'x)))

(%autoprove logic.substitute-list-of-cons
            (%restrict default definition-of-logic.substitute-list (equal x '(cons a x))))

(%defprojection :list (logic.substitute-list x sigma)
                :element (logic.substitute x sigma)
                :nil-preservingp t)



(%autoprove logic.substitute-when-logic.constantp
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-when-logic.variablep
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-when-logic.functionp-cheap
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-when-logic.lambdap-cheap
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.substitute-of-logic.function)

(%autoprove forcing-logic.function-name-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.function-args-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.substitute-of-logic.lambda
            ;; BOZO this should not be named `forcing` since there are no hyps
            (%disable default forcing-logic.termp-of-logic.lambda)
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.lambda-formals-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.lambda-body-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.lambda-actuals-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

