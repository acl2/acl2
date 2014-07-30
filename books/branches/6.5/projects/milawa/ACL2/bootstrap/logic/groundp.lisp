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
(include-book "substitute-term")
(%interactive)


(%autoadmit logic.flag-groundp)
(%autoadmit logic.groundp)
(%autoadmit logic.ground-listp)

(%autoprove definition-of-logic.groundp
            (%restrict default logic.flag-groundp (equal x 'x))
            (%enable default logic.groundp)
            (%enable default logic.ground-listp))

(%autoprove definition-of-logic.ground-listp
            (%restrict default logic.flag-groundp (equal x 'x))
            (%enable default logic.groundp)
            (%enable default logic.ground-listp))


(%autoprove logic.ground-listp-when-not-consp
            (%restrict default definition-of-logic.ground-listp (equal x 'x)))

(%autoprove logic.ground-listp-of-cons
            (%restrict default definition-of-logic.ground-listp (equal x '(cons a x))))

(%autoprove booleanp-of-logic.ground-listp
            (%cdr-induction x))

(%autoprove booleanp-of-logic.groundp
            (%restrict default definition-of-logic.groundp (equal x 'x)))

(%autoprove logic.groundp-when-logic.constantp
            (%restrict default definition-of-logic.groundp (equal x 'x)))

(%autoprove forcing-logic.ground-listp-of-logic.function-args-when-logic.groundp
            (%restrict default definition-of-logic.groundp (equal x 'x)))

(%autoprove forcing-logic.ground-listp-of-logic.lambda-actuals-when-logic.groundp
            (%restrict default definition-of-logic.groundp (equal x 'x)))



(%deflist logic.ground-listp (x)
          (logic.groundp x))

(%autoprove logic.ground-listp-when-logic.constant-listp
            (%cdr-induction x))

(%autoprove forcing-logic.groundp-of-logic.function
            (%restrict default definition-of-logic.groundp (equal x '(logic.function name args))))

(%autoprove forcing-logic.groundp-of-logic.lambda
            (%restrict default definition-of-logic.groundp (equal x '(logic.lambda formals body actuals))))



(%autoprove lemma-2-for-forcing-logic.groundp-of-logic.substitute
            (%cdr-induction sigma))

(%autoprove lemma-for-forcing-logic.groundp-of-logic.substitute
            (%logic.term-induction flag x)
            (%enable default lemma-2-for-forcing-logic.groundp-of-logic.substitute))

(%autoprove forcing-logic.groundp-of-logic.substitute
            (%use (%instance (%thm lemma-for-forcing-logic.groundp-of-logic.substitute) (flag 'term))))

(%autoprove forcing-logic.ground-listp-of-logic.substitute-list
            (%use (%instance (%thm lemma-for-forcing-logic.groundp-of-logic.substitute) (flag 'list))))

(%autoprove forcing-logic.groundp-when-logic.constant-listp-of-logic.function-args
            (%use (%instance (%thm forcing-logic.groundp-of-logic.function)
                             (name (logic.function-name term))
                             (args (logic.function-args term)))))


(%autoprove forcing-logic.groundp-when-logic.constant-listp-of-logic.lambda-actuals
            (%use (%instance (%thm forcing-logic.groundp-of-logic.lambda)
                             (formals (logic.lambda-formals term))
                             (body    (logic.lambda-body term))
                             (actuals (logic.lambda-actuals term)))))

(%ensure-exactly-these-rules-are-missing "../../logic/groundp")
