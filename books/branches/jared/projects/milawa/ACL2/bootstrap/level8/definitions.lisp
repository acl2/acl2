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
(%interactive)


(%autoadmit definitionp)

(%autoprove booleanp-of-definitionp
            (%enable default definitionp))

(%autoprove logic.formulap-when-definitionp
            (%enable default definitionp))

(%autoprove logic.fmtype-when-definitionp
            (%enable default definitionp))

(%autoprove logic.functionp-of-logic.=lhs-when-definitionp
            (%enable default definitionp))

(%autoprove logic.variable-listp-of-logic.function-args-of-logic.=lhs-when-definitionp
            (%enable default definitionp))

(%autoprove uniquep-of-logic.function-args-of-logic.=lhs-when-definitionp
            (%enable default definitionp))

(%autoprove subsetp-of-logic.term-vars-of-logic.=rhs-when-definitionp
            (%enable default definitionp))



(%deflist definition-listp (x)
          (definitionp x))

(%autoprove logic.formula-listp-when-definition-listp
            (%cdr-induction x))



(%autoadmit definition-list-lookup)

(%autoprove definition-list-lookup-when-not-consp
            (%restrict default definition-list-lookup (equal x 'x)))

(%autoprove definition-list-lookup-of-cons
            (%restrict default definition-list-lookup (equal x '(cons a x))))

(%autoprove definitionp-of-definition-list-lookup
            (%cdr-induction x))

(%autoprove logic.formula-atblp-of-definition-list-lookup
            (%cdr-induction x))

(%autoprove memberp-of-definition-list-lookup
            (%cdr-induction defs))

(%autoprove forcing-logic.fmtype-of-definition-list-lookup)

(%autoprove forcing-logic.function-name-of-logic.=lhs-of-definition-list-lookup
            (%cdr-induction defs))

(%autoprove forcing-logic.functionp-of-logic.=lhs-of-definition-list-lookup
            (%cdr-induction defs))

(%ensure-exactly-these-rules-are-missing "../../rewrite/definitions")



(%enable expensive-term/formula-inference
         logic.formulap-when-definitionp
         logic.formula-listp-when-definition-listp
         logic.functionp-of-logic.=lhs-when-definitionp
         logic.fmtype-when-definitionp)
