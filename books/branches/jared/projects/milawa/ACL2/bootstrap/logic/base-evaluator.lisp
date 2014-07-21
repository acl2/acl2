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


(%autoadmit logic.initial-arity-table)

(%autoprove logic.arity-tablep-of-logic.initial-arity-table)

(%noexec logic.initial-arity-table)




(%autoadmit logic.base-evaluablep)

(%autoprove booleanp-of-logic.base-evaluablep
            (%enable default logic.base-evaluablep)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-true-listp-of-logic.function-args))

(%autoprove forcing-logic.functionp-when-logic.base-evaluablep
            (%enable default logic.base-evaluablep))

(%autoprove logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
            (%enable default logic.base-evaluablep)
            (%disable default forcing-lookup-of-logic.function-name))

(%autoprove lookup-logic.function-name-in-logic.initial-arity-table-when-logic.base-evaluablep
            (%enable default logic.base-evaluablep)
            (%disable default forcing-lookup-of-logic.function-name))

(%autoprove lemma-for-logic.term-atblp-when-logic.base-evaluablep
            ;; BOZO we shouldn't need this use hint
            (%use (%instance (%thm forcing-logic.term-atblp-of-logic.function)
                             (name fn)
                             (args args)
                             (atbl (logic.initial-arity-table)))))

(%autoprove logic.term-atblp-when-logic.base-evaluablep
            (%autorule logic.term-atblp-when-logic.base-evaluablep)
            (%enable default logic.base-evaluablep)
            ;; BOZO we shouldn't need this use hint, we should just be able to enable the lemma.
            (%use (%instance (%thm lemma-for-logic.term-atblp-when-logic.base-evaluablep)
                             (fn (logic.function-name term))
                             (args (logic.function-args term))))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.base-evaluablep-when-preliminary-fn-applied-to-constants
            (%enable default logic.base-evaluablep)
            (%auto)
            (%use (%instance (%thm logic.function-namep-when-lookup-in-logic.arity-tablep)
                             (x (logic.initial-arity-table))
                             (a fn))))

(%autoprove logic.base-evaluablep-of-logic.function-equal
            (%enable default logic.base-evaluablep logic.initial-arity-table))



(%autoadmit logic.base-evaluator)

(%autoprove forcing-logic.constantp-of-logic.base-evaluator
            (%enable default logic.base-evaluator))

(%autoprove forcing-logic.constantp-of-logic.base-evaluator-free)

(%autoprove logic.base-evaluator-of-logic.function-equal
            (%enable default logic.base-evaluator))

(%ensure-exactly-these-rules-are-missing "../../logic/base-evaluator")

