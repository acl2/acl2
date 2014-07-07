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


(%autoadmit rewrite.syntaxp-arity-table)

(%autoprove logic.arity-tablep-of-rewrite.syntaxp-arity-table)
(%noexec rewrite.syntaxp-arity-table)


(%autoadmit rewrite.syntaxp-base-evaluablep)

(%autoprove booleanp-of-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep)
            (%forcingp nil))

(%autoprove forcing-logic.functionp-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep))

(%autoprove logic.constant-listp-of-logic.function-args-when-rewrite.syntaxp-base-evaluablep
            (%enable default
                     rewrite.syntaxp-base-evaluablep
                     logic.function-args))

(%autoprove lookup-logic.function-name-in-rewrite.syntaxp-arity-table-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep))

(%autoprove lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-arity-table))

(%autoprove logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep)
            ;; now looping with new reweriter changes??
            (%disable default len-when-tuplep)
            (%use (%instance (%thm lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep)
                             (fn (logic.function-name term))
                             (args (logic.function-args term)))))

(%autoprove rewrite.syntaxp-base-evaluablep-when-preliminary-fn-applied-to-constants
            (%enable default
                     rewrite.syntaxp-base-evaluablep
                     rewrite.syntaxp-arity-table))

(%autoprove rewrite.syntaxp-base-evaluablep-of-logic.function-equal
            (%enable default
                     rewrite.syntaxp-base-evaluablep
                     rewrite.syntaxp-arity-table))



(%autoadmit rewrite.syntaxp-base-evaluator)

(%autoprove forcing-logic.constantp-of-rewrite.syntaxp-base-evaluator
            (%enable default
                     rewrite.syntaxp-base-evaluator))

(%autoprove forcing-logic.constantp-of-rewrite.syntaxp-base-evaluator-free)

(%autoprove rewrite.syntaxp-base-evaluator-of-logic.function-equal
            (%enable default rewrite.syntaxp-base-evaluator))



(%autoadmit rewrite.flag-syntaxp-evaluator)

(%autoadmit rewrite.syntaxp-evaluator)
(%autoadmit rewrite.syntaxp-evaluator-list)

(%autoprove definition-of-rewrite.syntaxp-evaluator
            (%enable default rewrite.syntaxp-evaluator rewrite.syntaxp-evaluator-list)
            (%restrict default rewrite.flag-syntaxp-evaluator (equal x 'x)))

(%autoprove definition-of-rewrite.syntaxp-evaluator-list
            (%enable default rewrite.syntaxp-evaluator rewrite.syntaxp-evaluator-list)
            (%restrict default rewrite.flag-syntaxp-evaluator (equal x 'x)))

(%autoprove rewrite.flag-syntaxp-evaluator-when-term
            (%enable default rewrite.syntaxp-evaluator))

(%autoprove rewrite.flag-syntaxp-evaluator-when-list
            (%enable default rewrite.syntaxp-evaluator-list))

(%autoprove rewrite.syntaxp-evaluator-list-when-not-consp
            (%restrict default definition-of-rewrite.syntaxp-evaluator-list (equal x 'x)))

(%autoprove rewrite.syntaxp-evaluator-list-of-cons
            (%restrict default definition-of-rewrite.syntaxp-evaluator-list (equal x '(cons a x))))

(%autoprove true-listp-of-rewrite.syntaxp-evaluator-list
            (%cdr-induction x))

(%autoprove forcing-len-of-cdr-of-rewrite.syntaxp-evaluator-list
            (%cdr-induction x))

(%autoprove consp-of-rewrite.syntaxp-evaluator-list
            (%cdr-induction x))

(%autoprove lemma-for-forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator
            (%autoinduct rewrite.flag-syntaxp-evaluator flag x defs n)
            (%disable default
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      expensive-term/formula-inference)
            (%auto)
            (%restrict default definition-of-rewrite.syntaxp-evaluator (equal x 'x))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator
            (%use (%instance (%thm lemma-for-forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator)
                             (flag 'term))))

(%autoprove forcing-logic.constant-listp-of-cdr-of-rewrite.syntaxp-evaluator-list
            (%use (%instance (%thm lemma-for-forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator)
                             (flag 'list))))

