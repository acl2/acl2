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
(include-book "terms-3")
(%interactive)


(%autoadmit logic.flag-term-atblp)
(%autoadmit logic.term-atblp)
(%autoadmit logic.term-list-atblp)

(%autoprove definition-of-logic.term-atblp
            (%enable default logic.term-atblp logic.term-list-atblp)
            (%restrict default logic.flag-term-atblp (equal x 'x)))

(%autoprove definition-of-logic.term-list-atblp
            (%enable default logic.term-atblp logic.term-list-atblp)
            (%restrict default logic.flag-term-atblp (equal x 'x)))

(%autoprove logic.term-list-atblp-when-not-consp
            (%restrict default definition-of-logic.term-list-atblp (equal x 'x)))

(%autoprove logic.term-list-atblp-of-cons
            (%restrict default definition-of-logic.term-list-atblp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-logic.term-atblp
            (%logic.term-induction flag x)
            (local (%restrict default definition-of-logic.term-atblp (equal x 'x)))
            (%auto :strategy (cleanup split crewrite elim)))

(%autoprove booleanp-of-logic.term-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.term-atblp) (flag 'term))))

(%autoprove booleanp-of-logic.term-list-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.term-atblp) (flag 'list))))

(%autoprove logic.term-atblp-of-nil
            (%restrict default definition-of-logic.term-atblp (equal x ''nil)))

(%deflist logic.term-list-atblp (x atbl)
          (logic.term-atblp x atbl))

(%deflist logic.term-list-list-atblp (x atbl)
          (logic.term-list-atblp x atbl))



(%autoprove logic.term-atblp-when-logic.variablep
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove logic.term-atblp-when-logic.constantp
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove logic.term-list-atblp-when-logic.constant-listp
            (%cdr-induction x))

(%autoprove logic.term-list-atblp-when-logic.variable-listp
            (%cdr-induction x))

(%autoprove forcing-logic.term-atblp-of-logic.function
            (%restrict default definition-of-logic.term-atblp (equal x '(logic.function name args))))

(%autoprove forcing-logic.term-atblp-of-logic.lambda
            (%disable default logic.lambdap-when-not-anything-else-maybe-expensive)
            (%restrict default definition-of-logic.term-atblp (equal x '(logic.lambda formals body actuals))))

(%autoprove forcing-logic.term-list-atblp-of-logic.function-args
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove forcing-logic.term-list-atblp-of-logic.lambda-actuals
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-logic.lambda-body
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove logic.term-list-atblp-of-strip-firsts-when-logic.term-list-listp
            (%cdr-induction x))

(%autoprove forcing-lookup-of-logic.function-name
            (%disable default forcing-logic.term-list-atblp-of-logic.function-args)
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove forcing-lookup-of-logic.function-name-free)



(%autoprove lemma-1-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table)

(%autoprove lemma-2-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
            ;; BOZO previously we were using a backchain limit on this submapp
            ;; call in the Milawa-proof only.  Do we need to have that or is
            ;; the proof still reasonable?
            (%use (%instance (%thm equal-of-lookups-when-submapp) (a name) (x atbl) (y atbl2))))

(%autoprove lemma-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
            (%logic.term-induction flag x)
            (%auto :strategy (cleanup split))
            (%enable default
                     lemma-1-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
                     lemma-2-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table)
            (%forcingp nil)
            (%auto)
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))

(%autoprove logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
            (%use (%instance (%thm lemma-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table) (flag 'term))))

(%autoprove logic.term-list-atblp-when-logic.term-list-atblp-in-smaller-arity-table
            (%use (%instance (%thm lemma-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table) (flag 'list))))

(%autoprove logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table-alt)

(%autoprove logic.term-list-atblp-when-logic.term-list-atblp-in-smaller-arity-table-alt)

(%autoprove logic.term-atblp-when-malformed-cheap
            (%restrict default definition-of-logic.term-atblp (equal x 'x)))


(%ensure-exactly-these-rules-are-missing
 "../../logic/terms"
 ;; BOZO somehow we didn't need this.  Localize it in ACL2 or get rid of it in ACL2?
 LEMMA-FOR-FORCING-LOOKUP-OF-LOGIC.FUNCTION-NAME)

