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
(include-book "substitute-formula")
(%interactive)


(%autoadmit logic.term-formula)

(%autoprove forcing-logic.formulap-of-logic.term-formula
            (%enable default logic.term-formula))

(%autoprove forcing-logic.formula-atblp-of-logic.term-formula
            (%enable default logic.term-formula))

(%autoprove logic.substitute-formula-of-logic.term-formula
            (%enable default logic.term-formula))



(%defprojection :list (logic.term-list-formulas x)
                :element (logic.term-formula x))

(%autoprove redefinition-of-logic.term-list-formulas
            (%cdr-induction x)
            (%enable default logic.term-formula))

(%autoprove forcing-logic.formula-listp-of-logic.term-list-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.term-list-formulas
            (%cdr-induction x))

(%autoprove memberp-of-logic.term-formula-and-logic.term-list-formulas
            (%cdr-induction x)
            (%enable default logic.term-formula))

(%autoprove memberp-of-logic.pnot-of-logic.pequal-nil-in-logic.term-list-formulas
            (%cdr-induction x)
            (%enable default logic.term-formula))

(%autoprove subsetp-of-logic.term-list-formulas-and-logic.term-list-formulas
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.term-list-formulas
            (%cdr-induction x))




(%defprojection :list (logic.term-list-list-formulas x)
                :element (logic.term-list-formulas x))

(%autoprove forcing-logic.formula-list-listp-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-list-atblp-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove cons-listp-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove supserset-of-somep-of-logic.term-list-formulas-and-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove all-superset-of-somep-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove logic.term-list-list-formulas-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-list-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove logic.term-list-list-formulas-of-listify-each
            (%cdr-induction x)
            (%enable default logic.term-formula))


(%ensure-exactly-these-rules-are-missing "../../logic/term-formula")

