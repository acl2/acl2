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
(include-book "formulas")
(include-book "substitute-term")
(%interactive)

(%autoadmit logic.substitute-formula)

(%autoprove logic.substitute-formula-of-logic.por
            (%restrict default logic.substitute-formula (equal formula '(logic.por x y))))

(%autoprove logic.substitute-formula-of-logic.pnot
            (%restrict default logic.substitute-formula (equal formula '(logic.pnot x))))

(%autoprove logic.substitute-formula-of-logic.pequal
            (%restrict default logic.substitute-formula (equal formula '(logic.pequal x y))))

(%autoprove logic.substitute-formula-when-malformed-cheap
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove logic.substitute-formula-of-nil)

(%autoprove forcing-logic.formulap-of-logic.substitute-formula
            (%logic.formulap-induction formula)
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove forcing-logic.formula-atblp-of-logic.substitute-formula
            (%logic.formulap-induction formula)
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove forcing-logic.substitute-formula-under-iff
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove forcing-logic.fmtype-of-logic.substitute-formula
            (%restrict default logic.substitute-formula (equal formula 'x)))

(%autoprove forcing-logic.=lhs-of-logic.substitute-formula
            (%restrict default logic.substitute-formula (equal formula 'x)))

(%autoprove forcing-logic.=rhs-of-logic.substitute-formula
            (%restrict default logic.substitute-formula (equal formula 'x)))

