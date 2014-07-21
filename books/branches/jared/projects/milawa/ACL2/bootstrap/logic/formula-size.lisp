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
(%interactive)

;; BOZO shouldn't formula-size be using the proper accessors?  This definition
;; seems strange and not very good.
(%autoadmit logic.formula-size)

(%autoprove natp-of-logic.formula-size
            (%restrict default logic.formula-size (equal x 'x)))

(%autoprove logic.formula-size-nonzero
            (%restrict default logic.formula-size (equal x 'x)))

(%autoprove ordp-of-logic.formula-size)

(%autoprove forcing-logic.formula-size-of-logic.=lhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.=lhs))

(%autoprove forcing-logic.formula-size-of-logic.=rhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.=rhs))

(%autoprove forcing-logic.formula-size-of-logic.~arg
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.~arg))

(%autoprove forcing-logic.formula-size-of-logic.vlhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.vlhs))

(%autoprove forcing-logic.formula-size-of-logic.vrhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.vrhs))

(%autoprove logic.formula-size-of-logic.pnot
            (%restrict default logic.formula-size (equal x '(cons 'pnot* (cons x 'nil))))
            (%enable default logic.pnot))

(%autoprove logic.formula-size-of-logic.por
            (%restrict default logic.formula-size (equal x '(cons 'por* (cons x (cons y 'nil)))))
            (%enable default logic.por))

(%autoprove logic.formula-size-of-pequal
            (%restrict default logic.formula-size (equal x '(cons 'pequal* (cons x (cons y 'nil)))))
            (%enable default logic.pequal))



(%autoadmit logic.formula-list-size)

(%autoprove logic.formula-list-size-when-not-consp
            (%restrict default logic.formula-list-size (equal x 'x)))

(%autoprove logic.formula-list-size-of-cons
            (%restrict default logic.formula-list-size (equal x '(cons a x))))

(%autoprove natp-of-logic.formula-list-size
            (%cdr-induction x))

(%autoprove ordp-of-logic.formula-list-size)

(%ensure-exactly-these-rules-are-missing "../../logic/formula-size")

