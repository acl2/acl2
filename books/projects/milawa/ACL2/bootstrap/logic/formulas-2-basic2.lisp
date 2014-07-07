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
(include-book "formulas-1")
(%interactive)

(%autoprove logic.pequal-under-iff
            (%enable default logic.pequal))

(%autoprove logic.pnot-under-iff
            (%enable default logic.pnot))

(%autoprove logic.por-under-iff
            (%enable default logic.por))

(%autoprove forcing-logic.=lhs-under-iff
            (%enable default logic.fmtype logic.=lhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.=rhs-under-iff
            (%enable default logic.fmtype logic.=rhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.~arg-under-iff
            (%enable default logic.fmtype logic.~arg)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.vlhs-under-iff
            (%enable default logic.fmtype logic.vlhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.vrhs-under-iff
            (%enable default logic.fmtype logic.vrhs)
            (%restrict default logic.formulap (equal x 'x)))


(%autoprove logic.formulap-of-logic.pequal-of-nil-one
            (%enable default logic.pequal)
            (%restrict default logic.formulap (equal x '(cons 'pequal* (cons 'nil (cons x 'nil))))))

(%autoprove logic.formulap-of-logic.pequal-of-nil-two
            (%enable default logic.pequal)
            (%restrict default logic.formulap (equal x '(cons 'pequal* (cons x '(nil))))))

(%autoprove logic.formulap-of-logic.pnot-of-logic.pequal-of-nil-one
            (%enable default logic.pnot)
            (%restrict default logic.formulap (equal x '(CONS 'PNOT* (CONS (LOGIC.PEQUAL 'NIL X) 'NIL)))))

(%autoprove logic.formulap-of-logic.pnot-of-logic.pequal-of-nil-two
            (%enable default logic.pnot)
            (%restrict default logic.formulap (equal x '(CONS 'PNOT* (CONS (LOGIC.PEQUAL X 'NIL) 'NIL)))))

(%autoprove logic.formulap-of-logic.por-expensive
            (%restrict default logic.formulap (equal x '(cons 'por* (cons x (cons y 'nil)))))
            (%enable default logic.por))
