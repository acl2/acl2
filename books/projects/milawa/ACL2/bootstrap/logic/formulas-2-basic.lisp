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



(%autoprove forcing-logic.termp-of-logic.=lhs
            (%enable default logic.fmtype logic.=lhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.termp-of-logic.=rhs
            (%enable default logic.fmtype logic.=rhs)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default forcing-logic.termp-of-logic.=lhs))

(%autoprove forcing-logic.formulap-of-logic.~arg
            (%enable default logic.fmtype logic.~arg)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default forcing-logic.termp-of-logic.=lhs
                      forcing-logic.termp-of-logic.=rhs))

(%autoprove forcing-logic.formulap-of-logic.vlhs
            (%enable default logic.fmtype logic.vlhs)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default
                      forcing-logic.termp-of-logic.=lhs
                      forcing-logic.termp-of-logic.=rhs
                      forcing-logic.formulap-of-logic.~arg))

(%autoprove forcing-logic.formulap-of-logic.vrhs
            (%enable default logic.fmtype logic.vrhs)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default
                      forcing-logic.termp-of-logic.=lhs
                      forcing-logic.termp-of-logic.=rhs
                      forcing-logic.formulap-of-logic.~arg
                      forcing-logic.formulap-of-logic.vlhs))



(%autoprove forcing-logic.formulap-of-logic.pequal
            (%enable default logic.pequal)
            (%restrict default logic.formulap (equal x '(cons 'pequal* (cons a (cons b 'nil))))))

(%autoprove forcing-logic.formulap-of-logic.pnot
            (%enable default logic.pnot)
            (%restrict default logic.formulap (equal x '(cons 'pnot* (cons a 'nil)))))

(%autoprove forcing-logic.formulap-of-logic.por
            (%enable default logic.por)
            (%restrict default logic.formulap (equal x '(cons 'por* (cons a (cons b 'nil))))))

(%autoprove logic.fmtype-of-logic.pequal
            (%enable default logic.fmtype logic.pequal))

(%autoprove logic.fmtype-of-logic.pnot
            (%enable default logic.fmtype logic.pnot))

(%autoprove logic.fmtype-of-logic.por
            (%enable default logic.fmtype logic.por))

(%autoprove logic.=lhs-of-logic.pequal
            (%enable default logic.=lhs logic.pequal))

(%autoprove logic.=rhs-of-logic.pequal
            (%enable default logic.=rhs logic.pequal))

(%autoprove logic.~arg-of-logic.pnot
            (%enable default logic.~arg logic.pnot))

(%autoprove logic.vlhs-of-logic.por
            (%enable default logic.vlhs logic.por))

(%autoprove logic.vrhs-of-logic.por
            (%enable default logic.vrhs logic.por))

(%autoprove logic.=lhs-of-logic.pequal-free)

(%autoprove logic.=rhs-of-logic.pequal-free)

(%autoprove logic.fmtype-of-logic.pequal-free)



(%autoprove forcing-equal-of-logic.pequal-rewrite-two
            (%auto)
            (%enable default logic.fmtype logic.pequal logic.=lhs logic.=rhs)
            (%restrict default logic.formulap (equal x 'x))
            (%restrict default tuplep (or (equal n ''3) (equal n ''2) (equal n ''1)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-equal-of-logic.pequal-rewrite)



(%autoprove forcing-equal-of-logic.pnot-rewrite-two
            (%enable default logic.fmtype logic.pnot logic.~arg)
            (%restrict default logic.formulap (equal x 'x))
            (%restrict default tuplep (or (equal n ''2) (equal n ''1)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-equal-of-logic.pnot-rewrite)

(%autoprove forcing-equal-of-logic.por-rewrite-two
            (%enable default logic.fmtype logic.vlhs logic.vrhs logic.por)
            (%restrict default logic.formulap (equal x 'x))
            (%restrict default tuplep (or (equal n ''3) (equal n ''2) (equal n ''1)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-equal-of-logic.por-rewrite)




(%autoprove forcing-logic.pnot-of-logic.~arg)

(%autoprove forcing-logic.por-of-logic.vlhs-and-logic.vrhs)

(%autoprove forcing-logic.pequal-of-logic.=lhs-and-logic.=rhs)

(%autoprove equal-logic.pequal-logic.pequal-rewrite
            (%enable default logic.pequal))

(%autoprove equal-logic.pnot-logic.pnot-rewrite
            (%enable default logic.pnot))

(%autoprove equal-logic.por-logic.por-rewrite
            (%enable default logic.por))

