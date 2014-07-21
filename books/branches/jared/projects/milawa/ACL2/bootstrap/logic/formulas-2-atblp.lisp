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


(%autoprove rank-of-logic.=lhs-strong
            (%enable default logic.=lhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.=rhs-strong
            (%enable default logic.=rhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.~arg-strong
            (%enable default logic.~arg logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.vlhs-strong
            (%enable default logic.vlhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.vrhs-strong
            (%enable default logic.vrhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.pnot
            (%enable default logic.pnot))

(%autoprove rank-of-logic.pequal
            (%enable default logic.pequal))

(%autoprove rank-of-logic.por
            (%enable default logic.por))


(%autoadmit logic.formula-atblp)

(defmacro %logic.formulap-induction (x)
  `(%induct (rank ,x)
            ((equal (logic.fmtype ,x) 'pequal*)
             nil)
            ((equal (logic.fmtype ,x) 'pnot*)
             (((,x (logic.~arg ,x)))))
            ((equal (logic.fmtype ,x) 'por*)
             (((,x (logic.vlhs ,x)))
              ((,x (logic.vrhs ,x)))))
            ((and (not (equal (logic.fmtype ,x) 'pequal*))
                  (not (equal (logic.fmtype ,x) 'pnot*))
                  (not (equal (logic.fmtype ,x) 'por*)))
             nil)))

(%autoprove booleanp-of-logic.formula-atblp
            (%logic.formulap-induction x)
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove logic.formula-atblp-when-not-consp
            (%restrict default logic.formula-atblp (equal x 'x))
            (%enable default logic.fmtype))

(%autoprove forcing-logic.term-atblp-of-logic.=lhs
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-logic.=rhs
            (%restrict default logic.formula-atblp (equal x 'x))
            (%disable default forcing-logic.term-atblp-of-logic.=lhs))

(%autoprove forcing-logic.formula-atblp-of-logic.~arg
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove forcing-logic.formula-atblp-of-logic.vlhs
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove forcing-logic.formula-atblp-of-logic.vrhs
            (%restrict default logic.formula-atblp (equal x 'x))
            (%disable default forcing-logic.formula-atblp-of-logic.vlhs))

(%autoprove logic.formulap-when-malformed-cheap
            ;; BOZO I don't like where this is located; try moving it up in formulas.lisp and
            ;; move it to one of the basic files maybe.
            (%restrict default logic.formulap (equal x 'x))
            (%enable default logic.fmtype))

(%autoprove logic.formula-atblp-when-malformed-cheap
            (%restrict default logic.formula-atblp (equal x 'x)))

