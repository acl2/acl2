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
(include-book "formulas-2-atblp")
(include-book "formulas-2-basic")
(include-book "formulas-2-basic2")
(include-book "formulas-2-equal")
(include-book "formulas-2-list")
(%interactive)

(%autoprove forcing-logic.formula-atblp-of-logic.pequal
            (%restrict default logic.formula-atblp (equal x '(logic.pequal a b))))

(%autoprove forcing-logic.formula-atblp-of-logic.pnot
            (%restrict default logic.formula-atblp (equal x '(logic.pnot a)))
            (%disable default forcing-logic.formula-atblp-of-logic.~arg))

(%autoprove forcing-logic.formula-atblp-of-logic.por
            (%restrict default logic.formula-atblp (equal x '(logic.por a b)))
            (%disable default forcing-logic.formula-atblp-of-logic.vlhs forcing-logic.formula-atblp-of-logic.vrhs))


(%create-theory forcing-logic.formula-atblp-rules)
(%enable forcing-logic.formula-atblp-rules
         forcing-logic.term-atblp-of-logic.=lhs
         forcing-logic.term-atblp-of-logic.=rhs
         forcing-logic.formula-atblp-of-logic.~arg
         forcing-logic.formula-atblp-of-logic.vlhs
         forcing-logic.formula-atblp-of-logic.vrhs
         forcing-logic.formula-atblp-of-logic.pequal
         forcing-logic.formula-atblp-of-logic.pnot
         forcing-logic.formula-atblp-of-logic.por)


(encapsulate
 ()
 (local (%enable default forcing-logic.formula-atblp-rules))

 (%autoprove logic.formula-atblp-when-por-expensive
             (%restrict default logic.formula-atblp (equal x 'x)))
 (%autoprove logic.formula-atblp-when-pnot-expensive
             (%restrict default logic.formula-atblp (equal x 'x)))
 (%autoprove logic.formula-atblp-when-pequal-expensive
             (%restrict default logic.formula-atblp (equal x 'x)))
 (%autoprove logic.formula-atblp-of-logic.por-expensive
             (%restrict default logic.formula-atblp (equal x '(logic.por x y))))
 (%autoprove logic.formula-atblp-of-logic.pequal-expensive
             (%restrict default logic.formula-atblp (equal x '(logic.pequal x y))))
 (%autoprove logic.formula-atblp-of-logic.pnot-expensive
             (%restrict default logic.formula-atblp (equal x '(logic.pnot x)))))


(%create-theory backtracking-logic.formula-atblp-rules)
(%enable backtracking-logic.formula-atblp-rules
         logic.formula-atblp-when-por-expensive
         logic.formula-atblp-when-pnot-expensive
         logic.formula-atblp-when-pequal-expensive
         logic.formula-atblp-of-logic.por-expensive
         logic.formula-atblp-of-logic.pnot-expensive
         logic.formula-atblp-of-logic.pequal-expensive)

