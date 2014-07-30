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



(%autoadmit logic.formulap)

(%autoadmit logic.pequal)
(%autoadmit logic.pnot)
(%autoadmit logic.por)

(%noexec logic.pequal)
(%noexec logic.pnot)
(%noexec logic.por)

(%autoadmit logic.fmtype)
(%autoadmit logic.=lhs)
(%autoadmit logic.=rhs)
(%autoadmit logic.~arg)
(%autoadmit logic.vlhs)
(%autoadmit logic.vrhs)


(defmacro %logic.raw-formulap-induction (x)
  `(%induct (rank ,x)
            ((equal (first ,x) 'pequal*)
             nil)
            ((equal (first ,x) 'pnot*)
             (((,x (second ,x)))))
            ((equal (first ,x) 'por*)
             (((,x (second ,x)))
              ((,x (third ,x)))))
            ((and (not (equal (first ,x) 'pequal*))
                  (not (equal (first ,x) 'pnot*))
                  (not (equal (first ,x) 'por*)))
             nil)))

(%autoprove booleanp-of-logic.formulap
            (%logic.raw-formulap-induction x)
            (%restrict default logic.formulap (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.formulap-when-not-consp
            (%restrict default logic.formulap (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))



(%autoprove lemma-1-for-logic.formulap-when-logic.termp
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove lemma-2-for-logic.formulap-when-logic.termp
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%enable default logic.constantp))

(%autoprove logic.formulap-when-logic.termp
            (%use (%instance (%thm lemma-1-for-logic.formulap-when-logic.termp)))
            (%use (%instance (%thm lemma-2-for-logic.formulap-when-logic.termp))))

(%autoprove logic.termp-when-logic.formulap)
