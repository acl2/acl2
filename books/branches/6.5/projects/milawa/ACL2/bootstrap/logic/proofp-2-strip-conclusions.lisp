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
(include-book "proofp-1")
(%interactive)


(%defprojection :list (logic.strip-conclusions x)
                :element (logic.conclusion x)
                :nil-preservingp t)

(%autoprove second-of-logic.strip-conclusions)

(%autoprove forcing-logic.formula-listp-of-logic.strip-conclusions
            (%cdr-induction x))


(%autoprove logic.fmtype-of-logic.conclusion-of-nth-when-logic.all-disjunctionsp)

(%autoprove logic.fmtype-of-logic.conclusion-of-nth-when-logic.all-atomicp)

(%autoprove logic.vlhs-of-logic.conclusion-of-car-when-all-equalp)


(%autoprove logic.vlhs-of-logic.conclusion-of-nth-when-all-equalp-of-logic.vlhses
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

(%autoprove logic.fmtype-of-logic.vrhs-of-logic.conclusion-of-nth-when-logic.all-disjunctionsp-of-logic.all-atomicp)

(%autoprove logic.formula-atblp-of-logic.conclusion-of-car)
(%autoprove logic.formula-atblp-of-logic.conclusion-of-second)
(%autoprove logic.formula-atblp-of-logic.conclusion-of-third)


(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)

(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-when-len-2)
