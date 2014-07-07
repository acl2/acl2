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

(%autoadmit logic.=lhses-of-strip-conclusions)
(%autoprove logic.=lhses-of-strip-conclusions-removal
            (%restrict default logic.=lhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.=rhses-of-strip-conclusions)
(%autoprove logic.=rhses-of-strip-conclusions-removal
            (%restrict default logic.=rhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.vrhses-of-strip-conclusions)
(%autoprove logic.vrhses-of-strip-conclusions-removal
            (%restrict default logic.vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.vlhses-of-strip-conclusions)
(%autoprove logic.vlhses-of-strip-conclusions-removal
            (%restrict default logic.vlhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.=lhses-of-vrhses-of-strip-conclusions)
(%autoprove logic.=lhses-of-vrhses-of-strip-conclusions-removal
            (%restrict default logic.=lhses-of-vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.=rhses-of-vrhses-of-strip-conclusions)
(%autoprove logic.=rhses-of-vrhses-of-strip-conclusions-removal
            (%restrict default logic.=rhses-of-vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.all-atomicp-of-strip-conclusions)
(%autoprove logic.all-atomicp-of-strip-conclusions-removal
            (%restrict default logic.all-atomicp-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.all-disjunctionsp-of-strip-conclusions)
(%autoprove logic.all-disjunctionsp-of-strip-conclusions-removal
            (%restrict default logic.all-disjunctionsp-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.all-atomicp-of-vrhses-of-strip-conclusions)
(%autoprove logic.all-atomicp-of-vrhses-of-strip-conclusions-removal
            (%restrict default logic.all-atomicp-of-vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

