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
(include-book "support-2")
(%interactive)

(%defderiv build.lhs-commute-or-then-rassoc)

(%defderiv rw.crewrite-twiddle-bldr)

(%defderiv rw.crewrite-twiddle2-lemma :omit-okp t)
(%defderiv rw.crewrite-twiddle2-bldr)

(%defderiv clause.aux-split-twiddle-lemma-1 :omit-okp t)
(%defderiv clause.aux-split-twiddle)

(%defderiv clause.aux-split-twiddle2-lemma-1a :omit-okp t)
(%defderiv clause.aux-split-twiddle2-lemma-1  :omit-okp t)
(%defderiv clause.aux-split-twiddle2-lemma-2a :omit-okp t)
(%defderiv clause.aux-split-twiddle2-lemma-2  :omit-okp t)
(%defderiv clause.aux-split-twiddle2)

(%defderiv clause.aux-split-default-3-bldr)

(%defderiv clause.aux-limsplit-cutoff-step-bldr)