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
(include-book "trace-okp")
(%interactive)

(%deftheorem rw.compile-not-lemma1)

(%defderiv rw.compile-not-trace-lemma-0a :omit-okp t)
(%defderiv rw.compile-not-trace-lemma-1a :omit-okp t)
(%defderiv rw.compile-not-trace-lemma-2a :omit-okp t)

(%defderiv rw.compile-not-trace-lemma-0b :omit-okp t)
(%defderiv rw.compile-not-trace-lemma-1b :omit-okp t)
(%defderiv rw.compile-not-trace-lemma-2b :omit-okp t)

(%autoadmit rw.compile-not-trace)

(local (%enable default
                rw.compile-not-trace
                rw.not-tracep
                rw.trace-conclusion-formula
                rw.trace-formula))

(%autoprove lemma-1-for-rw.compile-not-trace)

(%autoprove lemma-2-for-rw.compile-not-trace
            (%car-cdr-elim proofs))

(local (%enable default
                lemma-1-for-rw.compile-not-trace
                lemma-2-for-rw.compile-not-trace))

(%autoprove rw.compile-not-trace-under-iff)

(%autoprove forcing-logic.appealp-of-rw.compile-not-trace)

(%autoprove logic.conclusion-of-rw.compile-not-trace)

(%autoprove logic.proofp-of-rw.compile-not-trace)

