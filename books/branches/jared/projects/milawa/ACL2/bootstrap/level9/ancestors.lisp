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
(include-book "worse-termp")
(%interactive)


(%autoadmit rw.anframep)

(%autoprove booleanp-of-rw.anframep
            (%enable default rw.anframep))

(%deflist rw.anstackp (x)
          (rw.anframep x))

(defsection rw.anframe-stuff

  (%autoadmit rw.anframe->term)
  (%autoadmit rw.anframe->guts)
  (%autoadmit rw.anframe->fcount)
  (%autoadmit rw.anframe->tokens)

  (local (%enable default
                  rw.anframep
                  rw.anframe->term
                  rw.anframe->guts
                  rw.anframe->fcount
                  rw.anframe->tokens))

  (%autoprove forcing-logic.termp-of-rw.anframe->term)

  (%autoprove forcing-logic.termp-of-rw.anframe->guts
              (%auto)
              (%fertilize (car (cdr x)) (clause.negative-term-guts (car x))))

  (%autoprove forcing-rw.anframe->fcount-elimination)

  (%autoadmit rw.anframe)

  (%autoprove rw.anframep-of-rw.anframe
              (%enable default rw.anframe)))



(%autoadmit rw.earlier-ancestor-biggerp)
(%autoadmit rw.ancestors-check-aux)
(%autoadmit rw.ancestors-check)


(%ensure-exactly-these-rules-are-missing "../../rewrite/ancestors")

