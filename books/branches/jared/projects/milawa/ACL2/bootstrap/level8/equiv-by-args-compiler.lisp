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

(defthm equal-of-cons-and-repeat
  ;; BOZO a nice and useful rule in need of a good home
  (equal (equal (cons a x)
                (repeat b n))
         (and (not (zp n))
              (equal a b)
              (equal x (repeat b (- n 1))))))

(%autoprove equal-of-cons-and-repeat
            (%autoinduct repeat b n)
            (%restrict default repeat (equal n 'n)))


(%autoadmit rw.compile-equiv-by-args-trace)

(local (%enable default
                rw.trace-conclusion-formula
                rw.trace-formula
                rw.equiv-by-args-tracep
                rw.compile-equiv-by-args-trace))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition))

(%autoprove rw.compile-equiv-by-args-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-equiv-by-args-trace)

(%autoprove lemma-for-logic.conclusion-of-rw.compile-equiv-by-args-trace
            (%enable default logic.function-name logic.function-args))

(local (%enable default lemma-for-logic.conclusion-of-rw.compile-equiv-by-args-trace))

(%autoprove logic.conclusion-of-rw.compile-equiv-by-args-trace
            (%auto)
            (%enable default
                     type-set-like-rules
                     formula-decomposition
                     expensive-arithmetic-rules-two)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      equal-of-logic.function-rewrite
                      equal-of-logic.function-rewrite-alt))

(%autoprove lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
            (%disable default
                      len-of-rw.trace-list-conclusion-formulas
                      [outside]len-of-rw.trace-list-conclusion-formulas)
            (%use (%instance (%thm len-of-rw.trace-list-conclusion-formulas)
                             (x (rw.trace->subtraces x)))))

(%autoprove lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace
            (%disable default
                      len-of-rw.trace-list-conclusion-formulas
                      [outside]len-of-rw.trace-list-conclusion-formulas)
            (%use (%instance (%thm len-of-rw.trace-list-conclusion-formulas)
                             (x (rw.trace->subtraces x)))))

(%autoprove lemma-3-for-logic.proofp-of-rw.compile-equiv-by-args-trace)

(%autoprove logic.proofp-of-rw.compile-equiv-by-args-trace
            (%enable default
                            lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                            lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                            lemma-3-for-logic.proofp-of-rw.compile-equiv-by-args-trace)
            (%auto)
            (%enable default
                     type-set-like-rules
                     expensive-arithmetic-rules-two))

