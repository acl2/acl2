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
(include-book "equiv-by-args-compiler")
(%interactive)


(%autoadmit build.lambda-equal-by-args)
(encapsulate
 ()
 (local (%enable default build.lambda-equal-by-args))
 (%autoprove build.lambda-equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.lambda-equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.lambda-equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.lambda-equal-by-args))

(%autoadmit build.disjoined-lambda-equal-by-args)
(encapsulate
 ()
 (local (%enable default build.disjoined-lambda-equal-by-args))
 (%autoprove build.disjoined-lambda-equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.disjoined-lambda-equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.disjoined-lambda-equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.disjoined-lambda-equal-by-args))

(%autoprove forcing-equal-when-equal-of-logic.lambda-parts
            (%enable default
                     logic.lambda-formals
                     logic.lambda-body
                     logic.lambda-actuals
                     logic.lambdap)
            (%restrict default definition-of-logic.termp (memberp x '(x y)))
            (%disable default
                      logic.term-vars-when-bad
                      logic.constantp-when-logic.variablep
                      logic.variablep-of-car-when-logic.variable-listp
                      logic.term-vars-when-constant
                      logic.term-vars-when-variable
                      logic.term-vars-when-logic.lambda
                      logic.variablep-when-logic.constantp
                      expensive-subsetp-rules
                      logic.formulap-when-logic.termp
                      logic.termp-when-logic.formulap
                      logic.termp-when-logic.variablep
                      logic.termp-when-logic.constantp
                      logic.termp-of-car-when-logic.term-listp
                      logic.term-vars-when-function-call))

(%autoadmit rw.compile-lambda-equiv-by-args-trace)

(local (%enable default
                rw.trace-conclusion-formula
                rw.trace-formula
                rw.lambda-equiv-by-args-tracep
                rw.compile-lambda-equiv-by-args-trace))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 forcing-logic.vrhses-of-logic.por-list-free))

(%autoprove lemma-for-rw.compile-lambda-equiv-by-args-trace
            (%disable default
                      len-of-rw.trace-list-lhses
                      [outside]len-of-rw.trace-list-lhses)
            (%use (%instance (%thm len-of-rw.trace-list-lhses)
                             (x y))))

(local (%enable default
                lemma-for-rw.compile-lambda-equiv-by-args-trace
                lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace))

(%autoprove rw.compile-lambda-equiv-by-args-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-lambda-equiv-by-args-trace)

(%autoprove logic.conclusion-of-rw.compile-lambda-equiv-by-args-trace
            (%auto)
            (%enable default
                     type-set-like-rules
                     forcing-equal-when-equal-of-logic.lambda-parts
                     expensive-arithmetic-rules-two
                     expensive-term/formula-inference
                     formula-decomposition))

(%autoprove logic.proofp-of-rw.compile-lambda-equiv-by-args-trace
            (%disable default
                      unusual-memberp-rules
                      memberp-when-memberp-of-cdr
                      memberp-when-not-consp))


