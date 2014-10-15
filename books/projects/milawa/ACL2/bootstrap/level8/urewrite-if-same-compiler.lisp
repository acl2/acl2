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

(%autoadmit rw.compile-urewrite-if-specialcase-same-trace)

(local (%splitlimit 20)) ;; BOZO Consider this globally at this level

(local (%enable default
                rw.compile-urewrite-if-specialcase-same-trace
                rw.urewrite-if-specialcase-same-tracep
                rw.trace-conclusion-formula
                rw.trace-formula
                equal-of-2-and-len))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 type-set-like-rules
                 expensive-subsetp-rules
                 same-length-prefixes-equal-cheap
                 formula-decomposition
                 unusual-consp-rules
                 expensive-term/formula-inference))

(local (%disable default
                 logic.appealp-of-car-when-logic.appeal-listp
                 logic.appealp-of-second-when-logic.appeal-listp
                 logic.appealp-when-memberp-of-logic.appeal-listp
                 logic.appeal-listp-of-cdr-when-logic.appeal-listp
                 logic.proofp-when-memberp-of-logic.proof-listp
                 logic.proofp-of-car-when-logic.proof-listp
                 logic.proof-listp-of-cdr-when-logic.proof-listp
                 rw.tracep-of-car-when-rw.trace-listp
                 rw.trace-listp-of-cdr-when-rw.trace-listp
                 rw.trace-listp-when-not-consp
                 logic.appeal-listp-when-not-consp
                 logic.proofp-when-not-consp
                 logic.proof-listp-when-not-consp
                 logic.strip-conclusions-when-not-consp
                 rw.trace-list-formulas-when-not-consp
                 rw.tracep-when-memberp-of-rw.trace-listp
                 forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                 forcing-equal-of-logic.function-with-two-args-alt))

(%autoprove rw.compile-urewrite-if-specialcase-same-trace-under-iff)

(%autoprove logic.appealp-of-rw.compile-urewrite-if-specialcase-same-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x))))))

(%autoprove logic.conclusion-of-rw.compile-urewrite-if-specialcase-same-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      logic.termp-when-logic.formulap
                      logic.formulap-when-logic.termp
                      forcing-equal-of-logic.pequal-rewrite
                      forcing-equal-of-logic.pequal-rewrite-two))

(%autoprove logic.proofp-of-rw.compile-urewrite-if-specialcase-same-trace
            (%use (%instance (%thm forcing-rw.trace-listp-of-rw.trace->subtraces)))
            (%restrict default logic.strip-conclusions          (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.appeal-listp (memberp x '(proofs (cdr proofs))))
            (%restrict default definition-of-logic.proof-listp  (memberp x '(proofs (cdr proofs))))
            (%restrict default rw.trace-list-formulas           (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x)))))
            (%restrict default definition-of-rw.trace-listp     (memberp x '((rw.trace->subtraces x) (cdr (rw.trace->subtraces x))))))
