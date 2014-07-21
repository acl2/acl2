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
(include-book "primary-eqtrace")
(include-book "secondary-eqtrace")
(include-book "transitivity-eqtraces")
(include-book "weakening-eqtrace")
(include-book "direct-iff-eqtrace")
(include-book "negative-iff-eqtrace")
(%interactive)



(%autoadmit rw.eqtrace-step-okp)
(%autoprove booleanp-of-rw.eqtrace-step-okp
            (%enable default rw.eqtrace-step-okp))


(%autoadmit rw.flag-eqtrace-okp)
(%autoadmit rw.eqtrace-okp)
(%autoadmit rw.eqtrace-list-okp)

(%autoprove definition-of-rw.eqtrace-okp
            (%restrict default rw.flag-eqtrace-okp (equal x 'x))
            (%enable default rw.eqtrace-okp rw.eqtrace-list-okp))

(%autoprove definition-of-rw.eqtrace-list-okp
            (%restrict default rw.flag-eqtrace-okp (equal x 'x))
            (%enable default rw.eqtrace-okp rw.eqtrace-list-okp))

(%autoprove rw.flag-eqtrace-okp-of-trace
            (%enable default rw.eqtrace-okp))

(%autoprove rw.flag-eqtrace-okp-of-list
            (%enable default rw.eqtrace-list-okp))



(%autoprove lemma-for-booleanp-of-rw.eqtrace-okp
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-okp (equal x 'x))
            (%restrict default definition-of-rw.eqtrace-list-okp (equal x 'x)))

(%autoprove booleanp-of-rw.eqtrace-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtrace-okp)
                             (flag 'trace))))

(%autoprove booleanp-of-rw.eqtrace-list-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtrace-okp)
                             (flag 'list))))

(%autoprove rw.eqtrace-list-okp-when-not-consp
            (%restrict default definition-of-rw.eqtrace-list-okp (equal x 'x)))

(%autoprove rw.eqtrace-list-okp-of-cons
            (%restrict default definition-of-rw.eqtrace-list-okp (equal x '(cons a x))))

(%autoprove rw.eqtrace-step-okp-of-nil
            (%enable default rw.eqtrace-step-okp))

(%autoprove rw.eqtrace-okp-of-nil
            (%restrict default definition-of-rw.eqtrace-okp (equal x ''nil)))

(%deflist rw.eqtrace-list-okp (x box)
          (rw.eqtrace-okp x box))


(%autoprove forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces
            (%restrict default definition-of-rw.eqtrace-okp (equal x 'x)))

(%autoprove rw.primary-eqtrace-okp-when-empty-box
            (%enable default rw.primary-eqtrace-okp))

(%autoprove rw.secondary-eqtrace-okp-when-empty-box
            (%enable default rw.secondary-eqtrace-okp))


(%autoprove lemma-for-rw.eqtrace-okp-when-empty-box
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-okp (equal x 'x))
            (%auto)
            (%forcingp nil)
            (%enable default
                     rw.eqtrace-step-okp
                     rw.trans1-eqtrace-okp
                     rw.trans2-eqtrace-okp
                     rw.trans3-eqtrace-okp
                     rw.weakening-eqtrace-okp
                     rw.direct-iff-eqtrace-okp
                     rw.negative-iff-eqtrace-okp))

(%autoprove rw.eqtrace-okp-when-empty-box
            (%use (%instance (%thm lemma-for-rw.eqtrace-okp-when-empty-box)
                             (flag 'trace))))

(%autoprove rw.eqtrace-list-okp-when-empty-box
            (%use (%instance (%thm lemma-for-rw.eqtrace-okp-when-empty-box)
                             (flag 'list))))


(encapsulate
 ()
 (local (%enable default rw.eqtrace-step-okp))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.primary-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.primary-eqtrace okp nhyp)
                                     (rw.primary-eqtrace 't nhyp)))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.secondary-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.secondary-eqtrace okp nhyp)
                                     (rw.secondary-eqtrace 't nhyp)))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.trans1-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.trans1-eqtrace iffp x y))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.trans2-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.trans2-eqtrace iffp x y))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.trans3-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.trans3-eqtrace iffp x y))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.weakening-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.weakening-eqtrace x))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.direct-iff-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.direct-iff-eqtrace okp nhyp)
                                     (rw.direct-iff-eqtrace 't nhyp)))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.negative-iff-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.negative-iff-eqtrace okp nhyp)
                                     (rw.negative-iff-eqtrace 't nhyp))))))



(%autoadmit rw.eqtrace-formula)


(%autoprove forcing-logic.formulap-of-rw.eqtrace-formula
            (%enable default rw.eqtrace-formula))

(%autoprove forcing-logic.formula-atblp-of-rw.eqtrace-formula
            (%enable default rw.eqtrace-formula))

(%defprojection :list (rw.eqtrace-formula-list x box)
                :element (rw.eqtrace-formula x box))

(%autoprove forcing-logic.formula-listp-of-rw.eqtrace-formula-list
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-rw.eqtrace-formula
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/eqtrace-okp")

