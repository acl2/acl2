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
(include-book "proofp-3-provablep")
(include-book "proofp-3-subproofs")
(%interactive)



(%autoprove lemma-main-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%restrict default definition-of-logic.proofp
                       (equal x '(logic.appeal (logic.method x)
                                               (logic.conclusion x)
                                               (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                            axioms thms atbl)
                                               (logic.extras x))))
            (%enable default lemma-appeal-step-for-forcing-logic.provablep-when-logic.subproofs-provable))


(%autoprove forcing-logic.provablep-when-logic.subproofs-provable
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (logic.appeal (logic.method x)
                                              (logic.conclusion x)
                                              (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                           axioms thms atbl)
                                              (logic.extras x)))))
            (%enable default lemma-main-for-forcing-logic.provablep-when-logic.subproofs-provable))

(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-of-cdr-when-logic.provable-listp)

(%autoprove logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest)


(%ensure-exactly-these-rules-are-missing "../../logic/proofp"
                                         ;; We don't have skip-okp here.
                                         logic.formula-atblp-of-logic.conclusion-when-logic.skip-okp
                                         booleanp-of-logic.skip-okp)

