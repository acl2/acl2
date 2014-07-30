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
(include-book "pequal-list")
(%interactive)


(%autoadmit build.pequal-from-equal-list)

(%autoprove len-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.appeal-listp-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-build.pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.pequal-from-equal-list (equal x 'x)))





(%autoadmit build.disjoined-pequal-from-equal-list)

(%autoprove len-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.appeal-listp-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-build.disjoined-pequal-from-equal-list
            (%cdr-induction x)
            (%restrict default build.disjoined-pequal-from-equal-list (equal x 'x)))




(%autoadmit build.equal-by-args)

(encapsulate
 ()
 (local (%enable default build.equal-by-args axiom-equal-when-same))
 (%autoprove build.equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.equal-by-args))



(%autoadmit build.disjoined-equal-by-args)

(encapsulate
 ()
 (local (%enable default build.disjoined-equal-by-args axiom-equal-when-same))
 (%autoprove build.disjoined-equal-by-args-under-iff)
 (%autoprove forcing-logic.appealp-of-build.disjoined-equal-by-args)
 (%autoprove forcing-logic.conclusion-of-build.disjoined-equal-by-args)
 (%autoprove forcing-logic.proofp-of-build.disjoined-equal-by-args))




(%autoadmit build.equal-by-args-aux-okp)

(%autoprove build.equal-by-args-aux-okp-removal
            (%autoinduct build.equal-by-args-aux-okp)
            (%splitlimit 8)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default build.equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoadmit build.equal-by-args-okp)

(%autoprove booleanp-of-build.equal-by-args-aux-okp
            (%autoinduct build.equal-by-args-aux-okp)
            (%splitlimit 8)
            (%restrict default build.equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoprove booleanp-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove build.equal-by-args-okp-of-logic.appeal-identity
            (%enable default build.equal-by-args-okp))

(%autoprove lemma-1-for-soundness-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove lemma-2-for-soundness-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove lemma-3-for-soundness-of-build.equal-by-args-okp
            (%enable default build.equal-by-args-okp))

(%autoprove forcing-soundness-of-build.equal-by-args-okp
            (%enable default
                     lemma-1-for-soundness-of-build.equal-by-args-okp
                     lemma-2-for-soundness-of-build.equal-by-args-okp
                     lemma-3-for-soundness-of-build.equal-by-args-okp)
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (build.equal-by-args (logic.function-name (first (logic.function-args (logic.=lhs (logic.conclusion x)))))
                                                     (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                  axioms thms atbl))))))




(%autoadmit build.disjoined-equal-by-args-aux-okp)

(%autoprove build.disjoined-equal-by-args-aux-okp-removal
            (%autoinduct build.disjoined-equal-by-args-aux-okp)
            (%splitlimit 8)
            (%disable default
                      trichotomy-of-<
                      antisymmetry-of-<
                      not-equal-when-less
                      not-equal-when-less-two
                      logic.termp-when-logic.formulap
                      logic.formulap-when-logic.termp
                      same-length-prefixes-equal-cheap
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots)
            (%disable default logic.vlhs-of-logic.conclusion-of-car-when-all-equalp)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default build.disjoined-equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoadmit build.disjoined-equal-by-args-okp)

(%autoprove booleanp-of-build.disjoined-equal-by-args-aux-okp
            (%autoinduct build.disjoined-equal-by-args-aux-okp)
            (%splitlimit 8)
            (%restrict default build.disjoined-equal-by-args-aux-okp (equal proofs 'proofs)))

(%autoprove booleanp-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp))

(%autoprove build.disjoined-equal-by-args-okp-of-logic.appeal-identity
            (%enable default build.disjoined-equal-by-args-okp))

(%autoprove lemma-1-for-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots))

(%autoprove lemma-2-for-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots))

(%autoprove lemma-3-for-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default build.disjoined-equal-by-args-okp)
            (%disable default
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots))

(%autoprove forcing-soundness-of-build.disjoined-equal-by-args-okp
            (%enable default
                     lemma-1-for-soundness-of-build.disjoined-equal-by-args-okp
                     lemma-2-for-soundness-of-build.disjoined-equal-by-args-okp
                     lemma-3-for-soundness-of-build.disjoined-equal-by-args-okp)
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (build.disjoined-equal-by-args
                                 (logic.function-name (first (logic.function-args (logic.=lhs (logic.vrhs (logic.conclusion x))))))
                                 (logic.vlhs (logic.conclusion x))
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl))))))
