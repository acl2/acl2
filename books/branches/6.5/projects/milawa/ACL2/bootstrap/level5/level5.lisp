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
(include-book "eqtrace-compiler")
(include-book "contradiction-bldr")
(include-book "update-clause-bldr")
(include-book "disjoined-update-clause-bldr")
(include-book "update-clause-iff-bldr")
(include-book "lambda-2")
(include-book "aux-split-negative")
(include-book "basic-if-lemmas")
(include-book "urewrite-if-lemmas")
(include-book "crewrite-if-lemmas")
(include-book "crewrite-if-lemmas2")
(%interactive)


(%autoadmit level5.step-okp)

(encapsulate
 ()
 (local (%enable default level5.step-okp))
 (%autoprove soundness-of-level5.step-okp)
 (%autoprove level5.step-okp-when-level4.step-okp
             (%forcingp nil)
             (%auto)
             (%enable default level4.step-okp)
             (%auto)
             (%enable default level3.step-okp)
             (%auto)
             (%enable default level2.step-okp)
             (%auto)
             (%enable default logic.appeal-step-okp))
 (%autoprove level5.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit level5.flag-proofp-aux))

(%autoadmit level5.proofp-aux)
(%autoadmit level5.proof-listp-aux)
(%autoprove definition-of-level5.proofp-aux
            (%enable default level5.proofp-aux level5.proof-listp-aux)
            (%restrict default level5.flag-proofp-aux (equal x 'x)))
(%autoprove definition-of-level5.proof-listp-aux
            (%enable default level5.proofp-aux level5.proof-listp-aux)
            (%restrict default level5.flag-proofp-aux (equal x 'x)))


(%autoprove level5.proofp-aux-when-not-consp      (%restrict default definition-of-level5.proofp-aux (equal x 'x)))
(%autoprove level5.proof-listp-aux-when-not-consp (%restrict default definition-of-level5.proof-listp-aux (equal x 'x)))
(%autoprove level5.proof-listp-aux-of-cons        (%restrict default definition-of-level5.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level5.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level5.proofp-aux (equal x 'x)))

(%autoprove booleanp-of-level5.proofp-aux      (%use (%instance (%thm lemma-for-booleanp-of-level5.proofp-aux) (flag 'proof))))
(%autoprove booleanp-of-level5.proof-listp-aux (%use (%instance (%thm lemma-for-booleanp-of-level5.proofp-aux) (flag 'list))))


(%deflist level5.proof-listp-aux (x axioms thms atbl)
          (level5.proofp-aux x axioms thms atbl))

(%autoprove lemma-for-logic.provablep-when-level5.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default definition-of-level5.proofp-aux (equal x 'x))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove logic.provablep-when-level5.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level5.proofp-aux) (flag 'proof))))

(%autoprove logic.provable-listp-when-level5.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level5.proofp-aux) (flag 'list))))



(%autoprove lemma-for-level5.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level5.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove level5.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level5.proofp-aux-when-logic.proofp) (flag 'proof))))

(%autoprove level5.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level5.proofp-aux-when-logic.proofp) (flag 'list))))

(%autoprove forcing-level5.proofp-aux-of-logic.provable-witness
            (%enable default level5.proofp-aux-when-logic.proofp))



(%autoadmit level5.proofp)
(%autoprove booleanp-of-level5.proofp
            (%enable default level5.proofp))
(%autoprove logic.provablep-when-level5.proofp
            (%enable default level5.proofp))


(defsection level5-transition
  (%install-new-proofp level5.proofp)
  (%auto)
  (%qed-install))


(%switch-builder rw.eqtrace-bldr                                         rw.eqtrace-bldr-high)
(%switch-builder rw.eqtrace-contradiction-bldr                           rw.eqtrace-contradiction-bldr-high)
(%switch-builder clause.update-clause-bldr                               clause.update-clause-bldr-high)
(%switch-builder clause.update-clause-iff-bldr                           clause.update-clause-iff-bldr-high)
(%switch-builder clause.disjoined-update-clause-bldr                     clause.disjoined-update-clause-bldr-high)
(%switch-builder build.lambda-pequal-by-args                             build.lambda-pequal-by-args-high)
(%switch-builder build.disjoined-lambda-pequal-by-args                   build.disjoined-lambda-pequal-by-args-high)
(%switch-builder clause.aux-split-negative-1-bldr                        clause.aux-split-negative-1-bldr-high)
(%switch-builder clause.aux-split-negative-2-bldr                        clause.aux-split-negative-2-bldr-high)
(%switch-builder rw.iff-implies-equal-if-specialcase-nil-bldr            rw.iff-implies-equal-if-specialcase-nil-bldr-high)
(%switch-builder rw.iff-implies-iff-if-specialcase-nil-bldr              rw.iff-implies-iff-if-specialcase-nil-bldr-high)
(%switch-builder rw.iff-implies-equal-if-specialcase-t-bldr              rw.iff-implies-equal-if-specialcase-t-bldr-high)
(%switch-builder rw.iff-implies-iff-if-specialcase-t-bldr                rw.iff-implies-iff-if-specialcase-t-bldr-high)
(%switch-builder rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr  rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr-high)
(%switch-builder rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr    rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr-high)
(%switch-builder rw.disjoined-iff-implies-equal-if-specialcase-t-bldr    rw.disjoined-iff-implies-equal-if-specialcase-t-bldr-high)
(%switch-builder rw.disjoined-iff-implies-iff-if-specialcase-t-bldr      rw.disjoined-iff-implies-iff-if-specialcase-t-bldr-high)
(%switch-builder rw.iff-implies-equal-if-bldr                            rw.iff-implies-equal-if-bldr-high)
(%switch-builder rw.iff-implies-iff-if-bldr                              rw.iff-implies-iff-if-bldr-high)
(%switch-builder rw.equal-of-if-x-y-y-bldr                               rw.equal-of-if-x-y-y-bldr-high)
(%switch-builder rw.iff-of-if-x-y-y-bldr                                 rw.iff-of-if-x-y-y-bldr-high)
(%switch-builder rw.disjoined-iff-implies-equal-if-bldr                  rw.disjoined-iff-implies-equal-if-bldr-high)
(%switch-builder rw.disjoined-iff-implies-iff-if-bldr                    rw.disjoined-iff-implies-iff-if-bldr-high)
(%switch-builder rw.disjoined-equal-of-if-x-y-y-bldr                     rw.disjoined-equal-of-if-x-y-y-bldr-high)
(%switch-builder rw.disjoined-iff-of-if-x-y-y-bldr                       rw.disjoined-iff-of-if-x-y-y-bldr-high)


;; At this point we laso switch to using a split limit, due to the tradeoffs in proof sizes.

(%splitlimit 8)



(%finish "level5")
(%save-events "level5.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
