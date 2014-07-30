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
(include-book "support-3")
(%interactive)



(%autoadmit level2.step-okp)

(encapsulate
 ()
 (local (%enable default level2.step-okp))
 (%autoprove soundness-of-level2.step-okp)
 (%autoprove level2.step-okp-when-logic.appeal-step-okp (%enable default logic.appeal-step-okp))
 (%autoprove level2.step-okp-when-not-consp             (%enable default logic.method)))

(encapsulate
 ()
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit level2.flag-proofp))

(%autoadmit level2.proofp)
(%autoadmit level2.proof-listp)
(%autoprove definition-of-level2.proofp
            (%enable default level2.proofp level2.proof-listp)
            (%restrict default level2.flag-proofp (equal x 'x)))
(%autoprove definition-of-level2.proof-listp
            (%enable default level2.proofp level2.proof-listp)
            (%restrict default level2.flag-proofp (equal x 'x)))


(%autoprove level2.proofp-when-not-consp      (%restrict default definition-of-level2.proofp (equal x 'x)))
(%autoprove level2.proof-listp-when-not-consp (%restrict default definition-of-level2.proof-listp (equal x 'x)))
(%autoprove level2.proof-listp-of-cons        (%restrict default definition-of-level2.proof-listp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level2.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level2.proofp (equal x 'x)))

(%autoprove booleanp-of-level2.proofp      (%use (%instance (%thm lemma-for-booleanp-of-level2.proofp) (flag 'proof))))
(%autoprove booleanp-of-level2.proof-listp (%use (%instance (%thm lemma-for-booleanp-of-level2.proofp) (flag 'list))))


(%deflist level2.proof-listp (x axioms thms atbl)
          (level2.proofp x axioms thms atbl))


(%autoprove lemma-for-logic.provablep-when-level2.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level2.proofp (equal x 'x)))

(%autoprove logic.provablep-when-level2.proofp           (%use (%instance (%thm lemma-for-logic.provablep-when-level2.proofp) (flag 'proof))))
(%autoprove logic.provable-listp-when-level2.proof-listp (%use (%instance (%thm lemma-for-logic.provablep-when-level2.proofp) (flag 'list))))



(%autoprove lemma-for-level2.proofp-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level2.proofp (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove level2.proofp-when-logic.proofp                 (%use (%instance (%thm lemma-for-level2.proofp-when-logic.proofp) (flag 'proof))))
(%autoprove level2.proof-listp-when-logic.proof-listp       (%use (%instance (%thm lemma-for-level2.proofp-when-logic.proofp) (flag 'list))))
(%autoprove forcing-level2.proofp-of-logic.provable-witness (%enable default level2.proofp-when-logic.proofp))

(defsection level2-transition
  (%install-new-proofp level2.proofp)
  (%auto)
  (%qed-install))

(%switch-builder build.commute-or                     build.commute-or-high)
(%switch-builder build.right-expansion                build.right-expansion-high)
(%switch-builder build.modus-ponens                   build.modus-ponens-high)
(%switch-builder build.modus-ponens-2                 build.modus-ponens-2-high)
(%switch-builder build.right-associativity            build.right-associativity-high)
(%switch-builder build.disjoined-left-expansion       build.disjoined-left-expansion-high)
(%switch-builder build.disjoined-right-expansion      build.disjoined-right-expansion-high)
(%switch-builder build.disjoined-contraction          build.disjoined-contraction-high)
(%switch-builder build.cancel-neg-neg                 build.cancel-neg-neg-high)
(%switch-builder build.insert-neg-neg                 build.insert-neg-neg-high)
(%switch-builder build.lhs-insert-neg-neg             build.lhs-insert-neg-neg-high)
(%switch-builder build.merge-negatives                build.merge-negatives-high)
(%switch-builder build.merge-implications             build.merge-implications-high)
(%switch-builder build.disjoined-commute-or           build.disjoined-commute-or-high)
(%switch-builder build.disjoined-right-associativity  build.disjoined-right-associativity-high)
(%switch-builder build.disjoined-cut                  build.disjoined-cut-high)
(%switch-builder build.disjoined-modus-ponens         build.disjoined-modus-ponens-high)
(%switch-builder build.disjoined-modus-ponens-2       build.disjoined-modus-ponens-2-high)
(%switch-builder build.lhs-commute-or-then-rassoc     build.lhs-commute-or-then-rassoc-high)
(%switch-builder rw.crewrite-twiddle-bldr             rw.crewrite-twiddle-bldr-high)
(%switch-builder rw.crewrite-twiddle2-bldr            rw.crewrite-twiddle2-bldr-high)
(%switch-builder clause.aux-split-twiddle             clause.aux-split-twiddle-high)
(%switch-builder clause.aux-split-twiddle2            clause.aux-split-twiddle2-high)
(%switch-builder clause.aux-split-default-3-bldr      clause.aux-split-default-3-bldr-high)



(%finish "level2")
(%save-events "level2.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
