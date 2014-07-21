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
(include-book "simple-split-bldr")
(include-book "simple-limsplit-bldr")
(include-book "factor-bldr-okp")
(%interactive)

(%autoadmit level6.step-okp)

(encapsulate
 ()
 (local (%enable default level6.step-okp))
 (%autoprove soundness-of-level6.step-okp)
 (%autoprove level6.step-okp-when-level5.step-okp
             (%forcingp nil)
             (%enable default level5.step-okp)
             (%auto)
             (%enable default level4.step-okp)
             (%auto)
             (%enable default level3.step-okp)
             (%auto)
             (%enable default level2.step-okp)
             (%auto)
             (%enable default logic.appeal-step-okp))
 (%autoprove level6.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit level6.flag-proofp-aux))

(%autoadmit level6.proofp-aux)
(%autoadmit level6.proof-listp-aux)
(%autoprove definition-of-level6.proofp-aux
            (%enable default level6.proofp-aux level6.proof-listp-aux)
            (%restrict default level6.flag-proofp-aux (equal x 'x)))
(%autoprove definition-of-level6.proof-listp-aux
            (%enable default level6.proofp-aux level6.proof-listp-aux)
            (%restrict default level6.flag-proofp-aux (equal x 'x)))


(%autoprove level6.proofp-aux-when-not-consp      (%restrict default definition-of-level6.proofp-aux (equal x 'x)))
(%autoprove level6.proof-listp-aux-when-not-consp (%restrict default definition-of-level6.proof-listp-aux (equal x 'x)))
(%autoprove level6.proof-listp-aux-of-cons        (%restrict default definition-of-level6.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level6.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level6.proofp-aux (equal x 'x)))

(%autoprove booleanp-of-level6.proofp-aux      (%use (%instance (%thm lemma-for-booleanp-of-level6.proofp-aux) (flag 'proof))))
(%autoprove booleanp-of-level6.proof-listp-aux (%use (%instance (%thm lemma-for-booleanp-of-level6.proofp-aux) (flag 'list))))


(%deflist level6.proof-listp-aux (x axioms thms atbl)
          (level6.proofp-aux x axioms thms atbl))

(%autoprove lemma-for-logic.provablep-when-level6.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%urewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%restrict default definition-of-level6.proofp-aux (equal x 'x))
            (%auto :strategy (cleanup split urewrite))
            (%disable default
                      ;; so many memberp terms that these get expensive
                      memberp-when-memberp-of-cdr
                      memberp-when-not-subset-of-somep-cheap
                      memberp-when-not-superset-of-somep-cheap
                      type-set-like-rules
                      same-length-prefixes-equal-cheap
                      logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest))

(%autoprove logic.provablep-when-level6.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level6.proofp-aux) (flag 'proof))))

(%autoprove logic.provable-listp-when-level6.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level6.proofp-aux) (flag 'list))))



(%autoprove lemma-for-level6.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level6.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove level6.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level6.proofp-aux-when-logic.proofp) (flag 'proof))))

(%autoprove level6.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level6.proofp-aux-when-logic.proofp) (flag 'list))))

(%autoprove forcing-level6.proofp-aux-of-logic.provable-witness
            (%enable default level6.proofp-aux-when-logic.proofp))



(%autoadmit level6.proofp)
(%autoprove booleanp-of-level6.proofp
            (%enable default level6.proofp))
(%autoprove logic.provablep-when-level6.proofp
            (%enable default level6.proofp))


(defsection level6-transition
  (%install-new-proofp level6.proofp)
  (%auto)
  (%qed-install))


(%switch-builder clause.simple-split-bldr     clause.simple-split-bldr-high)
(%switch-builder clause.simple-limsplit-bldr  clause.simple-limsplit-bldr-high)
(%switch-builder clause.factor-bldr           clause.factor-bldr-high)



(%finish "level6")
(%save-events "level6.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
