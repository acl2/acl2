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
(include-book "rewrite-world-bldrs")
(include-book "world-check")
(include-book "ancestors") ;; move to level 10?
(include-book "cachep") ;; move to level 10?
(include-book "fast-cache") ;; move to level 10?
(include-book "match-free") ;; move to level 10?



(local (%disable default
                 formula-decomposition
                 expensive-term/formula-inference
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 expensive-subsetp-rules
                 unusual-memberp-rules
                 unusual-consp-rules
                 unusual-subsetp-rules
                 memberp-when-memberp-of-cdr
                 subsetp-when-not-consp
                 subsetp-when-not-consp-two))


(%autoadmit level9.step-okp)

(encapsulate
 ()
 (local (%enable default level9.step-okp))
 (%autoprove soundness-of-level9.step-okp)
 (%autoprove level9.step-okp-when-level8.step-okp
             (%enable default level8.step-okp)
             (%auto)
             (%enable default level7.step-okp)
             (%auto)
             (%enable default level6.step-okp)
             (%auto)
             (%enable default level5.step-okp)
             (%auto)
             (%enable default level4.step-okp)
             (%auto)
             (%enable default level3.step-okp)
             (%auto)
             (%enable default level2.step-okp)
             (%auto)
             (%enable default logic.appeal-step-okp)
             (%auto))
 (%autoprove level9.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%forcingp nil))
 (local (%enable default expensive-arithmetic-rules))
 (%autoadmit level9.flag-proofp-aux))

(%autoadmit level9.proofp-aux)
(%autoadmit level9.proof-listp-aux)

(%autoprove definition-of-level9.proofp-aux
            (%enable default level9.proofp-aux level9.proof-listp-aux)
            (%restrict default level9.flag-proofp-aux (equal x 'x)))

(%autoprove definition-of-level9.proof-listp-aux
            (%enable default level9.proofp-aux level9.proof-listp-aux)
            (%restrict default level9.flag-proofp-aux (equal x 'x)))



(%autoprove level9.proofp-aux-when-not-consp
            (%enable default definition-of-level9.proofp-aux))

(%autoprove level9.proof-listp-aux-when-not-consp
            (%restrict default definition-of-level9.proof-listp-aux (equal x 'x)))

(%autoprove level9.proof-listp-aux-of-cons
            (%restrict default definition-of-level9.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level9.proofp-aux
            (%logic.appeal-induction flag x)
            (%enable default
                     definition-of-level9.proofp-aux
                     expensive-arithmetic-rules)
            (%forcingp nil))

(%autoprove booleanp-of-level9.proofp-aux
            (%use (%instance (%thm lemma-for-booleanp-of-level9.proofp-aux)
                             (flag 'proof))))

(%autoprove booleanp-of-level9.proof-listp-aux
            (%use (%instance (%thm lemma-for-booleanp-of-level9.proofp-aux)
                             (flag 'list))))

(%deflist level9.proof-listp-aux (x worlds defs axioms thms atbl)
  (level9.proofp-aux x worlds defs axioms thms atbl))

(%autoprove lemma-for-logic.provablep-when-level9.proofp-aux
            (%logic.appeal-induction flag x)
            (%splitlimit 2)
            (%liftlimit 8)
            (%disable default
                      forcing-true-listp-of-logic.subproofs
                      MEMBERP-WHEN-NOT-CONSP
                      CONSP-WHEN-CONSP-OF-CDR-CHEAP
                      LOOKUP-WHEN-NOT-CONSP
                      memberp-when-memberp-of-cdr
                      memberp-when-not-subset-of-somep-cheap
                      memberp-when-not-superset-of-somep-cheap
                      type-set-like-rules
                      same-length-prefixes-equal-cheap
                      logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest)
            (%waterfall default 100)
            (%restrict default definition-of-level9.proofp-aux (equal x 'x))
            (%enable default
                     expensive-arithmetic-rules
                     type-set-like-rules)
            (%waterfall default 100))

(%autoprove logic.provablep-when-level9.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level9.proofp-aux)
                             (flag 'proof))))

(%autoprove logic.provable-listp-when-level9.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level9.proofp-aux)
                             (flag 'list))))


(%autoprove lemma-for-level9.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level9.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x))
            (%enable default expensive-arithmetic-rules))

(%autoprove level9.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level9.proofp-aux-when-logic.proofp)
                             (flag 'proof))))

(%autoprove level9.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level9.proofp-aux-when-logic.proofp)
                             (flag 'list))))

(%autoprove forcing-level9.proofp-aux-of-logic.provable-witness
            (%enable default level9.proofp-aux-when-logic.proofp))

(%autoadmit level9.static-checksp)
(%enable default level9.static-checksp)

(%autoadmit level9.proofp)

(%autoprove booleanp-of-level9.proofp
            (%enable default level9.proofp))

(%autoprove logic.provablep-when-level9.proofp
            (%enable default
                     level9.proofp
                     expensive-term/formula-inference)
            (%disable default logic.provablep-when-level9.proofp-aux)
            (%use (%instance (%thm logic.provablep-when-level9.proofp-aux)
                             (x      (third (logic.extras x)))
                             (defs   (first (logic.extras x)))
                             (worlds (second (logic.extras x))))))

(defsection level9-transition
  (%install-new-proofp level9.proofp)
  (%auto)
  (%qed-install))

(ACL2::table tactic-harness 'current-adapter 'level9.adapter)

(%switch-builder rw.world-urewrite-list-bldr rw.world-urewrite-list-bldr-high)

;; This is special, we need to tell the interface to switch to the fast
;; urewriter during proofs.
(ACL2::table tactic-harness 'ufastp t)

(%finish "level9")
(%save-events "level9.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)

