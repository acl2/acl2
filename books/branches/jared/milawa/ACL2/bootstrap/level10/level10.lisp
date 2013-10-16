;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "crewrite-world")
(%interactive)

(%autoadmit level10.step-okp)

(encapsulate
 ()
 (local (%enable default level10.step-okp))
 (%autoprove soundness-of-level10.step-okp)
 (%autoprove level10.step-okp-when-level9.step-okp
             (%enable default level9.step-okp)
             (%auto)
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
 (%autoprove level10.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%forcingp nil))
 (local (%enable default expensive-arithmetic-rules))
 (%autoadmit level10.flag-proofp-aux))

(%autoadmit level10.proofp-aux)
(%autoadmit level10.proof-listp-aux)

(%autoprove definition-of-level10.proofp-aux
            (%enable default level10.proofp-aux level10.proof-listp-aux)
            (%restrict default level10.flag-proofp-aux (equal x 'x)))

(%autoprove definition-of-level10.proof-listp-aux
            (%enable default level10.proofp-aux level10.proof-listp-aux)
            (%restrict default level10.flag-proofp-aux (equal x 'x)))

(%autoprove level10.proofp-aux-when-not-consp
            (%enable default definition-of-level10.proofp-aux))

(%autoprove level10.proof-listp-aux-when-not-consp
            (%restrict default definition-of-level10.proof-listp-aux (equal x 'x)))

(%autoprove level10.proof-listp-aux-of-cons
            (%restrict default definition-of-level10.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level10.proofp-aux
            (%logic.appeal-induction flag x)
            (%enable default
                     definition-of-level10.proofp-aux
                     expensive-arithmetic-rules)
            (%forcingp nil))

(%autoprove booleanp-of-level10.proofp-aux
            (%use (%instance (%thm lemma-for-booleanp-of-level10.proofp-aux)
                             (flag 'proof))))

(%autoprove booleanp-of-level10.proof-listp-aux
            (%use (%instance (%thm lemma-for-booleanp-of-level10.proofp-aux)
                             (flag 'list))))

(%deflist level10.proof-listp-aux (x worlds defs axioms thms atbl)
          (level10.proofp-aux x worlds defs axioms thms atbl))




(%autoprove lemma-for-logic.provablep-when-level10.proofp-aux
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
                      unusual-consp-rules
                      unusual-memberp-rules
                      unusual-subsetp-rules
                      same-length-prefixes-equal-cheap
                      logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest)
            (%waterfall default 100)
            (%restrict default definition-of-level10.proofp-aux (equal x 'x))
            (%enable default
                     expensive-arithmetic-rules
                     type-set-like-rules)
            (%waterfall default 100))

(%autoprove logic.provablep-when-level10.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level10.proofp-aux)
                             (flag 'proof))))

(%autoprove logic.provable-listp-when-level10.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level10.proofp-aux)
                             (flag 'list))))


(%autoprove lemma-for-level10.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level10.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x))
            (%enable default expensive-arithmetic-rules))

(%autoprove level10.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level10.proofp-aux-when-logic.proofp)
                             (flag 'proof))))

(%autoprove level10.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level10.proofp-aux-when-logic.proofp)
                             (flag 'list))))



(%autoprove forcing-level10.proofp-aux-of-logic.provable-witness
            (%enable default level10.proofp-aux-when-logic.proofp))


(%autoadmit level10.static-checksp)
(%enable default level10.static-checksp)

(%autoadmit level10.proofp)

(%autoprove booleanp-of-level10.proofp
            (%enable default level10.proofp))

(%autoprove logic.provablep-when-level10.proofp
            (%enable default level10.proofp)
            (%disable default
                      logic.provablep-when-level10.proofp-aux
                      unusual-memberp-rules
                      memberp-when-memberp-of-cdr
                      memberp-when-not-consp
                      unusual-consp-rules
                      expensive-term/formula-inference
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      formula-decomposition
                      )
            (%use (%instance (%thm logic.provablep-when-level10.proofp-aux)
                             (x      (third (logic.extras x)))
                             (defs   (first (logic.extras x)))
                             (worlds (second (logic.extras x)))))
            (%auto :strategy (cleanup split crewrite))
            (%enable default expensive-term/formula-inference))

(defsection level10-transition
  (%install-new-proofp level10.proofp)
  (%auto)
  (%qed-install))

(ACL2::table tactic-harness 'current-adapter 'level10.adapter)

(%switch-builder rw.crewrite-clause-plan-compiler rw.crewrite-clause-plan-compiler-high)

;; This is special, we need to tell the interface to switch to the fast
;; crewriter during proofs.
(ACL2::table tactic-harness 'cfastp t)

(%finish "level10")
(%save-events "level10.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)


