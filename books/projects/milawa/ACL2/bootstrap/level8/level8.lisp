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
;; Software Foundation, Inc., 61 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "ccstep-check")
(%interactive)

(%autoadmit level8.step-okp)

(encapsulate
 ()
 (local (%enable default level8.step-okp))
 (%autoprove soundness-of-level8.step-okp)
 (%autoprove level8.step-okp-when-level7.step-okp
             (%forcingp nil)
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
             (%enable default logic.appeal-step-okp))
 (%autoprove level8.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit level8.flag-proofp-aux))

(%autoadmit level8.proofp-aux)
(%autoadmit level8.proof-listp-aux)
(%autoprove definition-of-level8.proofp-aux
            (%enable default level8.proofp-aux level8.proof-listp-aux)
            (%restrict default level8.flag-proofp-aux (equal x 'x)))
(%autoprove definition-of-level8.proof-listp-aux
            (%enable default level8.proofp-aux level8.proof-listp-aux)
            (%restrict default level8.flag-proofp-aux (equal x 'x)))


(%autoprove level8.proofp-aux-when-not-consp      (%restrict default definition-of-level8.proofp-aux (equal x 'x)))
(%autoprove level8.proof-listp-aux-when-not-consp (%restrict default definition-of-level8.proof-listp-aux (equal x 'x)))
(%autoprove level8.proof-listp-aux-of-cons        (%restrict default definition-of-level8.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level8.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level8.proofp-aux (equal x 'x)))

(%autoprove booleanp-of-level8.proofp-aux      (%use (%instance (%thm lemma-for-booleanp-of-level8.proofp-aux) (flag 'proof))))
(%autoprove booleanp-of-level8.proof-listp-aux (%use (%instance (%thm lemma-for-booleanp-of-level8.proofp-aux) (flag 'list))))


(%deflist level8.proof-listp-aux (x axioms thms atbl)
          (level8.proofp-aux x axioms thms atbl))

(%autoprove lemma-for-logic.provablep-when-level8.proofp-aux
            (%splitlimit 15)
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%urewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%restrict default definition-of-level8.proofp-aux (equal x 'x))
            (%auto :strategy (cleanup split urewrite))
            (%disable default
                      ;; so many memberp terms that these get expensive
                      memberp-when-memberp-of-cdr
                      memberp-when-not-subset-of-somep-cheap
                      memberp-when-not-superset-of-somep-cheap
                      type-set-like-rules
                      same-length-prefixes-equal-cheap
                      logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest))

(%autoprove logic.provablep-when-level8.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level8.proofp-aux) (flag 'proof))))

(%autoprove logic.provable-listp-when-level8.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level8.proofp-aux) (flag 'list))))



(%autoprove lemma-for-level8.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level8.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove level8.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level8.proofp-aux-when-logic.proofp) (flag 'proof))))

(%autoprove level8.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level8.proofp-aux-when-logic.proofp) (flag 'list))))

(%autoprove forcing-level8.proofp-aux-of-logic.provable-witness
            (%enable default level8.proofp-aux-when-logic.proofp))



(%autoadmit level8.proofp)
(%autoprove booleanp-of-level8.proofp
            (%enable default level8.proofp))
(%autoprove logic.provablep-when-level8.proofp
            (%enable default level8.proofp)
            (%disable default logic.provablep-when-level8.proofp-aux)
            (%use (%instance (%thm logic.provablep-when-level8.proofp-aux)
                             (x    (second (logic.extras x)))
                             (defs (first (logic.extras x)))))
            (%disable default
                      memberp-when-memberp-of-cdr
                      memberp-when-not-subset-of-somep-cheap
                      memberp-when-not-superset-of-somep-cheap
                      logic.provablep-of-car-when-logic.provable-listp-free
                      logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules))


(defsection level8-transition
  (%install-new-proofp level8.proofp)
  (%auto)
  (%qed-install))

(ACL2::table tactic-harness 'current-adapter 'level8.adapter)

(%switch-builder rw.ccstep-list-bldr rw.ccstep-list-bldr-high)
(%switch-builder rw.compile-trace rw.compile-trace-high)



(%finish "level8")
(%save-events "level8.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
