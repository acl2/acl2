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
