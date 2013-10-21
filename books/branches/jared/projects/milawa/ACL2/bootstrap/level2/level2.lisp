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
