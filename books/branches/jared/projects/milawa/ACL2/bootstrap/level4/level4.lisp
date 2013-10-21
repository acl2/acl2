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
(include-book "aux-limsplit-cutoff-bldr")
(include-book "aux-split-positive")
(include-book "aux-split-negative")
(include-book "aux-split-misc")
(include-book "casesplit")
(include-book "ccsteps")
(include-book "clause-basics")
(include-book "clean-clauses")
(include-book "crewrite-rule")
(include-book "eval")
(include-book "equal-by-args")
(include-book "factor-bldr")
(include-book "update-clause")
(include-book "clause-compiler")
(%interactive)


(%autoadmit level4.step-okp)

(encapsulate
 ()
 (local (%enable default level4.step-okp))
 (%autoprove soundness-of-level4.step-okp)
 (%autoprove level4.step-okp-when-level3.step-okp
             (%forcingp nil)
             (%auto)
             (%enable default level3.step-okp)
             (%auto)
             (%enable default level2.step-okp)
             (%auto)
             (%enable default logic.appeal-step-okp))
 (%autoprove level4.step-okp-when-not-consp
             (%enable default logic.method)))

(encapsulate
 ()
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit level4.flag-proofp-aux))

(%autoadmit level4.proofp-aux)
(%autoadmit level4.proof-listp-aux)
(%autoprove definition-of-level4.proofp-aux
            (%enable default level4.proofp-aux level4.proof-listp-aux)
            (%restrict default level4.flag-proofp-aux (equal x 'x)))
(%autoprove definition-of-level4.proof-listp-aux
            (%enable default level4.proofp-aux level4.proof-listp-aux)
            (%restrict default level4.flag-proofp-aux (equal x 'x)))


(%autoprove level4.proofp-aux-when-not-consp      (%restrict default definition-of-level4.proofp-aux (equal x 'x)))
(%autoprove level4.proof-listp-aux-when-not-consp (%restrict default definition-of-level4.proof-listp-aux (equal x 'x)))
(%autoprove level4.proof-listp-aux-of-cons        (%restrict default definition-of-level4.proof-listp-aux (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-level4.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level4.proofp-aux (equal x 'x)))

(%autoprove booleanp-of-level4.proofp-aux      (%use (%instance (%thm lemma-for-booleanp-of-level4.proofp-aux) (flag 'proof))))
(%autoprove booleanp-of-level4.proof-listp-aux (%use (%instance (%thm lemma-for-booleanp-of-level4.proofp-aux) (flag 'list))))


(%deflist level4.proof-listp-aux (x axioms thms atbl)
          (level4.proofp-aux x axioms thms atbl))

(%autoprove lemma-for-logic.provablep-when-level4.proofp-aux
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default definition-of-level4.proofp-aux (equal x 'x))
            (%auto :strategy (cleanup urewrite split)))

(%autoprove logic.provablep-when-level4.proofp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level4.proofp-aux) (flag 'proof))))

(%autoprove logic.provable-listp-when-level4.proof-listp-aux
            (%use (%instance (%thm lemma-for-logic.provablep-when-level4.proofp-aux) (flag 'list))))



(%autoprove lemma-for-level4.proofp-aux-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%auto)
            (%restrict default definition-of-level4.proofp-aux (equal x 'x))
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove level4.proofp-aux-when-logic.proofp
            (%use (%instance (%thm lemma-for-level4.proofp-aux-when-logic.proofp) (flag 'proof))))

(%autoprove level4.proof-listp-aux-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-level4.proofp-aux-when-logic.proofp) (flag 'list))))

(%autoprove forcing-level4.proofp-aux-of-logic.provable-witness
            (%enable default level4.proofp-aux-when-logic.proofp))



(%autoadmit level4.proofp)
(%autoprove booleanp-of-level4.proofp
            (%enable default level4.proofp))
(%autoprove logic.provablep-when-level4.proofp
            (%enable default level4.proofp))


(defsection level4-transition
  (%install-new-proofp level4.proofp)
  (%auto)
  (%qed-install))


(%switch-builder clause.substitute-iff-into-literal-bldr            clause.substitute-iff-into-literal-bldr-high)
(%switch-builder clause.disjoined-substitute-iff-into-literal-bldr  clause.disjoined-substitute-iff-into-literal-bldr-high)
(%switch-builder clause.standardize-negative-term-bldr              clause.standardize-negative-term-bldr-high)
(%switch-builder clause.standardize-double-negative-term-bldr       clause.standardize-double-negative-term-bldr-high)

(%switch-builder clause.aux-split-double-negate-lemma1-bldr         clause.aux-split-double-negate-lemma1-bldr-high)
(%switch-builder clause.aux-split-double-negate-lemma2-bldr         clause.aux-split-double-negate-lemma2-bldr-high)
(%switch-builder clause.aux-split-positive-bldr                     clause.aux-split-positive-bldr-high)
(%switch-builder clause.aux-split-positive-1-bldr                   clause.aux-split-positive-1-bldr-high)
(%switch-builder clause.aux-split-positive-2-bldr                   clause.aux-split-positive-2-bldr-high)
(%switch-builder clause.aux-split-negative-bldr                     clause.aux-split-negative-bldr-high)
(%switch-builder clause.disjoined-aux-split-negative-bldr           clause.disjoined-aux-split-negative-bldr-high)
;(%switch-builder clause.aux-split-negative-1-bldr                   clause.aux-split-negative-1-bldr-high)
;(%switch-builder clause.aux-split-negative-2-bldr                   clause.aux-split-negative-2-bldr-high)
(%switch-builder clause.aux-split-default-1-bldr                    clause.aux-split-default-1-bldr-high)
(%switch-builder clause.aux-split-default-2-bldr                    clause.aux-split-default-2-bldr-high)
(%switch-builder clause.aux-limsplit-cutoff-bldr-nice               clause.aux-limsplit-cutoff-bldr-nice)

(%switch-builder clause.casesplit-lemma1-bldr                       clause.casesplit-lemma1-bldr-high)
(%switch-builder clause.disjoined-casesplit-lemma1-bldr             clause.disjoined-casesplit-lemma1-bldr-high)

(%switch-builder clause.aux-update-clause-lemma1-bldr               clause.aux-update-clause-lemma1-bldr-high)
(%switch-builder clause.aux-update-clause-lemma2-bldr               clause.aux-update-clause-lemma2-bldr-high)
(%switch-builder clause.aux-update-clause-iff-lemma1-bldr           clause.aux-update-clause-iff-lemma1-bldr-high)
(%switch-builder clause.aux-update-clause-iff-lemma2-bldr           clause.aux-update-clause-iff-lemma2-bldr-high)

(%switch-builder rw.ccstep-lemma-1                                  rw.ccstep-lemma-1-high)
(%switch-builder rw.ccstep-lemma-2                                  rw.ccstep-lemma-2-high)
(%switch-builder rw.ccstep-lemma-3                                  rw.ccstep-lemma-3-high)
(%switch-builder rw.ccstep-lemma-4                                  rw.ccstep-lemma-4-high)

(%switch-builder clause.obvious-term-bldr                           clause.obvious-term-bldr-high)

(%switch-builder eval-lemma-1-bldr                                  eval-lemma-1-bldr-high)
(%switch-builder eval-lemma-2-bldr                                  eval-lemma-2-bldr-high)

(%switch-builder rw.compile-crewrite-rule-trace-lemma1              rw.compile-crewrite-rule-trace-lemma1-high)
(%switch-builder rw.compile-crewrite-rule-trace-lemma2              rw.compile-crewrite-rule-trace-lemma2-high)

(%switch-builder clause.factor-bldr-lemma-1                         clause.factor-bldr-lemma-1-high)
(%switch-builder clause.factor-bldr-lemma-2                         clause.factor-bldr-lemma-2-high)

(%switch-builder build.equal-by-args                                build.equal-by-args-high)
(%switch-builder build.disjoined-equal-by-args                      build.disjoined-equal-by-args-high)

(%switch-builder clause.prove-arbitrary-formula-from-its-clause     clause.prove-arbitrary-formula-from-its-clause-high)

(%finish "level4")
(%save-events "level4.events")

;; Clear out the thmfiles table since we'll use the saved image from now on.
(ACL2::table tactic-harness 'thmfiles nil)
