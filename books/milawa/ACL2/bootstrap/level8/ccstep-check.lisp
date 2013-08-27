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
(include-book "ccsteps")
(include-book "ccstep-arities")
(%interactive)


(%autoprove forcing-rw.hypbox-listp-of-rw.ccstep-list-hypboxes
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-rw.ccstep-list-terms
            (%cdr-induction x))

(%autoprove forcing-rw.trace-listp-of-rw.ccstep-list-gather-traces
            (%cdr-induction x))

(%autoprove forcing-rw.eqtrace-listp-of-rw.ccstep-list-gather-contradictions
            (%cdr-induction x))

(%autoprove forcing-logic.formulap-of-rw.ccstep-list->original-goal
            (%cdr-induction x)
            (%restrict default rw.ccstep-list->original-goal (equal x 'x))
            (%enable default rw.ccstep->original-goal))

(%autoprove logic.provable-listp-of-remove-duplicates-when-logic.provable-listp-free)



(defsection rw.ccstep-list-bldr-okp

  (%autoadmit rw.ccstep-list-bldr-okp)
  (%autoadmit rw.ccstep-list-bldr-high)

  (local (%enable default
                  rw.ccstep-list-bldr-okp
                  rw.ccstep-list-bldr-high))

  (%autoprove rw.ccstep-list-bldr-okp-of-rw.ccstep-list-bldr-high)

  (local (%disable default
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   memberp-when-not-consp
                   memberp-when-not-subset-of-somep-cheap
                   memberp-when-not-superset-of-somep-cheap
                   memberp-when-memberp-of-cdr
                   in-superset-when-in-subset-one
                   not-in-subset-when-not-in-superset-two
                   subset-of-somep-when-obvious-alt
                   superset-of-somep-when-obvious-alt
                   memberp-when-logic.all-terms-larger-cheap))

  (%autoprove booleanp-of-rw.ccstep-list-bldr-okp)
  (%autoprove rw.ccstep-list-bldr-okp-of-logic.appeal-identity)
  (%autoprove lemma-1-for-soundness-of-rw.ccstep-list-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-rw.ccstep-list-bldr-okp)

  (%autoprove forcing-soundness-of-rw.ccstep-list-bldr-okp
              (%use (%instance (%thm lemma-1-for-soundness-of-rw.ccstep-list-bldr-okp)))
              (%use (%instance (%thm lemma-2-for-soundness-of-rw.ccstep-list-bldr-okp)))
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.ccstep-list-bldr (logic.extras x)
                                                       defs
                                                       (if (rw.ccstep->provedp (first (logic.extras x)))
                                                           nil
                                                         (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                                                 axioms thms atbl))
                                                       (logic.provable-list-witness (RW.CCSTEP-LIST-FORCED-GOALS (LOGIC.EXTRAS X))
                                                                                    axioms thms atbl)))))))


(%ensure-exactly-these-rules-are-missing "../../rewrite/ccstep-check")

