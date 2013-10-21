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
(include-book "skeletonp")
(include-book "elim") ;; bozo for strip-conclusions-of-restn, etc.
(%interactive)



(%autoadmit tactic.crewrite-first-okp)

(%autoprove booleanp-of-tactic.crewrite-first-okp
            (%enable default tactic.crewrite-first-okp))


(%autoadmit tactic.crewrite-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.crewrite-first-tac
            (%enable default tactic.crewrite-first-tac))

(%autoprove forcing-tactic.crewrite-first-okp-of-tactic.crewrite-first-tac
            (%enable default
                     tactic.crewrite-first-tac
                     tactic.crewrite-first-okp))


(%autoadmit tactic.crewrite-first-compile)

(local (%enable default
                tactic.crewrite-first-okp
                tactic.crewrite-first-compile))

(%autoprove forcing-logic.appeal-listp-of-tactic.crewrite-first-compile
            (%auto :strategy (cleanup split urewrite))
            (%generalize (car (cdr (tactic.skeleton->extras x))) plan)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default dangerous-decomposition-of-app)
            (%auto))

(%autoprove forcing-logic.strip-conclusions-of-tactic.crewrite-first-compile
            (%auto :strategy (cleanup split urewrite))
            (%generalize (car (cdr (tactic.skeleton->extras x))) plan)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default dangerous-decomposition-of-app)
            (%auto))

(%autoprove forcing-logic.proof-listp-of-tactic.crewrite-first-compile
            (%disable default
                      unusual-memberp-rules
                      memberp-when-not-consp
                      MEMBERP-WHEN-MEMBERP-OF-CDR)
            (%auto)
            (%generalize (car (cdr (tactic.skeleton->extras x))) plan)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)

            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CDR (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (RW.CREWRITE-CLAUSE-PLAN->FORCED-GOALS PLAN))))))
            (%auto)

            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS2)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CDR (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (RW.CREWRITE-CLAUSE-PLAN->FORCED-GOALS PLAN))))))
            (%auto))


(%ensure-exactly-these-rules-are-missing "../../tactics/crewrite-first")
