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
(include-book "elim") ;; BOZO for strip-conclusions-of-restn
(%interactive)


(%autoadmit tactic.crewrite-all-okp)

(%autoprove booleanp-of-tactic.crewrite-all-okp
            (%enable default tactic.crewrite-all-okp))


(%autoadmit tactic.crewrite-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.crewrite-all-tac
            (%enable default tactic.crewrite-all-tac))

(%autoprove forcing-tactic.crewrite-all-okp-of-tactic.crewrite-all-tac
            (%enable default
                     tactic.crewrite-all-tac
                     tactic.crewrite-all-okp))

(%autoadmit tactic.crewrite-all-compile)

(local (%enable default
                tactic.crewrite-all-okp
                tactic.crewrite-all-compile))


(%autoprove forcing-logic.appeal-listp-of-tactic.crewrite-all-compile
            (%auto)
            (%generalize (car (cdr (tatic.skeleton->extras x))) plans)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))))))
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X)))))))))))

(%autoprove forcing-logic.strip-conclusions-of-tactic.crewrite-all-compile
            (%auto)
            (%generalize (car (cdr (tatic.skeleton->extras x))) plans)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))))))
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X)))))))))))

(%autoprove forcing-logic.proof-listp-of-tactic.crewrite-all-compile
            (%disable default
                      unusual-memberp-rules
                      memberp-when-not-consp
                      MEMBERP-WHEN-MEMBERP-OF-CDR)
            (%auto)
            (%generalize (car (cdr (tatic.skeleton->extras x))) plans)
            (%generalize (tactic.skeleton->goals x) goals)
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))))))
            (%auto)
            (%fertilize (LOGIC.STRIP-CONCLUSIONS PROOFS)
                        (APP
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (RW.CREWRITE-CLAUSE-PLAN-LIST->CLAUSES-PRIME
                            (CAR (CDR (TACTIC.SKELETON->EXTRAS X))))))
                         (LOGIC.DISJOIN-EACH-FORMULA-LIST
                          (LOGIC.TERM-LIST-LIST-FORMULAS
                           (CLAUSE.MAKE-CLAUSES-FROM-ARBITRARY-FORMULAS
                            (REMOVE-DUPLICATES
                             (RW.CREWRITE-CLAUSE-PLAN-LIST->FORCED-GOALS
                              (CAR (CDR (TACTIC.SKELETON->EXTRAS X)))))))))))

(%ensure-exactly-these-rules-are-missing "../../tactics/crewrite-all")