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
(include-book "fast-crewrite-clause")
(%interactive)


(%autoprove nth-of-cons-when-constantp
            (%restrict default nth (equal n 'n)))

(%autoprove rw.crewrite-clause-aux-of-nil
            (%restrict default rw.crewrite-clause-aux (equal todo ''nil)))

(%autoprove rw.crewrite-clause-of-nil
            (%enable default rw.crewrite-clause))

(%autoprove tactic.world->index-under-iff
            (%disable default forcing-natp-of-tactic.world->index)
            (%use (%instance (%thm forcing-natp-of-tactic.world->index))))

(%autoprove tactic.find-world-of-nil
            (%cdr-induction worlds)
            (%restrict default tactic.find-world (equal worlds 'worlds)))



(%autoadmit rw.make-crewrite-clause-plan)
(%autoadmit rw.crewrite-clause-planp)
(%autoadmit rw.crewrite-clause-plan-okp)
(%autoadmit rw.crewrite-clause-plan-atblp)
(%autoadmit rw.crewrite-clause-plan->progressp)
(%autoadmit rw.crewrite-clause-plan->clause)
(%autoadmit rw.crewrite-clause-plan->provedp)
(%autoadmit rw.crewrite-clause-plan->clause-prime)
(%autoadmit rw.crewrite-clause-plan->forced-goals)
(%autoadmit rw.crewrite-clause-plan-compiler)



(%autoprove lemma-1-for-rw.crewrite-clause-plan)
(%autoprove lemma-2-for-rw.crewrite-clause-plan)
(%autoprove lemma-3-for-rw.crewrite-clause-plan)
(%autoprove lemma-4-for-rw.crewrite-clause-plan)
(%autoprove lemma-5-for-rw.crewrite-clause-plan)
(%autoprove lemma-6-for-rw.crewrite-clause-plan)
(%autoprove lemma-7-for-rw.crewrite-clause-plan)
(%autoprove lemma-8-for-rw.crewrite-clause-plan)
(%autoprove lemma-9-for-rw.crewrite-clause-plan)
(%autoprove lemma-10-for-rw.crewrite-clause-plan)
(%autoprove lemma-11-for-rw.crewrite-clause-plan)

(encapsulate
 ()
 (local (%enable default
                 lemma-1-for-rw.crewrite-clause-plan
                 lemma-2-for-rw.crewrite-clause-plan
                 lemma-3-for-rw.crewrite-clause-plan
                 lemma-4-for-rw.crewrite-clause-plan
                 lemma-5-for-rw.crewrite-clause-plan
                 lemma-6-for-rw.crewrite-clause-plan
                 lemma-7-for-rw.crewrite-clause-plan
                 lemma-8-for-rw.crewrite-clause-plan
                 lemma-9-for-rw.crewrite-clause-plan
                 lemma-10-for-rw.crewrite-clause-plan
                 lemma-11-for-rw.crewrite-clause-plan))

 (local (%enable default
                 rw.make-crewrite-clause-plan
                 rw.crewrite-clause-planp
                 rw.crewrite-clause-plan-okp
                 rw.crewrite-clause-plan-atblp
                 rw.crewrite-clause-plan->clause
                 rw.crewrite-clause-plan->provedp
                 rw.crewrite-clause-plan->clause-prime
                 rw.crewrite-clause-plan->forced-goals
                 rw.crewrite-clause-plan-compiler))

 (%autoprove booleanp-of-rw.crewrite-clause-planp)
 (%autoprove booleanp-of-rw.crewrite-clause-plan-okp)
 (%autoprove booleanp-of-rw.crewrite-clause-plan-atblp)

 (%autoprove consp-of-rw.crewrite-clause-plan->clause-prime)
 (%autoprove logic.term-listp-of-rw.crewrite-clause-plan->clause-prime)
 (%autoprove true-listp-of-rw.crewrite-clause-plan->forced-goals)
 (%autoprove logic.formula-listp-of-rw.crewrite-clause-plan->forced-goals)
 (%autoprove logic.formula-list-atblp-of-rw.crewrite-clause-plan->forced-goals)

 (%autoprove rw.crewrite-clause-plan->clause-of-rw.make-crewrite-clause-plan)
 (%autoprove rw.crewrite-clause-planp-of-rw.make-crewrite-clause-plan)
 (%autoprove rw.crewrite-clause-plan-okp-of-rw.make-crewrite-clause-plan)
 (%autoprove rw.crewrite-clause-plan-atblp-of-rw.make-crewrite-clause-plan)

 (%autoprove logic.appealp-of-rw.crewrite-clause-plan-compiler)
 (%autoprove logic.conclusion-of-rw.crewrite-clause-plan-compiler)
 (%autoprove logic.proofp-of-rw.crewrite-clause-plan-compiler
             (%disable default
                       type-set-like-rules
                       expensive-term/formula-inference
                       formula-decomposition
                       expensive-arithmetic-rules
                       expensive-arithmetic-rules-two
                       unusual-memberp-rules
                       unusual-subsetp-rules
                       unusual-consp-rules)))


(%deflist rw.crewrite-clause-plan-listp (x)
          (rw.crewrite-clause-planp x))

(%deflist rw.crewrite-clause-plan-list-okp (x world)
          (rw.crewrite-clause-plan-okp x world))

(%deflist rw.crewrite-clause-plan-list-atblp (x atbl)
          (rw.crewrite-clause-plan-atblp x atbl))

(%defprojection :list (rw.make-crewrite-clause-plan-list x fastp theoryname world)
                :element (rw.make-crewrite-clause-plan x fastp theoryname world))


(%autoadmit rw.crewrite-clause-plan-list->progressp)

(%defprojection :list (rw.crewrite-clause-plan-list->clauses x)
                :element (rw.crewrite-clause-plan->clause x))

(%autoprove rw.crewrite-clause-plan-list->clauses-of-rw.make-crewrite-clause-plan-list
            (%cdr-induction x))

(%autoadmit rw.crewrite-clause-plan-list->clauses-prime)

(%autoprove cons-listp-of-rw.crewrite-clause-plan-list->clauses-prime
            (%cdr-induction x)
            (%restrict default rw.crewrite-clause-plan-list->clauses-prime
                       (equal x 'x)))

(%autoprove logic.term-list-listp-of-rw.crewrite-clause-plan-list->clauses-prime
            (%cdr-induction x)
            (%restrict default rw.crewrite-clause-plan-list->clauses-prime
                       (equal x 'x)))

(%autoadmit rw.crewrite-clause-plan-list->forced-goals)

(%autoprove true-listp-of-rw.crewrite-clause-plan-list->forced-goals
            (%cdr-induction x)
            (%restrict default rw.crewrite-clause-plan-list->forced-goals
                       (equal x 'x)))

(%autoprove logic.formula-listp-of-rw.crewrite-clause-plan-list->forced-goals
            (%cdr-induction x)
            (%restrict default rw.crewrite-clause-plan-list->forced-goals
                       (equal x 'x)))

(%autoprove logic.formula-list-atblp-of-rw.crewrite-clause-plan-list->forced-goals
            (%cdr-induction x)
            (%restrict default rw.crewrite-clause-plan-list->forced-goals
                       (equal x 'x)))

(%autoprove rw.crewrite-clause-plan-listp-of-rw.make-crewrite-clause-plan-list
            (%cdr-induction x))

(%autoprove rw.crewrite-clause-plan-list-okp-of-rw.make-crewrite-clause-plan-list
            (%cdr-induction x))

(%autoprove rw.crewrite-clause-plan-list-atblp-of-rw.make-crewrite-clause-plan-list
            (%cdr-induction x))


(%autoadmit rw.crewrite-clause-plan-list-compiler)

(%autoprove logic.appeal-listp-of-rw.crewrite-clause-plan-list-compiler
            (%autoinduct rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
            (%restrict default rw.crewrite-clause-plan-list-compiler (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list->clauses-prime (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list->forced-goals (equal x 'x)))

(%autoprove logic.strip-conclusions-of-rw.crewrite-clause-plan-list-compiler
            (%autoinduct rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
            (%restrict default rw.crewrite-clause-plan-list-compiler (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list->clauses-prime (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list->forced-goals (equal x 'x))
            (%forcingp nil))

(%autoprove logic.proof-listp-of-rw.crewrite-clause-plan-list-compiler
            (%autoinduct rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
            (%restrict default rw.crewrite-clause-plan-list-compiler (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list->clauses-prime (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list->forced-goals (equal x 'x))
            (%forcingp nil)
            (%disable default unusual-consp-rules unusual-memberp-rules))

(%autoprove rw.crewrite-clause-plan-atblp-removal
            (%enable default
                     rw.crewrite-clause-plan-atblp
                     rw.crewrite-clause-plan->clause))

(%autoprove rw.crewrite-clause-plan-list-atblp-removal
            (%cdr-induction x)
            (%restrict default rw.crewrite-clause-plan-list->clauses (equal x 'x))
            (%restrict default rw.crewrite-clause-plan-list-atblp (equal x 'x)))



(%autoprove consp-of-rw.crewrite-clause-plan->clause
            (%enable default
                     rw.crewrite-clause-planp
                     rw.crewrite-clause-plan->clause))

(%autoprove logic.term-listp-of-rw.crewrite-clause-plan->clause
            (%enable default
                     rw.crewrite-clause-planp
                     rw.crewrite-clause-plan->clause))

(%autoadmit rw.crewrite-clause-plan-compiler-high)
(%autoadmit rw.crewrite-clause-plan-compiler-okp)


(%autoprove rw.crewrite-clause-plan-compiler-okp-of-rw.crewrite-clause-plan-compiler-high
            (%enable default
                     rw.crewrite-clause-plan-compiler-okp
                     rw.crewrite-clause-plan-compiler-high))


(encapsulate
 ()
 (local (%enable default rw.crewrite-clause-plan-compiler-okp))
 (%autoprove booleanp-of-rw.crewrite-clause-plan-compiler-okp)
 (%autoprove rw.crewrite-clause-plan-compiler-okp-of-logic.appeal-identity)
 (%autoprove lemma-1-for-soundness-of-rw.crewrite-clause-plan-compiler-okp)
 (%autoprove lemma-2-for-soundness-of-rw.crewrite-clause-plan-compiler-okp
             (%disable default
                       unusual-subsetp-rules
                       unusual-memberp-rules
                       unusual-consp-rules))
 (%autoprove forcing-soundness-of-rw.crewrite-clause-plan-compiler-okp
             (%disable default
                       unusual-subsetp-rules
                       unusual-memberp-rules
                       unusual-consp-rules)
             (%use (%instance (%thm lemma-1-for-soundness-of-rw.crewrite-clause-plan-compiler-okp)))
             (%use (%instance (%thm lemma-2-for-soundness-of-rw.crewrite-clause-plan-compiler-okp)))
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (let* ((plan        (second (logic.extras x)))
                                        (world      (tactic.find-world (first (logic.extras x)) worlds))
                                        (provedp    (rw.crewrite-clause-plan->provedp plan))
                                        (subproofs* (logic.provable-list-witness
                                                     (logic.strip-conclusions (logic.subproofs x))
                                                     axioms thms atbl))
                                        (proof      (if provedp nil (car subproofs*)))
                                        (fproofs    (if provedp subproofs* (cdr subproofs*))))
                                   (rw.crewrite-clause-plan-compiler plan world proof fproofs)))))))

(%ensure-exactly-these-rules-are-missing "../../tactics/crewrite-world")
