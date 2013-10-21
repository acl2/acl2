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
(include-book "crewrite")
(%interactive)


(%autoprove rw.ccstep->clause-prime-under-iff
            (%enable default
                     rw.ccstep->clause-prime
                     rw.ccstep->provedp))

(%autoprove forcing-rw.eqtrace-okp-of-rw.assms->contradiction-and-rw.assms->hypbox-free)

(%autoprove forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-right
            (%enable default rw.assume-right))

(%autoprove forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-right-list
            (%cdr-induction nhyps))

(%autoprove forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-left
            (%enable default rw.assume-left))

(%autoprove forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-left-list
            (%cdr-induction nhyps))




(defsection rw.crewrite-take-step
  (%autoadmit rw.crewrite-take-step)
  (local (%enable default rw.crewrite-take-step))
  (%autoprove forcing-rw.ccstepp-of-rw.crewrite-take-step)
  (%autoprove forcing-rw.trace-okp-of-rw.ccstep->trace-of-rw.crewrite-take-step)
  (%autoprove forcing-rw.trace-atblp-of-rw.ccstep->trace-of-rw.crewrite-take-step)
  (%autoprove forcing-rw.ccstep-trace-env-okp-of-rw.ccstep->trace-of-rw.crewrite-take-step)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.ccstep->contradiction-of-rw.crewrite-take-step)
  (%autoprove forcing-logic.term-atblp-of-rw.ccstep->term-of-rw.crewrite-take-step)
  (%autoprove forcing-rw.hypbox-atblp-of-rw.ccstep->hypbox-of-rw.crewrite-take-step))




(defsection rw.crewrite-clause-aux

  (%autoadmit rw.crewrite-clause-aux)
  (local (%restrict default rw.crewrite-clause-aux (equal todo 'todo)))
  (local (%enable default rw.ccstep->provedp))

  (%autoprove forcing-rw.ccstep-listp-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux))

  (%autoprove forcing-rw.trace-list-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux))

  (%autoprove forcing-rw.trace-list-atblp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux))

  (%autoprove forcing-rw.trace-list-env-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux))

  (defthmd lemma-for-forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause-aux
    ;; BOZO unlocalize
    (implies (and (consp todo)
                  (consp (cdr todo))
                  (logic.term-listp todo)
                  (logic.term-listp done)
                  (rw.controlp control)
                  (not (rw.ccstep->provedp (rw.crewrite-take-step todo done blimit rlimit control n))))
             (equal
              (rw.ccstep->result-goal
               (rw.crewrite-take-step todo done blimit rlimit control n))
              (rw.ccstep->original-goal
               (rw.crewrite-take-step (cdr todo)
                                      (cons (rw.ccstep->t1prime
                                             (rw.crewrite-take-step todo done blimit rlimit control n))
                                            done)
                                      blimit rlimit control n))))
    :hints(("Goal"
            :in-theory (enable rw.crewrite-take-step
                               rw.ccstep->result-goal
                               rw.ccstep->original-goal
                               rw.ccstep->t1prime
                               rw.ccstep->provedp)
            :do-not-induct t)))

  (%autoprove lemma-for-forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause-aux
              (%enable default
                       rw.crewrite-take-step
                       rw.ccstep->result-goal
                       rw.ccstep->original-goal
                       rw.ccstep->t1prime
                       rw.ccstep->provedp))

  (%autoprove forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%enable default lemma-for-forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause-aux)
              (%restrict default rw.ccstep-list->compatiblep
                         (equal x '(CONS (RW.CREWRITE-TAKE-STEP TODO DONE BLIMIT RLIMIT CONTROL N) ACC))))

  (%autoprove forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%restrict default rw.ccstep-list->original-goal
                         (memberp x '(acc
                                      (CONS (RW.CREWRITE-TAKE-STEP TODO DONE BLIMIT RLIMIT CONTROL N) ACC))))
              (%restrict default rw.crewrite-clause-aux (equal todo '(cdr todo))))

  (%autoprove consp-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%restrict default rw.crewrite-clause-aux (memberp todo '(todo (cdr todo)))))


  (defthmd lemma-for-forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause-aux
    ;; BOZO unlocalize
    (implies (force (and (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)))
             (iff (rw.hypbox->left (rw.ccstep->hypbox (rw.crewrite-take-step todo done blimit rlimit control n)))
                  (consp (cdr todo))))
    :hints(("Goal" :in-theory (enable rw.crewrite-take-step))))

  (%autoprove lemma-for-forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause-aux
              (%enable default rw.crewrite-take-step))

  (%autoprove forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%enable default
                       rw.ccstep->terminalp
                       rw.ccstep->provedp
                       ;; BOZO i don't think we need this:
                       lemma-for-forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause-aux)
              (%restrict default rw.crewrite-clause-aux (memberp todo '(todo (cdr todo)))))

  (%autoprove forcing-rw.eqtrace-list-atblp-of-rw.ccstep-list-gather-contradictions-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%restrict default rw.crewrite-clause-aux (memberp todo '(todo (cdr todo)))))

  (%autoprove forcing-logic.term-list-atblp-of-rw.ccstep-list-terms-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%restrict default rw.crewrite-clause-aux (memberp todo '(todo (cdr todo)))))

  (%autoprove forcing-rw.hypbox-list-atblp-of-rw.ccstep-list-hypboxes-of-rw.crewrite-clause-aux
              (%autoinduct rw.crewrite-clause-aux)
              (%restrict default rw.crewrite-clause-aux (memberp todo '(todo (cdr todo))))))



(defsection rw.crewrite-clause

  (%autoadmit rw.crewrite-clause)

  (local (%enable default rw.crewrite-clause))

  (%autoprove forcing-rw.ccstep-listp-of-rw.crewrite-clause)
  (%autoprove forcing-rw.ccstep-listp-of-rw.crewrite-clause-free)
  (%autoprove forcing-rw.trace-list-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause)
  (%autoprove forcing-rw.trace-list-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-free)
  (%autoprove forcing-rw.trace-list-atblp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause)
  (%autoprove forcing-rw.trace-list-atblp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-free)
  (%autoprove forcing-rw.trace-list-env-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause)
  (%autoprove forcing-rw.trace-list-env-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-free)
  (%autoprove forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause)

  (defthmd lemma-for-forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause
    ;; BOZO unlocalize
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)))
             (equal (rw.ccstep->original-goal (rw.crewrite-take-step clause nil blimit rlimit control n))
                    (clause.clause-formula clause)))
    :hints(("Goal" :in-theory (enable rw.ccstep->original-goal
                                      rw.crewrite-take-step))))

  (%autoprove lemma-for-forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause
              (%enable default rw.ccstep->original-goal rw.crewrite-take-step))

  (%autoprove forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause
              (%enable default lemma-for-forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause))

  (%autoprove forcing-consp-of-rw.crewrite-clause)
  ;; BOZO ACL2 uses "lemma2" here which we don't seem to need
  (%autoprove forcing-rw.ccstep->result-goal-of-car-of-cdr-of-rw.crewrite-clause)
  (%autoprove forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause)
  (%autoprove forcing-rw.eqtrace-list-atblp-of-rw.ccstep-list-gather-contradictions-of-rw.crewrite-clause)
  (%autoprove forcing-logic.term-list-atblp-of-rw.ccstep-list-terms-of-rw.crewrite-clause)
  (%autoprove forcing-rw.hypbox-list-atblp-of-rw.ccstep-list-hypboxes-of-rw.crewrite-clause))




(defsection rw.crewrite-clause-bldr
  (%autoadmit rw.crewrite-clause-bldr)
  (local (%enable default rw.crewrite-clause-bldr))
  (%autoprove forcing-logic.appealp-of-rw.crewrite-clause-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.crewrite-clause-bldr)
  (%autoprove forcing-logic.proofp-of-rw.crewrite-clause-bldr))



(%defprojection :list (rw.crewrite-clause-list x blimit rlimit control n)
                :element (rw.crewrite-clause x blimit rlimit control n))

(%autoprove forcing-cons-listp-of-rw.crewrite-clause-list
            (%cdr-induction x))

(%autoprove forcing-rw.ccstep-list-listp-of-rw.crewrite-clause-list
            (%cdr-induction x))

(%autoprove forcing-rw.ccstep-list-listp-of-rw.crewrite-clause-list-free)

(%autoprove forcing-rw.trace-list-atblp-of-rw.ccstep-list-list-gather-traces-of-rw.crewrite-clause-list
            (%cdr-induction x))

(%autoprove forcing-rw.trace-list-atblp-of-rw.ccstep-list-list-gather-traces-of-rw.crewrite-clause-list-free)




(%autoadmit rw.ccstep-list-list-terminalp)

(%autoprove rw.ccstep-list-list-terminalp-when-not-consp
            (%restrict default rw.ccstep-list-list-terminalp (equal x 'x)))

(%autoprove rw.ccstep-list-list-terminalp-of-cons
            (%restrict default rw.ccstep-list-list-terminalp (equal x '(cons a x))))

(%autoprove rw.ccstep-list-list-terminalp-of-rw.crewrite-clause-list
            (%cdr-induction x))



(%autoadmit rw.ccstep-list-list-obligations)

(%autoprove true-listp-of-rw.ccstep-list-list-obligations
            (%autoinduct rw.ccstep-list-list-obligations)
            (%restrict default rw.ccstep-list-list-obligations (equal x 'x)))

(%autoprove forcing-cons-listp-of-rw.ccstep-list-list-obligations
            (%autoinduct rw.ccstep-list-list-obligations)
            (%restrict default rw.ccstep-list-list-obligations (equal x 'x)))

(%autoprove forcing-logic.term-list-listp-of-rw.ccstep-list-list-obligations
            (%autoinduct rw.ccstep-list-list-obligations)
            (%restrict default rw.ccstep-list-list-obligations (equal x 'x)))

(%autoprove forcing-logic.term-list-listp-of-rw.ccstep-list-list-obligations-free)




(defsection rw.crewrite-clause-list-bldr

  (%autoadmit rw.crewrite-clause-list-bldr)

  (local (%restrict default rw.crewrite-clause-list-bldr (equal clauses 'clauses)))

  (local (%restrict default rw.ccstep-list-list-obligations
                    (equal x '(RW.CREWRITE-CLAUSE-LIST CLAUSES BLIMIT RLIMIT CONTROL N))))

  (local (%disable default
                   expensive-term/formula-inference
                   unusual-subsetp-rules
                   unusual-memberp-rules
                   unusual-consp-rules
                   formula-decomposition
                   expensive-arithmetic-rules
                   expensive-arithmetic-rules-two
                   same-length-prefixes-equal-cheap
                   type-set-like-rules))

  (%autoprove forcing-logic.appeal-listp-of-rw.crewrite-clause-list-bldr
              (%autoinduct rw.crewrite-clause-list-bldr))

  (%autoprove forcing-logic.strip-conclusions-of-rw.crewrite-clause-list-bldr
              (%autoinduct rw.crewrite-clause-list-bldr))

  (%autoprove forcing-logic.proof-listp-of-rw.crewrite-clause-list-bldr
              (%autoinduct rw.crewrite-clause-list-bldr)
              (%disable default
                        memberp-when-not-consp
                        memberp-when-memberp-of-cdr
                        subsetp-transitive-two)))



(%autoadmit rw.crewrite-records-show-progressp)

