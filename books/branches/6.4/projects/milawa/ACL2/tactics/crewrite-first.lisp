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
(include-book "colors")
(include-book "skeletonp")
(include-book "worldp")
(include-book "crewrite-world")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(local
 (encapsulate
  ()
  (defthm logic.strip-conclusions-of-restn
    ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
    ;; belongs and try using it globally.
    (equal (logic.strip-conclusions (restn n x))
           (restn n (logic.strip-conclusions x))))

  (in-theory (disable restn-of-logic.strip-conclusions))

  (ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-restn)
                                              (:rewrite restn-of-logic.strip-conclusions)))


  (defthm logic.strip-conclusions-of-firstn
    ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
    ;; belongs and try using it globally.
    (equal (logic.strip-conclusions (firstn n x))
           (firstn n (logic.strip-conclusions x))))

  (in-theory (disable firstn-of-logic.strip-conclusions))

  (ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-firstn)
                                              (:rewrite firstn-of-logic.strip-conclusions)))))



(defund tactic.crewrite-first-okp (x worlds)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds))
                  :guard-debug t))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'crewrite-first)
         (let* ((windex (first extras))
                (plan   (second extras))
                (world  (tactic.find-world windex worlds)))
           (and world
                (rw.crewrite-clause-planp plan)
                (rw.crewrite-clause-plan-okp plan world)
                (rw.crewrite-clause-plan->progressp plan)
                (let ((old-goals (tactic.skeleton->goals history))
                      (forced-clauses (clause.make-clauses-from-arbitrary-formulas
                                       (rw.crewrite-clause-plan->forced-goals plan))))
                  (and (consp old-goals)
                       (equal (rw.crewrite-clause-plan->clause plan) (car old-goals))
                       (equal goals
                              (if (rw.crewrite-clause-plan->provedp plan)
                                  (fast-app (cdr old-goals) forced-clauses)
                                (cons (rw.crewrite-clause-plan->clause-prime plan)
                                      (fast-app (cdr old-goals) forced-clauses)))))))))))

(defthm booleanp-of-tactic.crewrite-first-okp
  (equal (booleanp (tactic.crewrite-first-okp x worlds))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.crewrite-first-okp)
                                 ((:executable-counterpart acl2::force))))))




(defund tactic.crewrite-first-tac (x theoryname fastp world warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.worldp world)
                              (booleanp warnp))))
  (let* ((goals      (tactic.skeleton->goals x))
         (windex     (tactic.world->index world))
         (findtheory (lookup theoryname (tactic.world->theories world))))
    (cond ((not (consp goals))
           (and warnp
                (ACL2::cw "~s0crewrite-first-tac failure~s1: all clauses have already been proven.~%" *red* *black*)))
          ((not findtheory)
           (and warnp
                (ACL2::cw "~s0crewrite-first-tac failure~s1: no theory named ~s2 is defined.~%" *red* *black* theoryname)))
          (t
           (let* ((plan      (rw.make-crewrite-clause-plan (car goals) fastp theoryname world))
                  (progressp (rw.crewrite-clause-plan->progressp plan))
                  (provedp   (rw.crewrite-clause-plan->provedp plan))
                  (fgoals    (rw.crewrite-clause-plan->forced-goals plan))
                  (fclauses  (clause.make-clauses-from-arbitrary-formulas fgoals)))
             (cond ((not progressp)
                    (ACL2::cw "~s0crewrite-first-tac failure~s1: no progress was made.~%" *red* *black*))
                   (t
                    (tactic.extend-skeleton (if provedp
                                                (app (cdr goals) fclauses)
                                              (cons (rw.crewrite-clause-plan->clause-prime plan)
                                                    (app (cdr goals) fclauses)))
                                            'crewrite-first
                                            (list windex plan)
                                            x))))))))

(defthm forcing-tactic.skeletonp-of-tactic.crewrite-first-tac
  (implies (and (tactic.crewrite-first-tac x theoryname fastp world warnp)
                (force (tactic.skeletonp x))
                (force (tactic.worldp world)))
           (equal (tactic.skeletonp (tactic.crewrite-first-tac x theoryname fastp world warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.crewrite-first-tac))))

(defthm forcing-tactic.crewrite-first-okp-of-tactic.crewrite-first-tac
  (implies (and (tactic.crewrite-first-tac x theoryname fastp world warnp)
                (force (tactic.worldp world))
                (force (tactic.world-listp worlds))
                (force (tactic.skeletonp x))
                (force (equal world (tactic.find-world (tactic.world->index world) worlds))))
           (equal (tactic.crewrite-first-okp
                   (tactic.crewrite-first-tac x theoryname fastp world warnp)
                   worlds)
                  t))
  :hints(("Goal" :in-theory (enable tactic.crewrite-first-tac
                                    tactic.crewrite-first-okp))))




(defund tactic.crewrite-first-compile (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (logic.appeal-listp proofs)
                              (tactic.crewrite-first-okp x worlds)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history        (tactic.skeleton->history x))
         (old-goals      (tactic.skeleton->goals history))
         (extras         (tactic.skeleton->extras x))
         (windex         (first extras))
         (plan           (second extras))
         (world          (tactic.find-world windex worlds))
         (provedp        (rw.crewrite-clause-plan->provedp plan))
         (fgoals         (rw.crewrite-clause-plan->forced-goals plan))
         (num-old-proofs (fast-len (cdr old-goals) 0)))
    (if provedp
        ;; We need to generate the first proof from scratch
        (let* ((cdr-old-goals-proofs (firstn num-old-proofs proofs))
               (forced-proofs        (clause.prove-arbitrary-formulas-from-their-clauses
                                      fgoals
                                      (restn num-old-proofs proofs)))
               (proof1               (rw.crewrite-clause-plan-compiler plan world nil forced-proofs)))
          (cons proof1 cdr-old-goals-proofs))
      ;; We need to generate the first proof using an existing proof
      (let* ((proof1-seed          (car proofs))
             (cdr-old-goals-proofs (firstn num-old-proofs (cdr proofs)))
             (forced-proofs        (clause.prove-arbitrary-formulas-from-their-clauses
                                    fgoals
                                    (restn num-old-proofs (cdr proofs))))
             (proof1               (rw.crewrite-clause-plan-compiler plan world proof1-seed
                                                                     forced-proofs)))
          (cons proof1 cdr-old-goals-proofs)))))

(defobligations tactic.crewrite-first-compile
  (rw.crewrite-clause-plan-compiler
   clause.prove-arbitrary-formulas-from-their-clauses))

(encapsulate
 ()
 (local (in-theory (enable tactic.crewrite-first-okp
                           tactic.crewrite-first-compile)))

 (local (ACL2::allow-fertilize t))

 (verify-guards tactic.crewrite-first-compile
                :hints(("Goal" :do-not-induct t)))

 (defthm forcing-logic.appeal-listp-of-tactic.crewrite-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.crewrite-first-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.crewrite-first-compile x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.crewrite-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.crewrite-first-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.crewrite-first-compile x worlds proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.crewrite-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.crewrite-first-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.world-list-atblp worlds atbl)
                        (tactic.world-list-env-okp worlds axioms thms)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.crewrite-first-compile)))
            (equal (logic.proof-listp (tactic.crewrite-first-compile x worlds proofs) axioms thms atbl)
                   t))))

