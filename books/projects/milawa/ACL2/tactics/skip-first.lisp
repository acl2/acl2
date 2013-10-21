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
(include-book "../build/skip")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund tactic.skip-first-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'skip-first)
         (not extras)
         (let ((prev-goals (tactic.skeleton->goals history)))
           (and (consp prev-goals)
                (equal goals (cdr prev-goals)))))))

(defthm booleanp-of-tactic.skip-first-okp
  (equal (booleanp (tactic.skip-first-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.skip-first-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.skip-first-tac (x)
  ;; Replace occurrences of expr with var, a new variable
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0skip-first-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (tactic.extend-skeleton (cdr goals)
                              'skip-first
                              nil
                              x))))

(defthm forcing-tactic.skeletonp-of-tactic.skip-first-tac
  (implies (and (tactic.skip-first-tac x)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.skip-first-tac x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skip-first-tac))))

(defthm forcing-tactic.skip-first-okp-of-tactic.skip-first-tac
  (implies (and (tactic.skip-first-tac x)
                (force (tactic.skeletonp x)))
           (equal (tactic.skip-first-okp (tactic.skip-first-tac x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skip-first-tac tactic.skip-first-okp))))




(defund tactic.skip-first-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.skip-first-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history    (tactic.skeleton->history x))
         (prev-goals (tactic.skeleton->goals history)))
    (cons (build.skip (clause.clause-formula (first prev-goals))) proofs)))

(defobligations tactic.skip-first-compile
  (build.skip))

(encapsulate
 ()
 (local (in-theory (enable tactic.skip-first-okp tactic.skip-first-compile)))

 (verify-guards tactic.skip-first-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.skip-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.skip-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.skip-first-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.skip-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.skip-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.skip-first-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.skip-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.skip-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.skip-first-compile)))
            (equal (logic.proof-listp (tactic.skip-first-compile x proofs) axioms thms atbl)
                   t))))
