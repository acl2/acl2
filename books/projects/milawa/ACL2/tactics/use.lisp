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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund tactic.use-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'use)
         (logic.appealp extras)
         (let ((old-goals (tactic.skeleton->goals history)))
           (and (consp old-goals)
                (let* ((clause1    (car old-goals))
                       (conclterm  (logic.compile-formula (logic.conclusion extras)))
                       ;; The proof should be valid, so its conclusion should be true.
                       ;; So (not conclterm) should be a "false" term
                       ;; And it's always sound to add a false term to a disjunction.
                       (new-clause1 (cons (logic.function 'not (list conclterm)) clause1)))
                  (and (consp goals)
                       (equal (car goals) new-clause1)
                       (equal (cdr goals) (cdr old-goals)))))))))

(defthm booleanp-of-tactic.use-okp
  (equal (booleanp (tactic.use-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.use-okp)
                                 ((:executable-counterpart acl2::force))))))

(defund tactic.use-env-okp (x axioms thms atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.use-okp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.use-okp)))))
  (let* ((extras (tactic.skeleton->extras x)))
    ;; bozo what about later with extended proof checkers?
    (logic.proofp extras axioms thms atbl)))

(defthm booleanp-of-tactic.use-env-okp
  (equal (booleanp (tactic.use-env-okp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable tactic.use-env-okp))))



(defund tactic.use-tac (x proof)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.appealp proof))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0use-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let* ((clause1       (car goals))
             (conclterm     (logic.compile-formula (logic.conclusion proof)))
             (new-clause1   (cons (logic.function 'not (list conclterm)) clause1)))
        (tactic.extend-skeleton (cons new-clause1 (cdr goals)) 'use proof x)))))

(defthm forcing-tactic.skeletonp-of-tactic.use-tac
  (implies (and (tactic.use-tac x proof)
                (force (tactic.skeletonp x))
                (force (logic.appealp proof)))
           (equal (tactic.skeletonp (tactic.use-tac x proof))
                  t))
  :hints(("Goal" :in-theory (enable tactic.use-tac))))

(defthm forcing-tactic.use-okp-of-tactic.use-tac
  (implies (and (tactic.use-tac x proof)
                (force (tactic.skeletonp x))
                (force (logic.appealp proof)))
           (equal (tactic.use-okp (tactic.use-tac x proof))
                  t))
  :hints(("Goal" :in-theory (enable tactic.use-tac tactic.use-okp))))

(defthm forcing-tactic.use-env-okp-of-tactic.use-tac
  (implies (and (tactic.use-tac x proof)
                (force (tactic.skeletonp x))
                (force (logic.appealp proof))
                (force (logic.proofp proof axioms thms atbl)))
           (equal (tactic.use-env-okp (tactic.use-tac x proof) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.use-tac tactic.use-env-okp))))




(defund@ tactic.use-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.use-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((proof (tactic.skeleton->extras x))
         (cform (logic.conclusion proof)))
    (cons (@derive
           ((v (! cform) (= cterm t))         (@given (first (build.compile-formula cform))))
           ((v (! cform) (!= cterm nil))      (build.disjoined-not-nil-from-t @-))
           (cform                             (@given proof))
           ((!= cterm nil)                    (build.modus-ponens @- @--))
           ((= (not cterm) nil)               (build.negative-lit-from-not-pequal-nil @-))
           ((v (!= (not cterm) nil) clause1)  (@given (car proofs)))
           (clause1                           (build.modus-ponens @-- @-)))
          (cdr proofs))))

(defobligations tactic.use-compile
  (build.compile-formula
   build.modus-ponens
   build.negative-lit-from-not-pequal-nil))


(encapsulate
 ()
 (local (in-theory (enable tactic.use-okp
                           tactic.use-env-okp
                           tactic.use-compile
                           logic.term-formula)))

 (local (defthm crock
          (implies (and (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (TACTIC.SKELETON->GOALS X)))
                               (LOGIC.STRIP-CONCLUSIONS PROOFS))
                        (force (tactic.skeletonp x))
                        (force (consp proofs)))
                   (equal (logic.conclusion (first proofs))
                          (logic.disjoin-formulas
                           (logic.term-list-formulas (first (tactic.skeleton->goals x))))))))

 (verify-guards tactic.use-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.use-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.use-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.use-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.use-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.use-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.use-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.use-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.use-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.use-env-okp x axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.use-compile)))
            (equal (logic.proof-listp (tactic.use-compile x proofs) axioms thms atbl)
                   t))))
