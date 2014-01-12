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


(defund tactic.cleanup-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'cleanup)
         (not extras)
         (let* ((old-goals   (tactic.skeleton->goals history))
                (cleanup     (clause.fast-clean-clauses old-goals))
                (unprovablep (first cleanup))
                (progressp   (second cleanup))
                (new-goals   (third cleanup)))
           (and (not unprovablep)
                progressp
                (equal goals new-goals))))))

(defthm booleanp-of-tactic.cleanup-okp
  (equal (booleanp (tactic.cleanup-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.cleanup-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.cleanup-tac (x warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (booleanp warnp))))
  (let* ((goals       (tactic.skeleton->goals x))
         (cleanup     (clause.fast-clean-clauses goals))
         (unprovablep (first cleanup))
         (progressp   (second cleanup))
         (new-goals   (third cleanup)))
    (cond (unprovablep
           ;; We print this out even if the warnings are off.
           (ACL2::cw "~s0Cleanup-tac failure~s1: unprovable clause discovered.~%" *red* *black*))
          ((not progressp)
           (and warnp
                (ACL2::cw "~s0Cleanup-tac failure~s1: the goal is already clean.~%" *red* *black*)))
          (t
           (tactic.extend-skeleton new-goals 'cleanup nil x)))))

(defthm forcing-tactic.skeletonp-of-tactic.cleanup-tac
  (implies (and (tactic.cleanup-tac x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.cleanup-tac x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cleanup-tac))))

(defthm forcing-tactic.cleanup-okp-of-tactic.cleanup-tac
  (implies (and (tactic.cleanup-tac x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.cleanup-okp (tactic.cleanup-tac x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cleanup-tac tactic.cleanup-okp))))




(defund tactic.cleanup-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.cleanup-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history   (tactic.skeleton->history x))
         (old-goals (tactic.skeleton->goals history)))
    (clause.clean-clauses-bldr old-goals proofs)))

(defobligations tactic.cleanup-compile
  (clause.clean-clauses-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.cleanup-okp tactic.cleanup-compile)))

 (verify-guards tactic.cleanup-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.cleanup-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.cleanup-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.cleanup-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.cleanup-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.cleanup-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.cleanup-compile x proofs))
                   (clause.clause-list-formulas
                    (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.cleanup-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.cleanup-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.cleanup-compile)
                        ))
            (equal (logic.proof-listp (tactic.cleanup-compile x proofs) axioms thms atbl)
                   t))))
