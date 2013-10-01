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
(include-book "conditional-eqsubst")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund tactic.conditional-eqsubst-all-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'conditional-eqsubst-all)
         (tuplep 3 extras)
         (let ((hypterm    (first extras))
               (lhs        (second extras))
               (rhs        (third extras))
               (orig-goals (tactic.skeleton->goals history)))
           (and (logic.termp hypterm)
                (logic.termp lhs)
                (logic.termp rhs)
                (let ((correctness-of-subst (list (logic.function 'not (list hypterm))
                                                  (logic.function 'equal (list lhs rhs))))
                      (subst-is-applicable  (multicons hypterm orig-goals))
                      (post-subst-goals     (logic.replace-subterm-list-list orig-goals lhs rhs)))
                  (equal goals (cons correctness-of-subst
                                     (app subst-is-applicable post-subst-goals)))))))))

(defund tactic.conditional-eqsubst-all-env-okp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.conditional-eqsubst-all-okp x)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.conditional-eqsubst-all-okp)))))
  (let* ((extras  (tactic.skeleton->extras x))
         (hypterm (first extras))
         (lhs     (second extras))
         (rhs     (third extras)))
    (and (logic.term-atblp hypterm atbl)
         (logic.term-atblp lhs atbl)
         (logic.term-atblp rhs atbl))))

(defthm booleanp-of-tactic.conditional-eqsubst-all-okp
  (equal (booleanp (tactic.conditional-eqsubst-all-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.conditional-eqsubst-all-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm booleanp-of-tactic.conditional-eqsubst-all-env-okp
  (equal (booleanp (tactic.conditional-eqsubst-all-env-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.conditional-eqsubst-all-env-okp)
                                 ((:executable-counterpart acl2::force))))))


;; (local (defthm forcing-logic.term-list-listp-of-multicons
;;          (implies (force (and (logic.termp a)
;;                               (logic.term-list-listp x)))
;;                   (equal (logic.term-list-listp (multicons a x))
;;                          t))
;;          :hints(("Goal" :induct (cdr-induction x)))))

(local (defthm forcing-logic.term-list-list-atblp-of-multicons
         (implies (force (and (logic.term-atblp a atbl)
                              (logic.term-list-list-atblp x atbl)))
                  (equal (logic.term-list-list-atblp (multicons a x) atbl)
                         t))
         :hints(("Goal" :induct (cdr-induction x)))))




(defund tactic.conditional-eqsubst-all-tac (x hypterm lhs rhs warnp)
  ;; Replace occurrences of expr with var, a new variable
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.termp hypterm)
                              (logic.termp lhs)
                              (logic.termp rhs)
                              (booleanp warnp))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (and warnp
             (ACL2::cw "~s0Conditional-eqsubst-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*))
      (let* ((correctness-of-subst (list (logic.function 'not (list hypterm))
                                         (logic.function 'equal (list lhs rhs))))
             (subst-is-applicable  (multicons hypterm goals))
             (post-subst-goals     (logic.replace-subterm-list-list goals lhs rhs)))
        (tactic.extend-skeleton (cons correctness-of-subst (fast-app subst-is-applicable post-subst-goals))
                                'conditional-eqsubst-all
                                (list hypterm lhs rhs)
                                x)))))

(defthm forcing-tactic.skeletonp-of-tactic.conditional-eqsubst-all-tac
  (implies (and (tactic.conditional-eqsubst-all-tac x hypterm lhs rhs warnp)
                (force (logic.termp hypterm))
                (force (logic.termp lhs))
                (force (logic.termp rhs))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.conditional-eqsubst-all-tac x hypterm lhs rhs warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.conditional-eqsubst-all-tac))))

(defthm forcing-tactic.conditional-eqsubst-all-okp-of-tactic.conditional-eqsubst-all-tac
  (implies (and (tactic.conditional-eqsubst-all-tac x hypterm lhs rhs warnp)
                (force (logic.termp hypterm))
                (force (logic.termp lhs))
                (force (logic.termp rhs))
                (force (tactic.skeletonp x)))
           (equal (tactic.conditional-eqsubst-all-okp (tactic.conditional-eqsubst-all-tac x hypterm lhs rhs warnp))
                  t))
  :hints(("Goal" :in-theory (e/d (tactic.conditional-eqsubst-all-tac
                                  tactic.conditional-eqsubst-all-okp)))))

(defthm forcing-tactic.conditional-eqsubst-all-env-okp-of-tactic.conditional-eqsubst-all-tac
  (implies (and (tactic.conditional-eqsubst-all-tac x hypterm lhs rhs warnp)
                (force (logic.term-atblp hypterm atbl))
                (force (logic.term-atblp lhs atbl))
                (force (logic.term-atblp rhs atbl))
                (force (tactic.skeletonp x)))
           (equal (tactic.conditional-eqsubst-all-env-okp (tactic.conditional-eqsubst-all-tac x hypterm lhs rhs warnp) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.conditional-eqsubst-all-tac
                                    tactic.conditional-eqsubst-all-env-okp))))



(defund tactic.conditional-eqsubst-list-bldr (p orig-goals proof1 proofs2 proofs3 lhs rhs)
  (declare (xargs :guard (and (logic.formulap p)
                              (logic.term-list-listp orig-goals)
                              (cons-listp orig-goals)
                              (logic.appealp proof1)
                              (logic.appeal-listp proofs2)
                              (logic.appeal-listp proofs3)
                              (logic.termp lhs)
                              (logic.termp rhs)
                              (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                              (equal (logic.strip-conclusions proofs2)
                                     (logic.por-list (repeat (logic.pnot p) (len orig-goals))
                                                     (clause.clause-list-formulas orig-goals)))
                              (equal (logic.strip-conclusions proofs3)
                                     (clause.clause-list-formulas (logic.replace-subterm-list-list orig-goals lhs rhs))))))
  (if (consp orig-goals)
      (cons (tactic.conditional-eqsubst-bldr p (car orig-goals) proof1 (car proofs2) (car proofs3) lhs rhs)
            (tactic.conditional-eqsubst-list-bldr p (cdr orig-goals) proof1 (cdr proofs2) (cdr proofs3) lhs rhs))
    nil))

(defobligations tactic.conditional-eqsubst-list-bldr
  (tactic.conditional-eqsubst-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.conditional-eqsubst-list-bldr)))

 (defthm forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-list-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-list-listp orig-goals)
                        (cons-listp orig-goals)
                        (logic.appealp proof1)
                        (logic.appeal-listp proofs2)
                        (logic.appeal-listp proofs3)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                        (equal (logic.strip-conclusions proofs2)
                               (logic.por-list (repeat (logic.pnot p) (len orig-goals))
                                               (clause.clause-list-formulas orig-goals)))
                        (equal (logic.strip-conclusions proofs3)
                               (clause.clause-list-formulas (logic.replace-subterm-list-list orig-goals lhs rhs)))))
            (equal (logic.appeal-listp (tactic.conditional-eqsubst-list-bldr p orig-goals proof1 proofs2 proofs3 lhs rhs))
                   t))
   :hints(("Goal" :induct (cdr-cdr-cdr-induction orig-goals proofs2 proofs3))))

 (defthm forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-list-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-list-listp orig-goals)
                        (cons-listp orig-goals)
                        (logic.appealp proof1)
                        (logic.appeal-listp proofs2)
                        (logic.appeal-listp proofs3)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                        (equal (logic.strip-conclusions proofs2)
                               (logic.por-list (repeat (logic.pnot p) (len orig-goals))
                                               (clause.clause-list-formulas orig-goals)))
                        (equal (logic.strip-conclusions proofs3)
                               (clause.clause-list-formulas (logic.replace-subterm-list-list orig-goals lhs rhs)))))
            (equal (logic.strip-conclusions (tactic.conditional-eqsubst-list-bldr p orig-goals proof1 proofs2 proofs3 lhs rhs))
                   (clause.clause-list-formulas orig-goals)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-tactic.conditional-eqsubst-list-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-list-listp orig-goals)
                        (cons-listp orig-goals)
                        (logic.appealp proof1)
                        (logic.appeal-listp proofs2)
                        (logic.appeal-listp proofs3)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                        (equal (logic.strip-conclusions proofs2)
                               (logic.por-list (repeat (logic.pnot p) (len orig-goals))
                                               (clause.clause-list-formulas orig-goals)))
                        (equal (logic.strip-conclusions proofs3)
                               (clause.clause-list-formulas (logic.replace-subterm-list-list orig-goals lhs rhs)))
                        ;; ---
                        (logic.term-list-list-atblp orig-goals atbl)
                        (logic.proofp proof1 axioms thms atbl)
                        (logic.proof-listp proofs2 axioms thms atbl)
                        (logic.proof-listp proofs3 axioms thms atbl)
                        (@obligations tactic.conditional-eqsubst-list-bldr)))
            (equal (logic.proof-listp (tactic.conditional-eqsubst-list-bldr p orig-goals proof1 proofs2 proofs3 lhs rhs) axioms thms atbl)
                   t))))




(defund tactic.conditional-eqsubst-all-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.conditional-eqsubst-all-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras       (tactic.skeleton->extras x))
         (history      (tactic.skeleton->history x))
         (orig-goals   (tactic.skeleton->goals history))
         (hypterm      (first extras))
         (lhs          (second extras))
         (rhs          (third extras))
         (len          (len orig-goals)))
    (tactic.conditional-eqsubst-list-bldr (logic.pequal hypterm ''nil)
                                          orig-goals
                                          (tactic.conditional-eqsubst-lemma1 (car proofs))
                                          (firstn len (cdr proofs))
                                          (restn len (cdr proofs))
                                          lhs
                                          rhs)))

(defobligations tactic.conditional-eqsubst-all-compile
  (tactic.conditional-eqsubst-lemma1
   tactic.conditional-eqsubst-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.conditional-eqsubst-all-okp
                           tactic.conditional-eqsubst-all-env-okp
                           tactic.conditional-eqsubst-all-compile
                           logic.term-formula)))

 (local (defthm len-1-when-not-cdr
          (implies (not (cdr x))
                   (equal (equal (len x) 1)
                          (consp x)))
          :rule-classes ((:rewrite :backchain-limit-lst 0))))

 (local (defthm crock1
          (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                          (logic.strip-conclusions proofs))
                   (equal (logic.conclusion (first proofs))
                          (logic.disjoin-formulas (logic.term-list-formulas (car goals)))))))

 (local (defthm crock2
          (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                          (logic.strip-conclusions proofs))
                   (equal (logic.strip-conclusions (firstn n proofs))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas (firstn n goals)))))
          :hints(("Goal" :in-theory (enable firstn)))))

 (local (defthm crock3
          (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                          (logic.strip-conclusions proofs))
                   (equal (logic.strip-conclusions (restn n proofs))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas (restn n goals)))))
          :hints(("Goal" :in-theory (enable restn)))))

 (local (defthm crock4
          (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                          (logic.strip-conclusions proofs))
                   (equal (logic.strip-conclusions (firstn n (cdr proofs)))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas (firstn n (cdr goals))))))))

 (local (defthm crock5
          (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                          (logic.strip-conclusions proofs))
                   (equal (logic.strip-conclusions (restn n (cdr proofs)))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas (restn n (cdr goals))))))))

 (local (defthm crock6
          (implies (equal (app a b) x)
                   (equal (firstn (len a) x)
                          (list-fix a)))))

 (local (defthm crock7
          (implies (equal (app a b) x)
                   (equal (restn (len a) x)
                          (list-fix b)))))

 (local (defthm crock8
          (implies (equal (app a (app b c)) x)
                   (equal (firstn (len b) (restn (len a) x))
                          (list-fix b)))))

 (local (defthm crock9
          (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                          (logic.strip-conclusions proofs))
                   (equal (consp proofs)
                          (consp goals)))))

 (local (defthm crock10
          (implies (EQUAL (APP (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))) Y)
                          (CDR (TACTIC.SKELETON->GOALS X)))
                   (EQUAL (FIRSTN (LEN (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))
                                  (CDR (TACTIC.SKELETON->GOALS X)))
                          (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X))
                                     (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))))
          :hints(("Goal" :use ((:instance crock6
                                          (a (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))))
                                          (b y)
                                          (x (CDR (TACTIC.SKELETON->GOALS X)))))))))

 (local (defthm crock11
          (implies (EQUAL (APP (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))) Y)
                          (CDR (TACTIC.SKELETON->GOALS X)))
                   (EQUAL (RESTN (LEN (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))
                                 (CDR (TACTIC.SKELETON->GOALS X)))
                          (list-fix Y)))
          :hints(("Goal" :use ((:instance crock7
                                          (a (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))))
                                          (b y)
                                          (x (CDR (TACTIC.SKELETON->GOALS X)))))))))

 (local (defthm stupid
          (implies (cons-listp x)
                   (LOGIC.ALL-DISJUNCTIONSP (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (MULTICONS a x)))))
          :hints(("Goal" :induct (cdr-induction x)))))

 (local (defthm stupid2
          (implies (cons-listp x)
                   (equal (LOGIC.VLHSES (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (MULTICONS a x))))
                          (repeat (logic.term-formula a) (len x))))
          :hints(("Goal" :induct (cdr-induction x)))))

 (local (defthm stupid3
          (implies (cons-listp x)
                   (equal (LOGIC.VRHSES (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (MULTICONS a x))))
                          (logic.disjoin-each-formula-list (logic.term-list-list-formulas x))))
          :hints(("Goal" :induct (cdr-induction x)))))

 (defthm forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.conditional-eqsubst-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.conditional-eqsubst-all-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.conditional-eqsubst-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.conditional-eqsubst-all-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.conditional-eqsubst-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.conditional-eqsubst-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.conditional-eqsubst-all-env-okp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.conditional-eqsubst-all-compile)))
            (equal (logic.proof-listp (tactic.conditional-eqsubst-all-compile x proofs) axioms thms atbl)
                   t)))

 (verify-guards tactic.conditional-eqsubst-all-compile))


