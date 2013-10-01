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



;; Conditional Equal Substitution Tactic
;;
;; This tactic allows you to use a conditional equality to split a goal into
;; three goals.  Given an alleged equality of the form:
;;
;;    hypterm -> (equal lhs rhs)
;;
;; We split the current goal, L1 v ... v Ln, into three new subgoals:
;;
;;    (1) (not hypterm) v (equal lhs rhs)      "correctness of substitution"
;;    (2) hypterm v L1 v ... v Ln              "applicability of substitution"
;;    (3) L1/[lhs<-rhs] v ... v Ln[lhs<-rhs]   "post substitution goal"
;;
;; Why is this a sound thing to do?
;;
;;   a. From the proof of (1), we can prove the following for each Li (by the
;;      disjoined replace subterm builder):
;;
;;          (not hypterm) v Li = Li/[lhs<-rhs]
;;
;;   b. From the proof of (3), we can prove (using simple expansion):
;;
;;          (not hypterm) v L1/[lhs<-rhs] v ... v Ln/[lhs<-rhs]
;;
;;   c. From a and b, we can prove (by the disjoined update clause builder):
;;
;;          (not hypterm) v L1 v ... v Ln
;;
;;   d. From c and the proof of (2), we can prove (using cut and contraction):
;;
;;          L1 v ... v Ln
;;
;; Which was our original goal, and hence what we needed to prove.  Together
;; with generalization, this tactic allows us to implement destructor
;; elimination.  For example, suppose we want to prove:
;;
;;   (implies (and (consp x)
;;                 (foo (car x))
;;                 (bar (cdr x)))
;;            (baz x y))
;;
;; Then we will invoke the equal substitution tactic using:
;;
;;    hypterm = (consp x)
;;    lhs     = x
;;    rhs     = (cons (car x) (cdr x))
;;
;; This generates three new goals.  First, to defend the correctness of our
;; substitution, we need to show:
;;
;;    (1) (implies (consp x) (equal x (cons (car x) (cdr x))))
;;
;; This ought to be trivial using the axioms about conses.  Next, we need to
;; show that the substitution is applicable to the current goal.  This is the
;; following implication:
;;
;;    (2) (implies (and (not (consp x))
;;                      (consp x)
;;                      (foo (car x))
;;                      (bar (cdr x)))
;;                 (baz x y))
;;
;; Obviously that's easy to prove since we now have contradictory hyps.  But
;; if (consp x) wasn't one of our assumptions to begin with, we might have had
;; to do some work to prove it.  Finally, we have the more interesting subgoal:
;;
;;    (3) (implies (and (consp (cons (car x) (cdr x)))
;;                      (foo (car (cons (car x) (cdr x))))
;;                      (bar (cdr (cons (car x) (cdr x)))))
;;                 (baz (cons (car x) (cdr x)) y))
;;
;; At this point, (car x) and (cdr x) would need to be generalized, giving us:
;;
;;   (3') (implies (and (consp (cons x1 x2))
;;                      (foo (car (cons x1 x2)))
;;                      (bar (cdr (cons x1 x2))))
;;                 (baz (cons x1 x2) y))
;;
;; And now simple unconditional rewriting should immediately yield:
;;
;;  (3'') (implies (and (foo x1)
;;                      (bar x2))
;;                 (baz (cons x1 x2) y))
;;
;; Which is what I'd expect from car-cdr-elim.

(defund tactic.conditional-eqsubst-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'conditional-eqsubst)
         (tuplep 3 extras)
         (let ((hypterm    (first extras))
               (lhs        (second extras))
               (rhs        (third extras))
               (prev-goals (tactic.skeleton->goals history)))
           (and (logic.termp hypterm)
                (logic.termp lhs)
                (logic.termp rhs)
                (consp prev-goals)
                (let ((new-goal1     (first goals))
                      (new-goal2     (second goals))
                      (new-goal3     (third goals))
                      (other-goals   (cdr (cdr (cdr goals))))
                      (original-goal (car prev-goals)))
                  (and (equal new-goal1 (list (logic.function 'not (list hypterm))
                                              (logic.function 'equal (list lhs rhs))))
                       (equal new-goal2 (cons hypterm original-goal))
                       (equal new-goal3 (logic.replace-subterm-list original-goal lhs rhs))
                       (equal other-goals (cdr prev-goals)))))))))

(defund tactic.conditional-eqsubst-env-okp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.conditional-eqsubst-okp x)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.conditional-eqsubst-okp)))))
  (let* ((extras  (tactic.skeleton->extras x))
         (hypterm (first extras))
         (lhs     (second extras))
         (rhs     (third extras)))
    (and (logic.term-atblp hypterm atbl)
         (logic.term-atblp lhs atbl)
         (logic.term-atblp rhs atbl))))

(defthm booleanp-of-tactic.conditional-eqsubst-okp
  (equal (booleanp (tactic.conditional-eqsubst-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.conditional-eqsubst-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm booleanp-of-tactic.conditional-eqsubst-env-okp
  (equal (booleanp (tactic.conditional-eqsubst-env-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.conditional-eqsubst-env-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.conditional-eqsubst-tac (x hypterm lhs rhs)
  ;; Replace occurrences of expr with var, a new variable
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.termp hypterm)
                              (logic.termp lhs)
                              (logic.termp rhs))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0Conditional-eqsubst-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let* ((original-goal (car goals))
             (new-goal1     (list (logic.function 'not (list hypterm))
                                  (logic.function 'equal (list lhs rhs))))
             (new-goal2     (cons hypterm original-goal))
             (new-goal3     (logic.replace-subterm-list original-goal lhs rhs)))
        (tactic.extend-skeleton (cons new-goal1 (cons new-goal2 (cons new-goal3 (cdr goals))))
                                'conditional-eqsubst
                                (list hypterm lhs rhs)
                                x)))))

(defthm forcing-tactic.skeletonp-of-tactic.conditional-eqsubst-tac
  (implies (and (tactic.conditional-eqsubst-tac x hypterm lhs rhs)
                (force (logic.termp hypterm))
                (force (logic.termp lhs))
                (force (logic.termp rhs))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.conditional-eqsubst-tac x hypterm lhs rhs))
                  t))
  :hints(("Goal" :in-theory (enable tactic.conditional-eqsubst-tac))))

(defthm forcing-tactic.conditional-eqsubst-okp-of-tactic.conditional-eqsubst-tac
  (implies (and (tactic.conditional-eqsubst-tac x hypterm lhs rhs)
                (force (logic.termp hypterm))
                (force (logic.termp lhs))
                (force (logic.termp rhs))
                (force (tactic.skeletonp x)))
           (equal (tactic.conditional-eqsubst-okp (tactic.conditional-eqsubst-tac x hypterm lhs rhs))
                  t))
  :hints(("Goal" :in-theory (enable tactic.conditional-eqsubst-tac
                                    tactic.conditional-eqsubst-okp))))

(defthm forcing-tactic.conditional-eqsubst-env-okp-of-tactic.conditional-eqsubst-tac
  (implies (and (tactic.conditional-eqsubst-tac x hypterm lhs rhs)
                (force (logic.term-atblp hypterm atbl))
                (force (logic.term-atblp lhs atbl))
                (force (logic.term-atblp rhs atbl))
                (force (tactic.skeletonp x)))
           (equal (tactic.conditional-eqsubst-env-okp (tactic.conditional-eqsubst-tac x hypterm lhs rhs) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.conditional-eqsubst-tac
                                    tactic.conditional-eqsubst-env-okp))))





;; Why is this a sound thing to do?
;;
;;   a. From the proof of (1), we can prove the following for each Li (by the
;;      disjoined replace subterm builder):
;;
;;          (not hypterm) v Li = Li/[lhs<-rhs]
;;
;;   b. From the proof of (3), we can prove (using simple expansion):
;;
;;          (not hypterm) v L1/[lhs<-rhs] v ... v Ln/[lhs<-rhs]
;;
;;   c. From a and b, we can prove (by the disjoined update clause builder):
;;
;;          (not hypterm) v L1 v ... v Ln
;;
;;   d. From c and the proof of (2), we can prove (using cut and contraction):
;;
;;          L1 v ... v Ln

(defderiv tactic.conditional-eqsubst-lemma1
  :derive (v (= (? hyp) nil) (= (? a) (? b)))
  :from   ((proof x (v (!= (not (? hyp)) nil) (!= (equal (? a) (? b)) nil))))
  :proof  (@derive
           ((v (!= (not (? hyp)) nil) (!= (equal (? a) (? b)) nil))   (@given x))
           ((v (!= (not (? hyp)) nil) (= (equal (? a) (? b)) t))      (build.disjoined-equal-t-from-not-nil @-))
           ((v (!= (not (? hyp)) nil) (= (? a) (? b)))                (build.disjoined-pequal-from-equal @-))
           ((v (= (? a) (? b)) (!= (not (? hyp)) nil))                (build.commute-or @-))
           ((v (= (? a) (? b)) (= (? hyp) nil))                       (build.disjoined-pequal-nil-from-negative-lit @-))
           ((v (= (? hyp) nil) (= (? a) (? b)))                       (build.commute-or @-))))

(defund tactic.conditional-eqsubst-bldr (p orig-goal proof1 proof2 proof3 lhs rhs)
  (declare (xargs :guard (and (logic.formulap p)
                              (logic.term-listp orig-goal)
                              (consp orig-goal)
                              (logic.appealp proof1)
                              (logic.appealp proof2)
                              (logic.appealp proof3)
                              (logic.termp lhs)
                              (logic.termp rhs)
                              (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                              (equal (logic.conclusion proof2) (logic.por (logic.pnot p) (clause.clause-formula orig-goal)))
                              (equal (logic.conclusion proof3) (clause.clause-formula (logic.replace-subterm-list orig-goal lhs rhs))))))


  (let* (;; P v L1 = L1/[lhs<-rhs]; ...; P v Ln = Ln/[lhs<-rhs]
         (line-1 (build.disjoined-replace-subterm-list orig-goal lhs rhs proof1))
         ;; P v L1/[lhs<-rhs] v ... v Ln/[lhs<-rhs]
         (line-2 (build.expansion P proof3))
         ;; P v L1 v ... v Ln
         (line-3 (clause.disjoined-update-clause-bldr (logic.replace-subterm-list orig-goal lhs rhs) line-2 line-1))
         ;; (L1 v ... v Ln) v (L1 v ... v Ln)
         (line-4 (build.cut line-3 proof2))
         ;; (L1 v ... v Ln)
         (line-5 (build.contraction line-4)))
    line-5))

(defobligations tactic.conditional-eqsubst-bldr
  (build.disjoined-replace-subterm-list
   build.expansion
   clause.disjoined-update-clause-bldr
   build.cut
   build.contraction))

(encapsulate
 ()
 (local (in-theory (enable tactic.conditional-eqsubst-bldr)))

 (defthm tactic.conditional-eqsubst-bldr-under-iff
   (iff (tactic.conditional-eqsubst-bldr p orig-goal proof1 proof2 proof3 lhs rhs)
        t))

 (defthm forcing-logic.appealp-of-tactic.conditional-eqsubst-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-listp orig-goal)
                        (consp orig-goal)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (logic.appealp proof3)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                        (equal (logic.conclusion proof2) (logic.por (logic.pnot p) (clause.clause-formula orig-goal)))
                        (equal (logic.conclusion proof3) (clause.clause-formula (logic.replace-subterm-list orig-goal lhs rhs)))))
            (equal (logic.appealp (tactic.conditional-eqsubst-bldr p orig-goal proof1 proof2 proof3 lhs rhs))
                   t)))

 (defthm forcing-logic.conclusion-of-tactic.conditional-eqsubst-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-listp orig-goal)
                        (consp orig-goal)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (logic.appealp proof3)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                        (equal (logic.conclusion proof2) (logic.por (logic.pnot p) (clause.clause-formula orig-goal)))
                        (equal (logic.conclusion proof3) (clause.clause-formula (logic.replace-subterm-list orig-goal lhs rhs)))))
            (equal (logic.conclusion (tactic.conditional-eqsubst-bldr p orig-goal proof1 proof2 proof3 lhs rhs))
                   (clause.clause-formula orig-goal)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-tactic.conditional-eqsubst-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-listp orig-goal)
                        (consp orig-goal)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (logic.appealp proof3)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (equal (logic.conclusion proof1) (logic.por p (logic.pequal lhs rhs)))
                        (equal (logic.conclusion proof2) (logic.por (logic.pnot p) (clause.clause-formula orig-goal)))
                        (equal (logic.conclusion proof3) (clause.clause-formula (logic.replace-subterm-list orig-goal lhs rhs)))
                        ;; ---
                        (logic.term-list-atblp orig-goal atbl)
                        (logic.proofp proof1 axioms thms atbl)
                        (logic.proofp proof2 axioms thms atbl)
                        (logic.proofp proof3 axioms thms atbl)
                        (@obligations tactic.conditional-eqsubst-bldr)))
            (equal (logic.proofp (tactic.conditional-eqsubst-bldr p orig-goal proof1 proof2 proof3 lhs rhs) axioms thms atbl)
                   t))))



(defund tactic.conditional-eqsubst-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.conditional-eqsubst-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras       (tactic.skeleton->extras x))
         (history      (tactic.skeleton->history x))
         (orig-goal    (car (tactic.skeleton->goals history)))
         (hypterm      (first extras))
         (lhs          (second extras))
         (rhs          (third extras)))
    (cons (tactic.conditional-eqsubst-bldr (logic.pequal hypterm ''nil)
                                           orig-goal
                                           (tactic.conditional-eqsubst-lemma1 (first proofs))
                                           (second proofs)
                                           (third proofs)
                                           lhs rhs)
          (cdr (cdr (cdr proofs))))))

(defobligations tactic.conditional-eqsubst-compile
  (tactic.conditional-eqsubst-lemma1
   tactic.conditional-eqsubst-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.conditional-eqsubst-okp
                           tactic.conditional-eqsubst-env-okp
                           tactic.conditional-eqsubst-compile
                           logic.term-formula)))

 (local (defthm crock
          (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
                   (equal (logic.conclusion (first proofs))
                          (clause.clause-formula (first goals))))))

 (local (defthm crock2
          (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
                   (equal (logic.conclusion (second proofs))
                          (clause.clause-formula (second goals))))))

 (local (defthm crock3
          (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
                   (equal (logic.conclusion (third proofs))
                          (clause.clause-formula (third goals))))))

 (local (defthm len-1-when-not-cdr
          (implies (not (cdr x))
                   (equal (equal (len x) 1)
                          (consp x)))
          :rule-classes ((:rewrite :backchain-limit-lst 0))))

 (verify-guards tactic.conditional-eqsubst-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.conditional-eqsubst-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.conditional-eqsubst-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.conditional-eqsubst-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.conditional-eqsubst-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.conditional-eqsubst-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.conditional-eqsubst-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.conditional-eqsubst-env-okp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.conditional-eqsubst-compile)))
            (equal (logic.proof-listp (tactic.conditional-eqsubst-compile x proofs) axioms thms atbl)
                   t))))
