; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "colors")
(include-book "skeletonp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Fertilize Tactic
;;
;; Suppose (not (equal x y)) is a member of the clause.  Then, we can think of
;; the clause as:
;;
;;    (implies (and (equal x y)
;;                  ...)
;;             ...)
;;
;; The fertilize tactic allows us to replace all occurrences of x with y (or
;; vice versa) throughout the entire clause.
;;
;; Why is this a sound thing to do?  Assume our input goal is L1 v ... v Ln, and
;; that we are replacing x with y.  So the user needs to prove:
;;
;;     L1/[x<-y] v ... v Ln[x<-y]
;;
;; We can give this proof to our disjoined replace subterm builder, along with
;; the propositional axiom x != y v x = y, to prove:
;;
;;     x != y v L1 v ... v Ln
;;
;; All we need to do now is also prove x = y v L1 v ... v Ln, then use cut and
;; contraction to conclude L1 v ... v Ln.
;;
;; To prove x = y v L1 v ... v Ln, notice that we either have,
;;
;;    (not (equal x y)) != nil, or
;;    (not (equal y x)) != nil,
;;
;; among our literals.  Either of these is interchangeable for x != y.  So,
;; begin with the propositional axiom:
;;
;;     x != y v x = y                        Propositional axiom
;;     (not (equal x y)) != nil v x = y      Trivial manipulation
;;     (L1 v ... v Ln) v x = y               Multi assoc expansion
;;     x = y v (L1 v ... v Ln)               Commute or
;;
;; This entire process has been pretty efficient.  The replacement step can be
;; expensive, but the other steps are all very cheap.

(local (defthm logic.term-listp-when-tuplep-2-of-logic.termps
         (implies (and (tuplep 2 x)
                       (logic.termp (first x))
                       (logic.termp (second x)))
                  (equal (logic.term-listp x)
                         t))
         :rule-classes ((:rewrite :backchain-limit-lst 1))))

(defund tactic.fertilize-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'fertilize)
         (tuplep 2 extras)
         (let ((target      (first extras))
               (replacement (second extras))
               (prev-goals  (tactic.skeleton->goals history)))
           (and (logic.termp target)
                (logic.termp replacement)
                (consp prev-goals)
                (let* ((original-goal (car prev-goals))
                       (other-goals   (cdr prev-goals))
                       (eq1           (logic.function 'equal (list target replacement)))
                       (eq2           (logic.function 'equal (list replacement target)))
                       (neq1          (logic.function 'not (list eq1)))
                       (neq2          (logic.function 'not (list eq2))))
                  (and (or (memberp neq1 original-goal)
                           (memberp neq2 original-goal))
                       (equal (car goals) (logic.replace-subterm-list original-goal target replacement))
                       (equal (cdr goals) other-goals))))))))

(defund tactic.fertilize-env-okp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.fertilize-okp x)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable tactic.fertilize-okp)))))
  (let* ((extras      (tactic.skeleton->extras x))
         (target      (first extras))
         (replacement (second extras)))
    (and (logic.term-atblp target atbl)
         (logic.term-atblp replacement atbl))))

(defthm booleanp-of-tactic.fertilize-okp
  (equal (booleanp (tactic.fertilize-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.fertilize-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm booleanp-of-tactic.fertilize-env-okp
  (equal (booleanp (tactic.fertilize-env-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.fertilize-env-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.fertilize-tac (x target replacement)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.termp target)
                              (logic.termp replacement))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0fertilize-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let* ((original-goal (car goals))
             (other-goals   (cdr goals))
             (eq1           (logic.function 'equal (list target replacement)))
             (eq2           (logic.function 'equal (list replacement target)))
             (neq1          (logic.function 'not (list eq1)))
             (neq2          (logic.function 'not (list eq2))))
        (cond ((and (not (memberp neq1 original-goal))
                    (not (memberp neq2 original-goal)))
               (ACL2::cw "~s0fertilize-tac failure~s1: the proposed equality was not found in the clause.~%" *red* *black*))
              (t
               (tactic.extend-skeleton (cons (logic.replace-subterm-list original-goal target replacement)
                                             other-goals)
                                       'fertilize
                                       (list target replacement)
                                       x)))))))

(defthm forcing-tactic.skeletonp-of-tactic.fertilize-tac
  (implies (and (tactic.fertilize-tac x target replacement)
                (force (logic.termp target))
                (force (logic.termp replacement))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.fertilize-tac x target replacement))
                  t))
  :hints(("Goal" :in-theory (enable tactic.fertilize-tac))))

(defthm forcing-tactic.fertilize-okp-of-tactic.fertilize-tac
  (implies (and (tactic.fertilize-tac x target replacement)
                (force (logic.termp target))
                (force (logic.termp replacement))
                (force (tactic.skeletonp x)))
           (equal (tactic.fertilize-okp (tactic.fertilize-tac x target replacement))
                  t))
  :hints(("Goal" :in-theory (enable tactic.fertilize-tac
                                    tactic.fertilize-okp))))

(defthm forcing-tactic.fertilize-env-okp-of-tactic.fertilize-tac
  (implies (and (tactic.fertilize-tac x target replacement)
                (force (logic.term-atblp target atbl))
                (force (logic.term-atblp replacement atbl))
                (force (tactic.skeletonp x)))
           (equal (tactic.fertilize-env-okp (tactic.fertilize-tac x target replacement) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.fertilize-tac
                                    tactic.fertilize-env-okp))))





(deftheorem tactic.fertilize-lemma1-helper
  :derive (v (!= (not (equal x y)) nil) (= x y))
  :proof (@derive
          ((v (!= x y) (= x y))                    (build.propositional-schema (@formula (= x y))))
          ((v (= x y) (!= x y))                    (build.commute-or @-))
          ((v (= x y) (= (equal x y) nil))         (build.disjoined-not-equal-from-not-pequal @-))
          ((v (= x y) (!= (not (equal x y)) nil))  (build.disjoined-negative-lit-from-pequal-nil @-))
          ((v (!= (not (equal x y)) nil) (= x y))  (build.commute-or @-)))
  :minatbl ((equal . 2)
            (not . 1)))

(defund@ tactic.fertilize-lemma1 (original-goal lhs rhs)
  (declare (xargs :guard (and (logic.term-listp original-goal)
                              (logic.termp lhs)
                              (logic.termp rhs)
                              (memberp (logic.function 'not (list (logic.function 'equal (list lhs rhs)))) original-goal))
                  :verify-guards nil))
  (@derive
   ((v (!= (not (equal x y)) nil) (= x y))            (build.theorem (tactic.fertilize-lemma1-helper)))
   ((v (!= (not (equal lhs rhs)) nil) (= lhs rhs))    (build.instantiation @- (list (cons 'x lhs) (cons 'y rhs))))
   ((v original-goal (= lhs rhs))                     (build.multi-assoc-expansion @- (logic.term-list-formulas original-goal)))))

(defobligations tactic.fertilize-lemma1
  (build.multi-assoc-expansion
   build.instantiation)
  :extra-thms ((tactic.fertilize-lemma1-helper)))

(encapsulate
 ()
 (local (in-theory (enable tactic.fertilize-lemma1-helper tactic.fertilize-lemma1)))

 (verify-guards tactic.fertilize-lemma1)

 (defthm tactic.fertilize-lemma1-under-iff
   (iff (tactic.fertilize-lemma1 original-goal lhs rhs)
        t))

 (defthm forcing-logic.appealp-of-tactic.fertilize-lemma1
   (implies (force (and (logic.term-listp original-goal)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (memberp (logic.function 'not (list (logic.function 'equal (list lhs rhs)))) original-goal)))
            (equal (logic.appealp (tactic.fertilize-lemma1 original-goal lhs rhs))
                   t)))

 (defthm forcing-logic.conclusion-of-tactic.fertilize-lemma1
   (implies (force (and (logic.term-listp original-goal)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (memberp (logic.function 'not (list (logic.function 'equal (list lhs rhs)))) original-goal)))
            (equal (logic.conclusion (tactic.fertilize-lemma1 original-goal lhs rhs))
                   (logic.por (clause.clause-formula original-goal)
                              (logic.pequal lhs rhs)))))

 (defthm@ forcing-logic.proofp-of-tactic.fertilize-lemma1
   (implies (force (and (logic.term-listp original-goal)
                        (logic.termp lhs)
                        (logic.termp rhs)
                        (memberp (logic.function 'not (list (logic.function 'equal (list lhs rhs)))) original-goal)
                        ;; ---
                        (logic.term-list-atblp original-goal atbl)
                        (logic.term-atblp lhs atbl)
                        (logic.term-atblp rhs atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations tactic.fertilize-lemma1)))
            (equal (logic.proofp (tactic.fertilize-lemma1 original-goal lhs rhs) axioms thms atbl)
                   t))))







;; Why is this a sound thing to do?  Assume our input goal is L1 v ... v Ln, and
;; that we are replacing x with y.  So the user needs to prove:
;;
;;     L1/[x<-y] v ... v Ln[x<-y]
;;
;; We can give this proof to our disjoined replace subterm builder, along with
;; the propositional axiom x != y v x = y, to prove:
;;
;;     x != y v L1 v ... v Ln
;;
;; All we need to do now is also prove x = y v L1 v ... v Ln, then use cut and
;; contraction to conclude L1 v ... v Ln.
;;
;; To prove x = y v L1 v ... v Ln, notice that we either have,
;;
;;    (not (equal x y)) != nil, or
;;    (not (equal y x)) != nil,
;;
;; among our literals.  Either of these is interchangeable for x != y.  So,
;; begin with the propositional axiom:
;;
;;     x != y v x = y                        Propositional axiom
;;     (not (equal x y)) != nil v x = y      Trivial manipulation
;;     (L1 v ... v Ln) v x = y               Multi assoc expansion
;;     x = y v (L1 v ... v Ln)               Commute or

(defund tactic.fertilize-bldr (target replacement orig-goal proof)
  (declare (xargs :guard (and (logic.termp target)
                              (logic.termp replacement)
                              (logic.term-listp orig-goal)
                              (or (memberp (logic.function 'not (list (logic.function 'equal (list target replacement)))) orig-goal)
                                  (memberp (logic.function 'not (list (logic.function 'equal (list replacement target)))) orig-goal))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (logic.replace-subterm-list orig-goal target replacement))))))
  (let* (;; target != replacement v target = replacement
         (line-1 (build.propositional-schema (logic.pequal target replacement)))
         ;; target != replacement v L1 = L1[target<-replacement]; ...; target != replacement v Ln = Ln[target<-replacement]
         (line-2 (build.disjoined-replace-subterm-list orig-goal target replacement line-1))
         ;; target != replacement v L1[target<-replacement] v ... v Ln[target<-replacement]
         (line-3 (build.expansion (logic.pnot (logic.pequal target replacement)) proof))
         ;; target != replacement v L1 v ... v Ln
         (line-4 (clause.disjoined-update-clause-bldr (logic.replace-subterm-list orig-goal target replacement) line-3 line-2))
         ;; target = replacement v L1 v ... v Ln
         (line-5 (if (memberp (logic.function 'not (list (logic.function 'equal (list target replacement)))) orig-goal)
                     (let* (;; (L1 v ... v Ln) v target = replacement
                            (crock-1 (tactic.fertilize-lemma1 orig-goal target replacement))
                            ;; target = replacement v L1 v ... v Ln
                            (crock-2 (build.commute-or crock-1)))
                       crock-2)
                   (let* (;; (L1 v ... v Ln) v replacement = target
                          (crock-1 (tactic.fertilize-lemma1 orig-goal replacement target))
                          ;; (L1 v ... v Ln) v target = replacement
                          (crock-2 (build.disjoined-commute-pequal crock-1))
                          ;; target = replacement v L1 v ... v Ln
                          (crock-3 (build.commute-or crock-2)))
                     crock-3)))
         ;; (L1 v ... v Ln) v (L1 v ... v Ln)
         (line-6 (build.cut line-5 line-4))
         ;; L1 v ... v Ln
         (line-7 (build.contraction line-6)))
    line-7))

(defobligations tactic.fertilize-bldr
  (build.propositional-schema
   build.disjoined-replace-subterm-list
   build.expansion
   clause.disjoined-update-clause-bldr
   tactic.fertilize-lemma1
   build.commute-or
   build.disjoined-commute-pequal
   build.cut
   build.contraction))

(encapsulate
 ()
 (local (in-theory (enable tactic.fertilize-bldr)))

 (defthm tactic.fertilize-bldr-under-iff
   (iff (tactic.fertilize-bldr target replacement orig-goal proof)
        t))

 (defthm forcing-logic.appealp-of-tactic.fertilize-bldr
   (implies (force (and (logic.termp target)
                        (logic.termp replacement)
                        (logic.term-listp orig-goal)
                        (or (memberp (logic.function 'not (list (logic.function 'equal (list target replacement)))) orig-goal)
                            (memberp (logic.function 'not (list (logic.function 'equal (list replacement target)))) orig-goal))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (logic.replace-subterm-list orig-goal target replacement)))))
            (equal (logic.appealp (tactic.fertilize-bldr target replacement orig-goal proof))
                   t)))

 (defthm forcing-logic.conclusion-of-tactic.fertilize-bldr
   (implies (force (and (logic.termp target)
                        (logic.termp replacement)
                        (logic.term-listp orig-goal)
                        (or (memberp (logic.function 'not (list (logic.function 'equal (list target replacement)))) orig-goal)
                            (memberp (logic.function 'not (list (logic.function 'equal (list replacement target)))) orig-goal))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (logic.replace-subterm-list orig-goal target replacement)))))
            (equal (logic.conclusion (tactic.fertilize-bldr target replacement orig-goal proof))
                   (clause.clause-formula orig-goal)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-tactic.fertilize-bldr
   (implies (force (and (logic.termp target)
                        (logic.termp replacement)
                        (logic.term-listp orig-goal)
                        (or (memberp (logic.function 'not (list (logic.function 'equal (list target replacement)))) orig-goal)
                            (memberp (logic.function 'not (list (logic.function 'equal (list replacement target)))) orig-goal))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (logic.replace-subterm-list orig-goal target replacement)))
                        ;; ---
                        (logic.term-list-atblp orig-goal atbl)
                        (logic.term-atblp target atbl)
                        (logic.term-atblp replacement atbl)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations tactic.fertilize-bldr)))
            (equal (logic.proofp (tactic.fertilize-bldr target replacement orig-goal proof) axioms thms atbl)
                   t))))




(defund tactic.fertilize-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.fertilize-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras       (tactic.skeleton->extras x))
         (history      (tactic.skeleton->history x))
         (orig-goal    (car (tactic.skeleton->goals history)))
         (target       (first extras))
         (replacement  (second extras)))
    (cons (tactic.fertilize-bldr target
                                 replacement
                                 orig-goal
                                 (first proofs))
          (cdr proofs))))

(defobligations tactic.fertilize-compile
  (tactic.fertilize-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.fertilize-okp
                           tactic.fertilize-env-okp
                           tactic.fertilize-compile
                           logic.term-formula)))

 (local (defthm crock
          (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
                   (equal (logic.conclusion (first proofs))
                          (clause.clause-formula (first goals))))))

 (verify-guards tactic.fertilize-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.fertilize-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.fertilize-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.fertilize-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.fertilize-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.fertilize-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.fertilize-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.fertilize-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.fertilize-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (tactic.fertilize-env-okp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations tactic.fertilize-compile)))
            (equal (logic.proof-listp (tactic.fertilize-compile x proofs) axioms thms atbl)
                   t))))

