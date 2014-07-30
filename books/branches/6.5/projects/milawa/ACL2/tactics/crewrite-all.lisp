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
(include-book "worldp")
(include-book "crewrite-world")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(local (defthm logic.strip-conclusions-of-restn
         ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
         ;; belongs and try using it globally.
         (equal (logic.strip-conclusions (restn n x))
                (restn n (logic.strip-conclusions x)))))

(local (in-theory (disable restn-of-logic.strip-conclusions)))

(local (ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-restn)
                                                   (:rewrite restn-of-logic.strip-conclusions))))


(local (defthm logic.strip-conclusions-of-firstn
         ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
         ;; belongs and try using it globally.
         (equal (logic.strip-conclusions (firstn n x))
                (firstn n (logic.strip-conclusions x)))))

(local (in-theory (disable firstn-of-logic.strip-conclusions)))

(local (ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-firstn)
                                                   (:rewrite firstn-of-logic.strip-conclusions))))





(defund tactic.crewrite-all-okp (x worlds)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds))))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'crewrite-all)
         (tuplep 2 extras)
         (let* ((windex    (first extras))
                (plans     (second extras))
                (world     (tactic.find-world windex worlds))
                (old-goals (tactic.skeleton->goals history)))
           (and world
                (consp old-goals)
                (rw.crewrite-clause-plan-listp plans)
                (rw.crewrite-clause-plan-list-okp plans world)
                (rw.crewrite-clause-plan-list->progressp plans)
                (equal old-goals (rw.crewrite-clause-plan-list->clauses plans))
                (let* ((clauses-prime (rw.crewrite-clause-plan-list->clauses-prime plans))
                       (fgoals1       (rw.crewrite-clause-plan-list->forced-goals plans))
                       (fgoals        (remove-duplicates fgoals1))
                       (fclauses      (clause.make-clauses-from-arbitrary-formulas fgoals)))
                  (equal goals (fast-app clauses-prime fclauses))))))))

(defthm booleanp-of-tactic.crewrite-all-okp
  (equal (booleanp (tactic.crewrite-all-okp x worlds))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.crewrite-all-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.crewrite-all-tac (x theoryname fastp world warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.worldp world)
                              (booleanp warnp))))
  (let* ((goals      (tactic.skeleton->goals x))
         (findtheory (lookup theoryname (tactic.world->theories world)))
         (windex     (tactic.world->index world)))
    (cond ((not (consp goals))
           (and warnp
                (ACL2::cw "~s0crewrite-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*)))
          ((not findtheory)
           (and warnp
                (ACL2::cw "~s0crewrite-all-tac failure~s1: no theory named ~s2 is defined.~%" *red* *black* theoryname)))
          (t
           (let* ((plans         (rw.make-crewrite-clause-plan-list goals fastp theoryname world))
                  (progressp     (rw.crewrite-clause-plan-list->progressp plans)))
             (if (not progressp)
                 (and warnp
                      (ACL2::cw "~s0crewrite-all-tac failure~s1: no progress was made.~%" *red* *black*))
               (let* ((clauses-prime (rw.crewrite-clause-plan-list->clauses-prime plans))
                      (fgoals1       (rw.crewrite-clause-plan-list->forced-goals plans))
                      (fgoals        (remove-duplicates fgoals1))
                      (fg1-len       (fast-len fgoals1 0))
                      (fg-len        (fast-len fgoals 0))
                      (fclauses      (clause.make-clauses-from-arbitrary-formulas fgoals)))
                 (ACL2::prog2$
                  (ACL2::prog2$
                   (ACL2::cw! "; Rewrote ~x0 clauses; ~x1 (+ ~x2 forced) remain.~%"
                              (fast-len goals 0)
                              (fast-len clauses-prime 0)
                              fg-len)
                   (or (equal fg-len fg1-len)
                       (ACL2::cw! ";; global forced-duplicates elimination eats ~x0 goals.~%"
                                  (- fg1-len fg-len))))
                  (tactic.extend-skeleton (fast-app clauses-prime fclauses)
                                          'crewrite-all
                                          (list windex plans)
                                          x)))))))))

(defthm forcing-tactic.skeletonp-of-tactic.crewrite-all-tac
  (implies (and (tactic.crewrite-all-tac x theoryname fastp world warnp)
                (force (tactic.skeletonp x))
                (force (tactic.worldp world)))
           (equal (tactic.skeletonp (tactic.crewrite-all-tac x theoryname fastp world warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.crewrite-all-tac))))

(defthm forcing-tactic.crewrite-all-okp-of-tactic.crewrite-all-tac
  (implies (and (tactic.crewrite-all-tac x theoryname fastp world warnp)
                (force (tactic.worldp world))
                (force (tactic.world-listp worlds))
                (force (tactic.skeletonp x))
                (force (equal world (tactic.find-world (tactic.world->index world) worlds))))
           (equal (tactic.crewrite-all-okp
                   (tactic.crewrite-all-tac x theoryname fastp world warnp)
                   worlds)
                  t))
  :hints(("Goal" :in-theory (enable tactic.crewrite-all-tac
                                    tactic.crewrite-all-okp))))




(defund tactic.crewrite-all-compile (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (logic.appeal-listp proofs)
                              (tactic.crewrite-all-okp x worlds)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras               (tactic.skeleton->extras x))
         (windex               (first extras))
         (plans                (second extras))
         (world                (tactic.find-world windex worlds))
         (clauses-prime        (rw.crewrite-clause-plan-list->clauses-prime plans))
         (clauses-prime-len    (fast-len clauses-prime 0))
         (clauses-prime-proofs (firstn clauses-prime-len proofs))
         (forced-clause-proofs (restn clauses-prime-len proofs))
         (forced-goals         (remove-duplicates
                                (rw.crewrite-clause-plan-list->forced-goals plans)))
         (forced-goal-proofs   (clause.prove-arbitrary-formulas-from-their-clauses
                                forced-goals forced-clause-proofs)))
    (rw.crewrite-clause-plan-list-compiler plans world clauses-prime-proofs forced-goal-proofs)))

(defobligations tactic.crewrite-all-compile
  (rw.crewrite-clause-plan-list-compiler
   clause.prove-arbitrary-formulas-from-their-clauses))

(encapsulate
 ()
 (local (in-theory (enable tactic.crewrite-all-okp
                           tactic.crewrite-all-compile)))

 (local (ACL2::allow-fertilize t))

 (verify-guards tactic.crewrite-all-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.crewrite-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.crewrite-all-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.crewrite-all-compile x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.crewrite-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.crewrite-all-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.crewrite-all-compile x worlds proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.crewrite-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.crewrite-all-okp x worlds)
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
                        (@obligations tactic.crewrite-all-compile)))
            (equal (logic.proof-listp (tactic.crewrite-all-compile x worlds proofs) axioms thms atbl)
                   t))))

