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
(include-book "rewrite-world") ;; for tactic.world->control, etc.
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)





;; BOZO move us

(defthm nth-of-cons-when-constantp
  (implies (syntaxp (acl2::quotep n))
           (equal (nth n (cons a x))
                  (if (zp n)
                      a
                    (nth (- n 1) x))))
  :hints(("Goal" :expand (nth n (cons a x)))))

(defthm rw.crewrite-clause-aux-of-nil
  (equal (rw.crewrite-clause-aux nil done blimit rlimit control n acc)
         acc)
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-aux))))

(defthm rw.crewrite-clause-of-nil
  (equal (rw.crewrite-clause nil blimit rlimit control n)
         nil)
  :hints(("Goal" :in-theory (enable rw.crewrite-clause))))

(defthm tactic.world->index-under-iff
  (implies (force (tactic.worldp x))
           (iff (tactic.world->index x)
                t))
  :hints(("Goal"
          :in-theory (disable forcing-natp-of-tactic.world->index)
          :use ((:instance forcing-natp-of-tactic.world->index)))))

(defthm tactic.find-world-of-nil
  (implies (force (tactic.world-listp worlds))
           (equal (tactic.find-world nil worlds)
                  nil))
  :hints(("Goal"
          :induct (cdr-induction worlds)
          :expand (tactic.find-world nil worlds))))





;; Clause Rewrite Plans.
;;
;; We now develop "plans" which explain how a clause has been rewritten, and
;; which can be easily and efficiently justified.
;;
;; Plans can be either fast or slow.  A fast plan is justified (with a fully
;; expansive proof) via running the slow rewriter to build the necessary
;; ccsteps.  A slow plan was produced by using the slow rewriter, and has
;; the ccsteps to use built in.
;;
;; A plan can also be a FAILURE plan, which represents a clause that was not
;; rewritten successfully.

(defund rw.make-crewrite-clause-plan (clause fastp theoryname world)
  (declare (xargs :guard (and (consp clause)
                              (logic.term-listp clause)
                              (tactic.worldp world))))
  (if fastp
      ;; Construct a "fast" plan using the fast crewriter.
      (let* ((results      (rw.fast-crewrite-clause clause
                                                    (tactic.world->blimit world)
                                                    (tactic.world->rlimit world)
                                                    (tactic.world->control theoryname world)
                                                    (tactic.world->rwn world)))
             (provedp      (car results))
             (clause-prime (if provedp
                               nil
                             (second results))))
        (if (equal (fast-rev clause-prime) clause)
            (list 'fail clause)
          (let* ((forced-goals1 (third results))
                 (forced-goals  (remove-duplicates forced-goals1)))
            (ACL2::prog2$
             (or (same-lengthp forced-goals1 forced-goals)
                 (ACL2::cw! ";; local forced-duplicates elimination eats ~x0 goals.~%"
                            (- (fast-len forced-goals1 0)
                               (fast-len forced-goals 0))))
             (list 'fast
                   clause
                   clause-prime
                   theoryname
                   forced-goals
                   nil ;; ccsteps
                   )))))
    ;; Construct a "slow" plan using the ordinary crewriter.
    (let* ((ccsteps (rw.crewrite-clause clause
                                        (tactic.world->blimit world)
                                        (tactic.world->rlimit world)
                                        (tactic.world->control theoryname world)
                                        (tactic.world->rwn world)))
           (provedp (rw.ccstep->provedp (car ccsteps)))
           (clause-prime (if provedp
                             nil
                           (rw.ccstep->clause-prime (car ccsteps)))))
      (if (equal (fast-rev clause-prime) clause)
          (list 'fail clause)
        (let* ((forced-goals1 (rw.ccstep-list-forced-goals ccsteps))
               (forced-goals  (remove-duplicates forced-goals1)))
          (ACL2::prog2$
           (or (same-lengthp forced-goals1 forced-goals)
               (ACL2::cw! ";; local forced-duplicates elimination eats ~x0 goals.~%"
                          (- (fast-len forced-goals1 0)
                             (fast-len forced-goals 0))))
           (list 'slow
                 clause
                 clause-prime
                 theoryname
                 forced-goals
                 ccsteps)))))))

(defund rw.crewrite-clause-planp (x)
  ;; Basic structural well-formedness of plans.
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x)
       (let ((type (car x)))
         (if (equal type 'fail)
             ;; Failures are just ('fail <clause>)
             (and (tuplep 2 x)
                  (let ((clause (nth 1 x)))
                    (and (consp clause)
                         (logic.term-listp clause))))
           ;; Fast/slow are tuples with (type clause clause-prime theoryname fgoals windex ccsteps)
           (and (tuplep 6 x)
                (let ((clause       (nth 1 x))
                      (clause-prime (nth 2 x))
                      ;; (theoryname  (nth 3 x))
                      (forced-goals (nth 4 x))
                      (ccsteps      (nth 5 x)))
                  (and
                   ;; Basic well-formedness for either kind of plan
                   (consp clause)
                   (logic.term-listp clause)
                   (logic.formula-listp forced-goals)
                   (true-listp forced-goals)
                   ;; Clause prime is nil if proved, or well-formed
                   (or (not clause-prime)
                       (and (consp clause-prime)
                            (logic.term-listp clause-prime)))
                   (if (equal type 'fast)
                       ;; Fast plan need not have ccsteps
                       (not ccsteps)
                     ;; Slow plan needs to have ccsteps in agreement with other stuff.
                     (and (equal type 'slow)
                          (consp ccsteps)
                          (rw.ccstep-listp ccsteps)
                          (equal clause-prime
                                 (if (rw.ccstep->provedp (car ccsteps))
                                     nil
                                   (rw.ccstep->clause-prime (car ccsteps))))
                          (equal forced-goals
                                 (remove-duplicates
                                  (rw.ccstep-list-forced-goals ccsteps))))))))))))

(defund rw.crewrite-clause-plan-okp (x world)
  ;; Comprehensive, semantic well-formedness check.
  (declare (xargs :guard (and (rw.crewrite-clause-planp x)
                              (tactic.worldp world))
                  :verify-guards nil))
  (if (equal (car x) 'fail)
      t
    (let* ((type         (nth 0 x))
           (clause       (nth 1 x))
           (clause-prime (nth 2 x))
           (theoryname   (nth 3 x))
           (forced-goals (nth 4 x))
           (ccsteps      (nth 5 x)))
      (and world
           (if (equal type 'fast)
               ;; Fast steps are right if the clause-prime and forced-goals are
               ;; right.
               (let ((results (rw.fast-crewrite-clause clause
                                                       (tactic.world->blimit world)
                                                       (tactic.world->rlimit world)
                                                       (tactic.world->control theoryname world)
                                                       (tactic.world->rwn world))))
                 (and (equal clause-prime
                             (if (first results)
                                 nil
                               (second results)))
                      (equal forced-goals
                             (remove-duplicates (third results)))))
             ;; For slow steps, we only need to show that these are the right
             ;; ccsteps.
             (equal ccsteps
                    (rw.crewrite-clause clause
                                        (tactic.world->blimit world)
                                        (tactic.world->rlimit world)
                                        (tactic.world->control theoryname world)
                                        (tactic.world->rwn world))))))))

(defund rw.crewrite-clause-plan-atblp (x atbl)
  (declare (xargs :guard (and (rw.crewrite-clause-planp x)
                              (logic.arity-tablep atbl))
                  :verify-guards nil))
  (let ((clause (nth 1 x)))
    (logic.term-list-atblp clause atbl)))

(defund rw.crewrite-clause-plan->progressp (x)
  (declare (xargs :guard (rw.crewrite-clause-planp x)
                  :verify-guards nil))
  (not (equal (car x) 'fail)))

(defund rw.crewrite-clause-plan->clause (x)
  (declare (xargs :guard (rw.crewrite-clause-planp x)
                  :verify-guards nil))
  (nth 1 x))

(defund rw.crewrite-clause-plan->provedp (x)
  (declare (xargs :guard (rw.crewrite-clause-planp x)
                  :verify-guards nil))
  (and (not (equal (car x) 'fail))
       (not (nth 2 x))))

(defund rw.crewrite-clause-plan->clause-prime (x)
  (declare (xargs :guard (and (rw.crewrite-clause-planp x)
                              (not (rw.crewrite-clause-plan->provedp x)))
                  :verify-guards nil))
  (if (equal (car x) 'fail)
      (nth 1 x)
    (nth 2 x)))

(defund rw.crewrite-clause-plan->forced-goals (x)
  (declare (xargs :guard (rw.crewrite-clause-planp x)
                  :verify-guards nil))
  (if (equal (car x) 'fail)
      nil
    (nth 4 x)))


(defund rw.crewrite-clause-plan-compiler (x world proof fproofs)
  (declare (xargs :guard (and (rw.crewrite-clause-planp x)
                              (tactic.worldp world)
                              (rw.crewrite-clause-plan-okp x world)
                              (if (rw.crewrite-clause-plan->provedp x)
                                  (not proof)
                                (and (logic.appealp proof)
                                     (equal (logic.conclusion proof)
                                            (clause.clause-formula
                                             (rw.crewrite-clause-plan->clause-prime x)))))
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.crewrite-clause-plan->forced-goals x)
                                       (logic.strip-conclusions fproofs)))
                  :verify-guards nil))
  (let ((type (car x)))
    (if (equal type 'fail)
        proof
      (let* ((clause       (nth 1 x))
             ;(clause-prime (nth 2 x))
             (theoryname   (nth 3 x))
             ;(forced-goals (nth 4 x))
             (control      (tactic.world->control theoryname world))
             (blimit       (tactic.world->blimit world))
             (rlimit       (tactic.world->rlimit world))
             (rwn          (tactic.world->rwn world))
             (ccsteps      (if (equal type 'fast)
                               (ACL2::prog2$
                                (ACL2::cw "Warning: constructing ccsteps for fast crewrite plan.~%")
                                (rw.crewrite-clause clause
                                                    (tactic.world->blimit world)
                                                    (tactic.world->rlimit world)
                                                    (tactic.world->control theoryname world)
                                                    (tactic.world->rwn world)))
                             (nth 5 x))))
        (rw.crewrite-clause-bldr clause blimit rlimit control rwn ccsteps
                                 proof fproofs)))))

(defobligations rw.crewrite-clause-plan-compiler
  (rw.crewrite-clause-bldr))



(encapsulate
 ()

 ;; Ugggggh.... ACL2 is terrible at fertilizing correctly.  We introduce a bunch
 ;; of free-variable rules to get the job done.  This is so horrible.  Someone
 ;; really needs to invent a decent way to do this.

 (defthmd lemma-1-for-rw.crewrite-clause-plan
   (implies (and (equal x (remove-duplicates (rw.ccstep-list-forced-goals y)))
                 (force (rw.ccstep-listp y)))
            (equal (logic.formula-listp x)
                   t)))

 (defthmd lemma-2-for-rw.crewrite-clause-plan
   (implies (and (equal x (remove-duplicates (rw.ccstep-list-forced-goals y)))
                 (rw.ccstep-list-forced-goals y))
            (equal (consp x)
                   t)))

 (defthmd lemma-3-for-rw.crewrite-clause-plan
   (implies (equal x (rw.ccstep-list-forced-goals y))
            (equal (true-listp x)
                   t)))

 (defthmd lemma-4-for-rw.crewrite-clause-plan
   (implies (and (equal free (clause.make-clauses-from-arbitrary-formulas formulas))
                 (force (logic.formula-listp formulas)))
            (equal (logic.term-list-listp free)
                   t)))

 (defthmd lemma-5-for-rw.crewrite-clause-plan
   (implies (and (equal (cdr free) (clause.make-clauses-from-arbitrary-formulas formulas))
                 (force (logic.formula-listp formulas)))
            (equal (logic.term-list-listp free)
                   (logic.term-listp (car free)))))

 (defthmd lemma-6-for-rw.crewrite-clause-plan
   (implies (and (equal free (rw.ccstep->clause-prime x))
                 (force (rw.ccstepp x)))
            (equal (logic.term-listp free)
                   t)))

 (defthmd lemma-7-for-rw.crewrite-clause-plan
   (implies (equal free (clause.make-clauses-from-arbitrary-formulas formulas))
            (equal (cons-listp free)
                   t)))

 (defthmd lemma-8-for-rw.crewrite-clause-plan
   (implies (equal (cdr free) (clause.make-clauses-from-arbitrary-formulas formulas))
            (equal (cons-listp free)
                   (if (consp free)
                       (consp (car free))
                     t))))

 (defthmd lemma-9-for-rw.crewrite-clause-plan
   (implies (and (equal free (rw.ccstep->clause-prime x))
                 (force (rw.ccstepp x)))
            (equal (consp free)
                   (not (rw.ccstep->provedp x)))))

 (defthmd lemma-10-for-rw.crewrite-clause-plan
   (implies (equal free (remove-duplicates x))
            (subsetp x free)))


 (defthmd lemma-11-for-rw.crewrite-clause-plan
   (implies (equal free (remove-duplicates y))
            (equal (logic.formula-list-atblp free atbl)
                   (logic.formula-list-atblp y atbl))))


 (local (in-theory (enable lemma-1-for-rw.crewrite-clause-plan
                           lemma-2-for-rw.crewrite-clause-plan
                           lemma-3-for-rw.crewrite-clause-plan
                           lemma-4-for-rw.crewrite-clause-plan
                           lemma-5-for-rw.crewrite-clause-plan
                           lemma-6-for-rw.crewrite-clause-plan
                           lemma-7-for-rw.crewrite-clause-plan
                           lemma-8-for-rw.crewrite-clause-plan
                           lemma-9-for-rw.crewrite-clause-plan
                           lemma-10-for-rw.crewrite-clause-plan
                           lemma-11-for-rw.crewrite-clause-plan
                           )))

 (local (in-theory (enable rw.make-crewrite-clause-plan
                           rw.crewrite-clause-planp
                           rw.crewrite-clause-plan-okp
                           rw.crewrite-clause-plan-atblp
                           rw.crewrite-clause-plan->clause
                           rw.crewrite-clause-plan->provedp
                           rw.crewrite-clause-plan->clause-prime
                           rw.crewrite-clause-plan->forced-goals
                           rw.crewrite-clause-plan-compiler)))

 (verify-guards rw.crewrite-clause-planp)
 (verify-guards rw.crewrite-clause-plan-atblp)
 (verify-guards rw.crewrite-clause-plan-okp)
 (verify-guards rw.crewrite-clause-plan->clause)
 (verify-guards rw.crewrite-clause-plan->progressp)
 (verify-guards rw.crewrite-clause-plan->provedp)
 (verify-guards rw.crewrite-clause-plan->clause-prime)
 (verify-guards rw.crewrite-clause-plan->forced-goals)
 (verify-guards rw.crewrite-clause-plan-compiler)


 (defthm booleanp-of-rw.crewrite-clause-planp
   (equal (booleanp (rw.crewrite-clause-planp x))
          t))

 (defthm booleanp-of-rw.crewrite-clause-plan-okp
   (equal (booleanp (rw.crewrite-clause-plan-okp x world))
          t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm booleanp-of-rw.crewrite-clause-plan-atblp
   (equal (booleanp (rw.crewrite-clause-plan-atblp x atbl))
          t))

 (defthm consp-of-rw.crewrite-clause-plan->clause-prime
   (implies (force (and (rw.crewrite-clause-planp x)
                        (not (rw.crewrite-clause-plan->provedp x))))
            (equal (consp (rw.crewrite-clause-plan->clause-prime x))
                   t)))

(defthm logic.term-listp-of-rw.crewrite-clause-plan->clause-prime
   (implies (force (rw.crewrite-clause-planp x))
            (equal (logic.term-listp (rw.crewrite-clause-plan->clause-prime x))
                   t)))


(defthm true-listp-of-rw.crewrite-clause-plan->forced-goals
   (implies (force (rw.crewrite-clause-planp x))
            (equal (true-listp (rw.crewrite-clause-plan->forced-goals x))
                   t)))

(defthm logic.formula-listp-of-rw.crewrite-clause-plan->forced-goals
   (implies (force (rw.crewrite-clause-planp x))
            (equal (logic.formula-listp (rw.crewrite-clause-plan->forced-goals x))
                   t)))

(defthm logic.formula-list-atblp-of-rw.crewrite-clause-plan->forced-goals
; Matt K. mod for v7-2: Don't force assumption below with free variable.
   (implies (and (force (rw.crewrite-clause-planp x))
                 (rw.crewrite-clause-plan-okp x world)
                 (force (and (rw.crewrite-clause-plan-atblp x atbl)
                             (tactic.worldp world)
                             (tactic.world-atblp world atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             )))
            (equal (logic.formula-list-atblp (rw.crewrite-clause-plan->forced-goals x) atbl)
                   t)))




(defthm rw.crewrite-clause-plan->clause-of-rw.make-crewrite-clause-plan
   (equal (rw.crewrite-clause-plan->clause (rw.make-crewrite-clause-plan clause fastp theoryname world))
          clause)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

(defthm rw.crewrite-clause-planp-of-rw.make-crewrite-clause-plan
   (implies (force (and (consp clause)
                        (logic.term-listp clause)
                        (tactic.worldp world)))
            (equal (rw.crewrite-clause-planp (rw.make-crewrite-clause-plan clause fastp theoryname world))
                   t)))

 (defthm rw.crewrite-clause-plan-okp-of-rw.make-crewrite-clause-plan
   (implies (force (and (consp clause)
                        (logic.term-listp clause)
                        (tactic.worldp world)))
            (equal (rw.crewrite-clause-plan-okp
                    (rw.make-crewrite-clause-plan clause fastp theoryname world)
                    world)
                   t)))

 (defthm rw.crewrite-clause-plan-atblp-of-rw.make-crewrite-clause-plan
   (implies (force (logic.term-list-atblp clause atbl))
            (equal (rw.crewrite-clause-plan-atblp
                    (rw.make-crewrite-clause-plan clause fastp theoryname world)
                    atbl)
                   t))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm logic.appealp-of-rw.crewrite-clause-plan-compiler
   (implies (force (and (rw.crewrite-clause-planp x)
                        (tactic.worldp world)
                        (rw.crewrite-clause-plan-okp x world)
                        (if (rw.crewrite-clause-plan->provedp x)
                            (not proof)
                          (and (logic.appealp proof)
                               (equal (logic.conclusion proof)
                                      (clause.clause-formula
                                       (rw.crewrite-clause-plan->clause-prime x)))))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.crewrite-clause-plan->forced-goals x)
                                 (logic.strip-conclusions fproofs))))
            (equal (logic.appealp (rw.crewrite-clause-plan-compiler x world proof fproofs))
                   t)))

 (defthm logic.conclusion-of-rw.crewrite-clause-plan-compiler
   (implies (force (and (rw.crewrite-clause-planp x)
                        (tactic.worldp world)
                        (rw.crewrite-clause-plan-okp x world)
                        (if (rw.crewrite-clause-plan->provedp x)
                            (not proof)
                          (and (logic.appealp proof)
                               (equal (logic.conclusion proof)
                                      (clause.clause-formula
                                       (rw.crewrite-clause-plan->clause-prime x)))))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.crewrite-clause-plan->forced-goals x)
                                 (logic.strip-conclusions fproofs))))
            (equal (logic.conclusion (rw.crewrite-clause-plan-compiler x world proof fproofs))
                   (clause.clause-formula (rw.crewrite-clause-plan->clause x)))))

 (defthm@ logic.proofp-of-rw.crewrite-clause-plan-compiler
   (implies (force (and (rw.crewrite-clause-planp x)
                        (tactic.worldp world)
                        (rw.crewrite-clause-plan-okp x world)
                        (if (rw.crewrite-clause-plan->provedp x)
                            (not proof)
                          (and (logic.appealp proof)
                               (equal (logic.conclusion proof)
                                      (clause.clause-formula
                                       (rw.crewrite-clause-plan->clause-prime x)))
                               ;; ---
                               (logic.proofp proof axioms thms atbl)
                               ))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.crewrite-clause-plan->forced-goals x)
                                 (logic.strip-conclusions fproofs))
                        ;; ---
                        (rw.crewrite-clause-plan-atblp x atbl)
                        (rw.crewrite-clause-plan-okp x world)
                        (logic.proof-listp fproofs axioms thms atbl)
                        (tactic.world-atblp world atbl)
                        (tactic.world-env-okp world axioms thms)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations rw.crewrite-clause-plan-compiler)))
            (equal (logic.proofp (rw.crewrite-clause-plan-compiler x world proof fproofs)
                                 axioms thms atbl)
                   t))))


(deflist rw.crewrite-clause-plan-listp (x)
  (rw.crewrite-clause-planp x)
  :elementp-of-nil nil)

(deflist rw.crewrite-clause-plan-list-okp (x world)
  (rw.crewrite-clause-plan-okp x world)
  :guard (and (rw.crewrite-clause-plan-listp x)
              (tactic.worldp world)))

(deflist rw.crewrite-clause-plan-list-atblp (x atbl)
  (rw.crewrite-clause-plan-atblp x atbl)
  :guard (and (rw.crewrite-clause-plan-listp x)
              (logic.arity-tablep atbl)))


(defprojection
  ;; Note: redefined in interface/rewrite-tactics to add timing info.
  :list (rw.make-crewrite-clause-plan-list x fastp theoryname world)
  :element (rw.make-crewrite-clause-plan x fastp theoryname world)
  :guard (and (cons-listp x)
              (logic.term-list-listp x)
              (tactic.worldp world)))

(defund rw.crewrite-clause-plan-list->progressp (x)
  (declare (xargs :guard (rw.crewrite-clause-plan-listp x)))
  (if (consp x)
      (or (rw.crewrite-clause-plan->progressp (car x))
          (rw.crewrite-clause-plan-list->progressp (cdr x)))
    nil))

(defprojection
  :list (rw.crewrite-clause-plan-list->clauses x)
  :element (rw.crewrite-clause-plan->clause x)
  :guard (rw.crewrite-clause-plan-listp x))

(defthm rw.crewrite-clause-plan-list->clauses-of-rw.make-crewrite-clause-plan-list
  (equal (rw.crewrite-clause-plan-list->clauses
          (rw.make-crewrite-clause-plan-list x fastp theoryname world))
         (list-fix x))
  :hints(("Goal"
          :induct (cdr-induction x))))

(defund rw.crewrite-clause-plan-list->clauses-prime (x)
  (declare (xargs :guard (rw.crewrite-clause-plan-listp x)))
  (if (consp x)
      (if (rw.crewrite-clause-plan->provedp (car x))
          (rw.crewrite-clause-plan-list->clauses-prime (cdr x))
        (cons (rw.crewrite-clause-plan->clause-prime (car x))
              (rw.crewrite-clause-plan-list->clauses-prime (cdr x))))
    nil))

(defthm cons-listp-of-rw.crewrite-clause-plan-list->clauses-prime
  (implies (force (rw.crewrite-clause-plan-listp x))
           (equal (cons-listp (rw.crewrite-clause-plan-list->clauses-prime x))
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand (rw.crewrite-clause-plan-list->clauses-prime x))))

(defthm logic.term-list-listp-of-rw.crewrite-clause-plan-list->clauses-prime
  (implies (force (rw.crewrite-clause-plan-listp x))
           (equal (logic.term-list-listp (rw.crewrite-clause-plan-list->clauses-prime x))
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand (rw.crewrite-clause-plan-list->clauses-prime x))))



(defund rw.crewrite-clause-plan-list->forced-goals (x)
  (declare (xargs :guard (rw.crewrite-clause-plan-listp x)))
  (if (consp x)
      (revappend (rw.crewrite-clause-plan->forced-goals (car x))
                 (rw.crewrite-clause-plan-list->forced-goals (cdr x)))
    nil))

(defthm true-listp-of-rw.crewrite-clause-plan-list->forced-goals
  (equal (true-listp (rw.crewrite-clause-plan-list->forced-goals x))
         t)
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand (rw.crewrite-clause-plan-list->forced-goals x))))

(defthm logic.formula-listp-of-rw.crewrite-clause-plan-list->forced-goals
  (implies (force (rw.crewrite-clause-plan-listp x))
           (equal (logic.formula-listp (rw.crewrite-clause-plan-list->forced-goals x))
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand (rw.crewrite-clause-plan-list->forced-goals x))))

(defthm logic.formula-list-atblp-of-rw.crewrite-clause-plan-list->forced-goals
  (implies (force (and (rw.crewrite-clause-plan-listp x)
                       (rw.crewrite-clause-plan-list-atblp x atbl)
                       (rw.crewrite-clause-plan-list-okp x world)
                       (tactic.worldp world)
                       (tactic.world-atblp world atbl)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.formula-list-atblp (rw.crewrite-clause-plan-list->forced-goals x) atbl)
                  t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand (rw.crewrite-clause-plan-list->forced-goals x))))

(defthm rw.crewrite-clause-plan-listp-of-rw.make-crewrite-clause-plan-list
  (implies (force (and (cons-listp x)
                       (logic.term-list-listp x)
                       (tactic.worldp world)))
           (rw.crewrite-clause-plan-listp
            (rw.make-crewrite-clause-plan-list x fastp theoryname world)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.crewrite-clause-plan-list-okp-of-rw.make-crewrite-clause-plan-list
  (implies (force (and (cons-listp x)
                       (logic.term-list-listp x)
                       (tactic.worldp world)))
           (equal (rw.crewrite-clause-plan-list-okp
                   (rw.make-crewrite-clause-plan-list x fastp theoryname world)
                   world)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.crewrite-clause-plan-list-atblp-of-rw.make-crewrite-clause-plan-list
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (rw.crewrite-clause-plan-list-atblp
                   (rw.make-crewrite-clause-plan-list x fastp theoryname world)
                    atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defund rw.crewrite-clause-plan-list-compiler (x world proofs fproofs)
  (declare (xargs :guard (and (rw.crewrite-clause-plan-listp x)
                              (tactic.worldp world)
                              (rw.crewrite-clause-plan-list-okp x world)
                              (logic.appeal-listp proofs)
                              (logic.appeal-listp fproofs)
                              (equal (clause.clause-list-formulas
                                      (rw.crewrite-clause-plan-list->clauses-prime x))
                                     (logic.strip-conclusions proofs))
                              (subsetp (rw.crewrite-clause-plan-list->forced-goals x)
                                       (logic.strip-conclusions fproofs)))
                  :verify-guards nil))
  (if (consp x)
      (if (rw.crewrite-clause-plan->provedp (car x))
          ;; We proved clause directly; use nil as the input proof.
          (cons (ACL2::prog2$ (ACL2::cw! ";; Compiling winning rewrite for clause ~x0.~%" (fast-len x 0))
                              (rw.crewrite-clause-plan-compiler (car x) world nil fproofs))
                (rw.crewrite-clause-plan-list-compiler (cdr x) world proofs fproofs))
        ;; We need the input proof.
        (cons (ACL2::prog2$ (ACL2::cw! ";; Compiling rewrite for clause ~x0.~%" (fast-len x 0))
                            (rw.crewrite-clause-plan-compiler (car x) world (car proofs) fproofs))
              (rw.crewrite-clause-plan-list-compiler (cdr x) world (cdr proofs) fproofs)))
    nil))

(defobligations rw.crewrite-clause-plan-list-compiler
  (rw.crewrite-clause-plan-compiler))

(verify-guards rw.crewrite-clause-plan-list-compiler
               :hints(("Goal" :in-theory (enable rw.crewrite-clause-plan-list-compiler
                                                 rw.crewrite-clause-plan-list->clauses-prime
                                                 rw.crewrite-clause-plan-list->forced-goals))))

(defthm logic.appeal-listp-of-rw.crewrite-clause-plan-list-compiler
  (implies (force (and (rw.crewrite-clause-plan-listp x)
                       (tactic.worldp world)
                       (rw.crewrite-clause-plan-list-okp x world)
                       (logic.appeal-listp proofs)
                       (logic.appeal-listp fproofs)
                       (equal (clause.clause-list-formulas
                               (rw.crewrite-clause-plan-list->clauses-prime x))
                              (logic.strip-conclusions proofs))
                       (subsetp (rw.crewrite-clause-plan-list->forced-goals x)
                                (logic.strip-conclusions fproofs))))
           (equal (logic.appeal-listp
                   (rw.crewrite-clause-plan-list-compiler x world proofs fproofs))
                  t))
  :hints(("Goal"
          :induct (rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
          :in-theory (enable (:induction rw.crewrite-clause-plan-list-compiler))
          :expand ((rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
                   (rw.crewrite-clause-plan-list->clauses-prime x)
                   (rw.crewrite-clause-plan-list->forced-goals x)
                   ))))

(defthm logic.strip-conclusions-of-rw.crewrite-clause-plan-list-compiler
  (implies (force (and (rw.crewrite-clause-plan-listp x)
                       (tactic.worldp world)
                       (rw.crewrite-clause-plan-list-okp x world)
                       (logic.appeal-listp proofs)
                       (logic.appeal-listp fproofs)
                       (equal (clause.clause-list-formulas
                               (rw.crewrite-clause-plan-list->clauses-prime x))
                              (logic.strip-conclusions proofs))
                       (subsetp (rw.crewrite-clause-plan-list->forced-goals x)
                                (logic.strip-conclusions fproofs))))
           (equal (logic.strip-conclusions (rw.crewrite-clause-plan-list-compiler x world proofs fproofs))
                  (clause.clause-list-formulas
                   (rw.crewrite-clause-plan-list->clauses x))))
  :hints(("Goal"
          :induct (rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
          :in-theory (enable (:induction rw.crewrite-clause-plan-list-compiler))
          :expand ((rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
                   (rw.crewrite-clause-plan-list->clauses-prime x)
                   (rw.crewrite-clause-plan-list->forced-goals x)
                   ))))

(defthm@ logic.proof-listp-of-rw.crewrite-clause-plan-list-compiler
   (implies (force (and (rw.crewrite-clause-plan-listp x)
                        (tactic.worldp world)
                        (rw.crewrite-clause-plan-list-okp x world)
                        (logic.appeal-listp proofs)
                        (logic.appeal-listp fproofs)
                        (equal (clause.clause-list-formulas
                                (rw.crewrite-clause-plan-list->clauses-prime x))
                               (logic.strip-conclusions proofs))
                        (subsetp (rw.crewrite-clause-plan-list->forced-goals x)
                                 (logic.strip-conclusions fproofs))
                        ;; ---
                        (rw.crewrite-clause-plan-list-atblp x atbl)
                        (rw.crewrite-clause-plan-list-okp x world)
                        (logic.proof-listp proofs axioms thms atbl)
                        (logic.proof-listp fproofs axioms thms atbl)
                        (tactic.world-atblp world atbl)
                        (tactic.world-env-okp world axioms thms)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations rw.crewrite-clause-plan-list-compiler)))
            (equal (logic.proof-listp (rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
                                      axioms thms atbl)
                   t))
    :hints(("Goal"
          :induct (rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
          :in-theory (enable (:induction rw.crewrite-clause-plan-list-compiler))
          :expand ((rw.crewrite-clause-plan-list-compiler x world proofs fproofs)
                   (rw.crewrite-clause-plan-list->clauses-prime x)
                   (rw.crewrite-clause-plan-list->forced-goals x)
                   ))))



(defthm rw.crewrite-clause-plan-atblp-removal
  (equal (rw.crewrite-clause-plan-atblp plan atbl)
         (logic.term-list-atblp (rw.crewrite-clause-plan->clause plan) atbl))
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-plan-atblp
                                    rw.crewrite-clause-plan->clause))))


(defthm rw.crewrite-clause-plan-list-atblp-removal
  (equal (rw.crewrite-clause-plan-list-atblp x atbl)
         (logic.term-list-list-atblp (rw.crewrite-clause-plan-list->clauses x) atbl))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.crewrite-clause-plan-list->clauses x)
                   (rw.crewrite-clause-plan-list-atblp x atbl)))))






(defthm consp-of-rw.crewrite-clause-plan->clause
  (implies (rw.crewrite-clause-planp plan)
           (equal (consp (rw.crewrite-clause-plan->clause plan))
                  t))
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-planp
                                    rw.crewrite-clause-plan->clause))))

(defthm logic.term-listp-of-rw.crewrite-clause-plan->clause
  (implies (rw.crewrite-clause-planp plan)
           (equal (logic.term-listp (rw.crewrite-clause-plan->clause plan))
                  t))
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-planp
                                    rw.crewrite-clause-plan->clause))))


(defund rw.crewrite-clause-plan-compiler-high (x world proof fproofs)
  (declare (xargs :guard (and (rw.crewrite-clause-planp x)
                              (tactic.worldp world)
                              (rw.crewrite-clause-plan-okp x world)
                              (if (rw.crewrite-clause-plan->provedp x)
                                  (not proof)
                                (and (logic.appealp proof)
                                     (equal (logic.conclusion proof)
                                            (clause.clause-formula
                                             (rw.crewrite-clause-plan->clause-prime x)))))
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.crewrite-clause-plan->forced-goals x)
                                       (logic.strip-conclusions fproofs)))
                  :guard-hints(("Goal" :in-theory (enable rw.crewrite-clause-planp
                                                          rw.crewrite-clause-plan->clause)))))
  (let ((fsubproofs (logic.find-proofs
                     (rw.crewrite-clause-plan->forced-goals x)
                     fproofs)))
    (logic.appeal 'rw.crewrite-clause-plan-compiler
                  (clause.clause-formula (rw.crewrite-clause-plan->clause x))
                  (if proof
                      (cons proof fsubproofs)
                    fsubproofs)
                  (list (tactic.world->index world) x))))

(defund rw.crewrite-clause-plan-compiler-okp (x worlds atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (tactic.world-listp worlds)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'rw.crewrite-clause-plan-compiler)
         (tuplep 2 extras)
         (let* ((windex  (first extras))
                (plan    (second extras))
                (world   (tactic.find-world windex worlds)))
           (and world
                ;; Lots of 'fusion'/'deforestation' possibilities here.
                (rw.crewrite-clause-planp plan)
                (rw.crewrite-clause-plan-okp plan world)
                (rw.crewrite-clause-plan-atblp plan atbl)
                (let ((clause  (rw.crewrite-clause-plan->clause plan))
                      (provedp (rw.crewrite-clause-plan->provedp plan))
                      (fgoals  (rw.crewrite-clause-plan->forced-goals plan)))
                  (and
                   (equal conclusion (clause.clause-formula clause))
                   (equal (logic.strip-conclusions subproofs)
                          (if provedp
                              fgoals
                            (cons (clause.clause-formula (rw.crewrite-clause-plan->clause-prime plan))
                                  fgoals))))))))))

(defthm rw.crewrite-clause-plan-compiler-okp-of-rw.crewrite-clause-plan-compiler-high
  (implies (and (rw.crewrite-clause-planp x)
                (tactic.worldp world)
                (rw.crewrite-clause-plan-okp x world)
                (if (rw.crewrite-clause-plan->provedp x)
                    (not proof)
                  (and (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula
                               (rw.crewrite-clause-plan->clause-prime x)))))
                (logic.appeal-listp fproofs)
                (subsetp (rw.crewrite-clause-plan->forced-goals x)
                         (logic.strip-conclusions fproofs))
                ;; -----
                ;; hrmn, non-guard things that need to hold.
                (rw.crewrite-clause-plan-atblp x atbl)
                (equal (tactic.find-world (TACTIC.WORLD->INDEX WORLD) worlds) world)
                )
           (equal (rw.crewrite-clause-plan-compiler-okp
                   (rw.crewrite-clause-plan-compiler-high x world proof fproofs)
                   worlds atbl)
                  t))
  :hints(("Goal" :in-theory (enable
                             rw.crewrite-clause-plan-compiler-okp
                             rw.crewrite-clause-plan-compiler-high))))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-clause-plan-compiler-okp)))

 (defthm booleanp-of-rw.crewrite-clause-plan-compiler-okp
   (equal (booleanp (rw.crewrite-clause-plan-compiler-okp x worlds atbl))
          t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.crewrite-clause-plan-compiler-okp-of-logic.appeal-identity
   (equal (rw.crewrite-clause-plan-compiler-okp (logic.appeal-identity x) worlds atbl)
          (rw.crewrite-clause-plan-compiler-okp x worlds atbl))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-rw.crewrite-clause-plan-compiler-okp
   (implies (and (rw.crewrite-clause-plan-compiler-okp x worlds atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (tactic.world-listp worlds)
                 (tactic.world-list-atblp worlds atbl)
                 (tactic.world-list-env-okp worlds axioms thms))
            (equal (logic.conclusion
                    (let* ((plan        (second (logic.extras x)))
                           (world      (tactic.find-world (first (logic.extras x)) worlds))
                           (provedp    (rw.crewrite-clause-plan->provedp plan))
                           (subproofs* (logic.provable-list-witness
                                        (logic.strip-conclusions (logic.subproofs x))
                                        axioms thms atbl))
                           (proof      (if provedp nil (car subproofs*)))
                           (fproofs    (if provedp subproofs* (cdr subproofs*))))
                      (rw.crewrite-clause-plan-compiler plan world proof fproofs)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-rw.crewrite-clause-plan-compiler-okp
   (implies (and (rw.crewrite-clause-plan-compiler-okp x worlds atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (tactic.world-listp worlds)
                 (tactic.world-list-atblp worlds atbl)
                 (tactic.world-list-env-okp worlds axioms thms)
                 (equal (cdr (lookup 'if atbl)) 3)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (@obligations rw.crewrite-clause-plan-compiler))
            (equal (logic.proofp
                    (let* ((plan        (second (logic.extras x)))
                           (world      (tactic.find-world (first (logic.extras x)) worlds))
                           (provedp    (rw.crewrite-clause-plan->provedp plan))
                           (subproofs* (logic.provable-list-witness
                                        (logic.strip-conclusions (logic.subproofs x))
                                        axioms thms atbl))
                           (proof      (if provedp nil (car subproofs*)))
                           (fproofs    (if provedp subproofs* (cdr subproofs*))))
                      (rw.crewrite-clause-plan-compiler plan world proof fproofs))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.crewrite-clause-plan-compiler-okp
   (implies (and (rw.crewrite-clause-plan-compiler-okp x worlds atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (tactic.world-listp worlds)
                             (tactic.world-list-atblp worlds atbl)
                             (tactic.world-list-env-okp worlds axioms thms)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (@obligations rw.crewrite-clause-plan-compiler))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :use ((:instance lemma-1-for-soundness-of-rw.crewrite-clause-plan-compiler-okp)
                  (:instance lemma-2-for-soundness-of-rw.crewrite-clause-plan-compiler-okp)
                  (:instance forcing-logic.provablep-when-logic.proofp
                             (x (let* ((plan        (second (logic.extras x)))
                                       (world      (tactic.find-world (first (logic.extras x)) worlds))
                                       (provedp    (rw.crewrite-clause-plan->provedp plan))
                                       (subproofs* (logic.provable-list-witness
                                                    (logic.strip-conclusions (logic.subproofs x))
                                                    axioms thms atbl))
                                       (proof      (if provedp nil (car subproofs*)))
                                       (fproofs    (if provedp subproofs* (cdr subproofs*))))
                                  (rw.crewrite-clause-plan-compiler plan world proof fproofs)))))))))


