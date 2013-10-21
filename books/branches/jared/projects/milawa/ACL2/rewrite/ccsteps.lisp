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
(include-book "../clauses/clean-clauses")
(include-book "../build/top")
(include-book "traces/trace-compiler")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Essay on conditionally rewriting clauses
;;
;; We now extend our conditional rewriter across a clause.  We use an
;; accumulator-style function which treats the clause as two pieces, todo and
;; done.  To begin we load all the literals into the todo list, and at each
;; step, we rewrite the first todo literal and move it to the done list.
;;
;; Suppose we are given the lists of literals todo = [t1, ..., tn] and done =
;; [d1, ..., dm].  We say the goal for this step is to prove the "step
;; formula", (t1 v ... v tn) v (d1 v ... v dn).  Since todo is initially set to
;; the whole clause we want to rewrite, the "original goal" (i.e., the goal for
;; the first step) will be to prove t1 v ... v tn.  That is, initially we want
;; to prove the whole clause we are rewriting.  Each step "reduces" this goal,
;; which is probably hard to prove, into a new goal which is hopefully easier
;; to prove because some literal has been rewritten.  In the end, all of the
;; rewritten literals are in done, so our final goal is to prove the rewritten
;; clause.
;;
;; When we build the proof corresponding to this rewriting, the process gets
;; reversed.  That is, assume we have a proof of the fully rewritten clause.
;; We now need to "unwind" each step, building a proof of each step-goal by
;; starting with the final step and working our way towards the original goal.
;; That is, given a proof of the fully rewritten clause, we work backwards to
;; construct a proof of the original clause.
;;
;; So how does each step work?  To make progress, we are first going to rewrite
;; t1 to t1' and then move t1' over to the done list.
;;
;; To rewrite t1, we can assume:
;;
;;    (1) [t2, ..., tn] are false, and
;;    (2) [d1, ..., dm] are false.
;;
;; As we assume these things, we might notice that we have contradictory assms,
;; in which case we can use the contradiction to immediately prove the clause
;; and we can stop early.
;;
;; Otherwise, we rewrite t1 to t1' under these assumptions.  We might notice
;; that t1' is obviously true, which means we have proven the goal and we can
;; stop without doing any more rewriting.  But usually this is not the case, so
;; we create a new todo and done list:
;;
;;   Todo': [t2, ..., tn]
;;   Done': [t1', d1, ..., dm]
;;
;; And these lists mark the beginning of the next step.



;; Representation of steps
;;
;; When we take each step, we need to record enough information to build a
;; proof of the step goal, given a proof of the next-step's goal.  We do
;; this using a ccstep ("crewrite clause step") structure.
;;
;; These structures contain:
;;
;;   - the term we rewrite, i.e., "t1",
;;   - the hypbox we were using, and then either:
;;       1. a proof of the hypbox formula, if there is a contradiction, or
;;       2. a trace of how t1 gets rewritten, otherwise.
;;
;; Note that from this, we can also recover:
;;
;;   - todo, by adding t1 to the "left nhyps" from the hypbox
;;   - done, by taking the "right nhyps" from the hypbox, and
;;   - (if there was no contradiction) t1-prime, by taking the rhs of the trace

(defsection rw.ccstepp

  (definlined rw.ccstepp (x)
    ;; ((term . hypbox) . (contradiction? . trace?))
    (declare (xargs :guard t))
    (let ((term          (car (car x)))
          (hypbox        (cdr (car x)))
          (contradiction (car (cdr x)))
          (trace         (cdr (cdr x))))
      (and (logic.termp term)
           (rw.hypboxp hypbox)
           (if contradiction
               (and (rw.eqtracep contradiction)
                    (rw.eqtrace-contradictionp contradiction)
                    (rw.eqtrace-okp contradiction hypbox)
                    (not trace))
             (and (rw.tracep trace)
                  (rw.trace->iffp trace)
                  (equal (rw.trace->hypbox trace) hypbox)
                  (equal (rw.trace->lhs trace) term))))))

  (definlined rw.ccstep->term (x)
    (declare (xargs :guard (rw.ccstepp x)))
    (car (car x)))

  (definlined rw.ccstep->hypbox (x)
    (declare (xargs :guard (rw.ccstepp x)))
    (cdr (car x)))

  (definlined rw.ccstep->contradiction (x)
    (declare (xargs :guard (rw.ccstepp x)))
    (car (cdr x)))

  (definlined rw.ccstep->trace (x)
    (declare (xargs :guard (rw.ccstepp x)))
    (cdr (cdr x)))

  (definlined rw.ccstep (term hypbox contradiction trace)
    (declare (xargs :guard (and (logic.termp term)
                                (rw.hypboxp hypbox)
                                (if contradiction
                                    (and (rw.eqtracep contradiction)
                                         (rw.eqtrace-contradictionp contradiction)
                                         (rw.eqtrace-okp contradiction hypbox)
                                         (not trace))
                                  (and (rw.tracep trace)
                                       (rw.trace->iffp trace)
                                       (equal (rw.trace->hypbox trace) hypbox)
                                       (equal (rw.trace->lhs trace) term))))))
    (cons (cons term hypbox)
          (cons contradiction trace)))

  (local (in-theory (enable rw.ccstepp
                            rw.ccstep
                            rw.ccstep->term
                            rw.ccstep->hypbox
                            rw.ccstep->contradiction
                            rw.ccstep->trace)))

  (defthm booleanp-of-rw.ccstepp
    (equal (booleanp (rw.ccstepp x))
           t))

  (defthm forcing-rw.ccstepp-of-rw.ccstep
    (implies (force (and (logic.termp term)
                         (rw.hypboxp hypbox)
                         (if contradiction
                             (and (rw.eqtracep contradiction)
                                  (rw.eqtrace-contradictionp contradiction)
                                  (rw.eqtrace-okp contradiction hypbox)
                                  (not trace))
                           (and (rw.tracep trace)
                                (rw.trace->iffp trace)
                                (equal (rw.trace->hypbox trace) hypbox)
                                (equal (rw.trace->lhs trace) term)))))
             (equal (rw.ccstepp (rw.ccstep term hypbox contradiction trace))
                    t)))

  (defthm rw.ccstep->term-of-rw.ccstep
    (equal (rw.ccstep->term (rw.ccstep term hypbox contradiction trace))
           term))

  (defthm rw.ccstep->hypbox-of-rw.ccstep
    (equal (rw.ccstep->hypbox (rw.ccstep term hypbox contradiction trace))
           hypbox))

  (defthm rw.ccstep->contradiction-of-rw.ccstep
    (equal (rw.ccstep->contradiction (rw.ccstep term hypbox contradiction trace))
           contradiction))

  (defthm rw.ccstep->trace-of-rw.ccstep
    (equal (rw.ccstep->trace (rw.ccstep term hypbox contradiction trace))
           trace))

  (defthm forcing-logic.termp-of-rw.ccstep->term
    (implies (force (rw.ccstepp x))
             (equal (logic.termp (rw.ccstep->term x))
                    t)))

  (defthm forcing-rw.hypboxp-of-rw.ccstep->hypbox
    (implies (force (rw.ccstepp x))
             (equal (rw.hypboxp (rw.ccstep->hypbox x))
                    t)))

  (defthm forcing-rw.eqtracep-of-rw.ccstep->contradiction
    (implies (force (and (rw.ccstep->contradiction x)
                         (rw.ccstepp x)))
             (equal (rw.eqtracep (rw.ccstep->contradiction x))
                    t)))

  (defthm forcing-rw.eqtrace-contradictionp-of-rw.ccstep->contradiction
    (implies (force (and (rw.ccstep->contradiction x)
                         (rw.ccstepp x)))
             (equal (rw.eqtrace-contradictionp (rw.ccstep->contradiction x))
                    t)))

  (defthm forcing-rw.eqtrace-okp-of-rw.ccstep->contradiction
    (implies (force (and (rw.ccstep->contradiction x)
                         (rw.ccstepp x)))
             (equal (rw.eqtrace-okp (rw.ccstep->contradiction x) (rw.ccstep->hypbox x))
                    t)))

  (defthm forcing-rw.hypbox->right-of-rw.ccstep->hypbox-when-rw.ccstep->contradiction
    (implies (and (rw.ccstep->contradiction x)
                  (force (rw.ccstepp x))
                  (not (rw.hypbox->left (rw.ccstep->hypbox x))))
             (iff (rw.hypbox->right (rw.ccstep->hypbox x))
                  t)))

  (defthm forcing-rw.tracep-of-rw.ccstep->trace
    (implies (force (and (not (rw.ccstep->contradiction x))
                         (rw.ccstepp x)))
             (equal (rw.tracep (rw.ccstep->trace x))
                    t)))

  (defthm forcing-rw.trace->iffp-of-rw.ccstep->trace
    (implies (force (and (not (rw.ccstep->contradiction x))
                         (rw.ccstepp x)))
             (equal (rw.trace->iffp (rw.ccstep->trace x))
                    t)))

  (defthm forcing-rw.trace->hypbox-of-rw.ccstep->trace
    (implies (force (and (not (rw.ccstep->contradiction x))
                         (rw.ccstepp x)))
             (equal (rw.trace->hypbox (rw.ccstep->trace x))
                    (rw.ccstep->hypbox x))))

  (defthm forcing-rw.trace->lhs-of-rw.ccstep->trace
    (implies (force (and (not (rw.ccstep->contradiction x))
                         (rw.ccstepp x)))
             (equal (rw.trace->lhs (rw.ccstep->trace x))
                    (rw.ccstep->term x)))))


;; (defthm rw.ccstepp-when-not-consp
;;   (implies (not (consp x))
;;            (equal (rw.ccstepp x)
;;                   nil))
;;   :hints(("Goal" :in-theory (enable rw.ccstepp))))

;; (defthm consp-of-rw.ccstep
;;   (equal (consp (rw.ccstep term hypbox contradiction trace))
;;          t)
;;   :hints(("Goal" :in-theory (enable rw.ccstep))))



(deflist rw.ccstep-listp (x)
  (rw.ccstepp x)
  :elementp-of-nil nil)

(deflist rw.ccstep-list-listp (x)
  (rw.ccstep-listp x)
  :elementp-of-nil t)

(defprojection :list (rw.ccstep-list-terms x)
               :element (rw.ccstep->term x)
               :guard (rw.ccstep-listp x)
               :nil-preservingp t)

(defprojection :list (rw.ccstep-list-list-terms x)
               :element (rw.ccstep-list-terms x)
               :guard (rw.ccstep-list-listp x)
               :nil-preservingp t)

(defprojection :list (rw.ccstep-list-hypboxes x)
               :element (rw.ccstep->hypbox x)
               :guard (rw.ccstep-listp x)
               :nil-preservingp t)

(defprojection :list (rw.ccstep-list-list-hypboxes x)
               :element (rw.ccstep-list-hypboxes x)
               :guard (rw.ccstep-list-listp x)
               :nil-preservingp t)




(defsection rw.ccstep-list-gather-traces

  (defund rw.ccstep-list-gather-traces (x)
    ;; BOZO tail-recursive version?
    (declare (xargs :guard (rw.ccstep-listp x)))
    (if (consp x)
        (if (rw.ccstep->contradiction (car x))
            (rw.ccstep-list-gather-traces (cdr x))
          (cons (rw.ccstep->trace (car x))
                (rw.ccstep-list-gather-traces (cdr x))))
      nil))

  (defthm rw.ccstep-list-gather-traces-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list-gather-traces x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-gather-traces))))

  (defthm rw.ccstep-list-gather-traces-of-cons
    (equal (rw.ccstep-list-gather-traces (cons a x))
           (if (rw.ccstep->contradiction a)
               (rw.ccstep-list-gather-traces x)
             (cons (rw.ccstep->trace a)
                   (rw.ccstep-list-gather-traces x))))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-gather-traces))))

  (defthm true-listp-of-rw.ccstep-list-gather-traces
    (equal (true-listp (rw.ccstep-list-gather-traces x))
           t)
    :hints(("Goal" :induct (cdr-induction x)))))



(defsection rw.ccstep-list-list-gather-traces

  (defund rw.ccstep-list-list-gather-traces (x)
    ;; BOZO tail-recursive version?
    (declare (xargs :guard (rw.ccstep-list-listp x)))
    (if (consp x)
        (fast-app (rw.ccstep-list-gather-traces (car x))
                  (rw.ccstep-list-list-gather-traces (cdr x)))
      nil))

  (defthm rw.ccstep-list-list-gather-traces-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list-list-gather-traces x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-list-gather-traces))))

  (defthm true-listp-of-rw.ccstep-list-list-gather-traces
    (equal (true-listp (rw.ccstep-list-list-gather-traces x))
           t)
    :hints(("Goal"
            :expand (rw.ccstep-list-list-gather-traces x)
            :induct (cdr-induction x))))

  (defthm rw.ccstep-list-list-gather-traces-of-cons
    (equal (rw.ccstep-list-list-gather-traces (cons a x))
           (app (rw.ccstep-list-gather-traces a)
                (rw.ccstep-list-list-gather-traces x)))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-list-gather-traces)))))



(defsection rw.ccstep-list-gather-contradictions

  (defund rw.ccstep-list-gather-contradictions (x)
    ;; BOZO tail-recursive version?
    (declare (xargs :guard (rw.ccstep-listp x)))
    (if (consp x)
        (if (rw.ccstep->contradiction (car x))
            (cons (rw.ccstep->contradiction (car x))
                  (rw.ccstep-list-gather-contradictions (cdr x)))
          (rw.ccstep-list-gather-contradictions (cdr x)))
      nil))

  (defthm rw.ccstep-list-gather-contradictions-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list-gather-contradictions x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-gather-contradictions))))

  (defthm rw.ccstep-list-gather-contradictions-of-cons
    (equal (rw.ccstep-list-gather-contradictions (cons a x))
           (if (rw.ccstep->contradiction a)
               (cons (rw.ccstep->contradiction a)
                     (rw.ccstep-list-gather-contradictions x))
             (rw.ccstep-list-gather-contradictions x)))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-gather-contradictions))))

  (defthm true-listp-of-rw.ccstep-list-gather-contradictions
    (equal (true-listp (rw.ccstep-list-gather-contradictions x))
           t)
    :hints(("Goal" :induct (cdr-induction x)))))



(defsection rw.ccstep-list-list-gather-contradictions

  (defund rw.ccstep-list-list-gather-contradictions (x)
    ;; BOZO tail-recursive version?
    (declare (xargs :guard (rw.ccstep-list-listp x)))
    (if (consp x)
        (fast-app (rw.ccstep-list-gather-contradictions (car x))
                  (rw.ccstep-list-list-gather-contradictions (cdr x)))
      nil))

 (defthm rw.ccstep-list-list-gather-contradictions-when-not-consp
   (implies (not (consp x))
            (equal (rw.ccstep-list-list-gather-contradictions x)
                   nil))
   :hints(("Goal" :in-theory (enable rw.ccstep-list-list-gather-contradictions))))

 (defthm true-listp-of-rw.ccstep-list-list-gather-contradictions
   (equal (true-listp (rw.ccstep-list-list-gather-contradictions x))
          t)
   :hints(("Goal"
           :expand (rw.ccstep-list-list-gather-contradictions x)
           :induct (cdr-induction x))))

 (defthm rw.ccstep-list-list-gather-contradictions-of-cons
   (equal (rw.ccstep-list-list-gather-contradictions (cons a x))
          (app (rw.ccstep-list-gather-contradictions a)
               (rw.ccstep-list-list-gather-contradictions x)))
   :hints(("Goal" :in-theory (enable rw.ccstep-list-list-gather-contradictions)))))





(definlined rw.ccstep->provedp (x)
  ;; Did this step prove the clause?  That is, did we notice a contradictory
  ;; assms or rewrite t1 into an obviously true literal?
  (declare (xargs :guard (rw.ccstepp x)))
    (if (rw.ccstep->contradiction x)
        t
      (clause.obvious-termp (rw.trace->rhs (rw.ccstep->trace x)))))

(definlined rw.ccstep->terminalp (x)
  ;; Was this our final step?  That is, did we prove the clause, or run out
  ;; of literals to rewrite?
  (declare (xargs :guard (rw.ccstepp x)))
    (if (rw.ccstep->contradiction x)
        t
      (or (clause.obvious-termp (rw.trace->rhs (rw.ccstep->trace x)))
          (not (rw.hypbox->left (rw.ccstep->hypbox x))))))

(defthm rw.ccstep->terminalp-when-rw.ccstep->provedp
  (implies (rw.ccstep->provedp x)
           (equal (rw.ccstep->terminalp x)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep->terminalp rw.ccstep->provedp))))

(definlined rw.ccstep->original-goal (x)
  ;; What formula was this step originally intended to prove?
  (declare (xargs :guard (rw.ccstepp x)))
  (let* ((t1     (rw.ccstep->term x))
         (hypbox (rw.ccstep->hypbox x))
         (t2-tn  (rw.hypbox->left hypbox))
         (todo   (cons t1 t2-tn))
         (done   (rw.hypbox->right hypbox)))
    (if (consp done)
        (logic.por (clause.clause-formula todo)
                   (clause.clause-formula done))
      (clause.clause-formula todo))))

(definlined rw.ccstep->result-goal (x)
  ;; What will be the goal formula for the next step, after taking this one?
  ;; (We assume this step did not prove the clause.)
  (declare (xargs :guard (and (rw.ccstepp x)
                              (not (rw.ccstep->provedp x)))
                  :guard-hints (("Goal" :in-theory (enable rw.ccstep->provedp)))))
  (let* ((hypbox   (rw.ccstep->hypbox x))
         (trace    (rw.ccstep->trace x))
         (t1-prime (rw.trace->rhs trace))
         (t2-tn    (rw.hypbox->left hypbox))
         (done     (rw.hypbox->right hypbox)))
    (if (consp t2-tn)
        (logic.por (clause.clause-formula t2-tn)
                   (clause.clause-formula (cons t1-prime done)))
      (clause.clause-formula (cons t1-prime done)))))

(definlined rw.ccstep->clause-prime (x)
  ;; Given a terminal step, what is the "fully reduced clause" that remains to
  ;; be proved?
  (declare (xargs :guard (and (rw.ccstepp x)
                              ;; BOZO Trying to remove: (rw.ccstep->terminalp x)
                              )))
  (let ((hypbox        (rw.ccstep->hypbox x))
        (contradiction (rw.ccstep->contradiction x))
        (trace         (rw.ccstep->trace x)))
    (cond (contradiction
           ;; Proved it, clause-prime is empty
           nil)
          ((clause.obvious-termp (rw.trace->rhs trace))
           ;; Proved it, clause-prime is empty
           nil)
          (t
           ;; Didn't prove it, done list is just the nhyps-right.
           (cons (rw.trace->rhs trace)
                 (rw.hypbox->right hypbox))))))

(defthm booleanp-of-rw.ccsetp->provedp
  ;; BOZO misnamed
  (equal (booleanp (rw.ccstep->provedp x))
         t)
  :hints(("Goal" :in-theory (enable rw.ccstep->provedp))))

(defthm forcing-logic.term-listp-of-rw.ccstep->clause-prime
  (implies (force (rw.ccstepp x))
           (equal (logic.term-listp (rw.ccstep->clause-prime x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep->clause-prime))))

(defthm forcing-true-listp-of-rw.ccstep->clause-prime
  (implies (force (rw.ccstepp x))
           (equal (true-listp (rw.ccstep->clause-prime x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep->clause-prime))))

(defthm forcing-rw.ccstep->result-goal-when-rw.ccstep->terminalp
  (implies (and (rw.ccstep->terminalp x)
                (not (rw.ccstep->provedp x))
                (force (rw.ccstepp x)))
           (equal (rw.ccstep->result-goal x)
                  (clause.clause-formula (rw.ccstep->clause-prime x))))
  :hints(("Goal" :in-theory (enable rw.ccstep->result-goal
                                    rw.ccstep->terminalp
                                    rw.ccstep->provedp
                                    rw.ccstep->clause-prime))))

(definlined rw.ccstep->t1prime (x)
  ;; What did t1 rewrite to?  (We assume x is not a provedp step)
  (declare (xargs :guard (and (rw.ccstepp x)
                              (not (rw.ccstep->provedp x)))
                  :guard-hints (("Goal" :in-theory (enable rw.ccstep->provedp)))))
  (rw.trace->rhs (rw.ccstep->trace x)))

(defthm forcing-logic.termp-of-rw.ccstep->t1prime
  (implies (force (and (rw.ccstepp x)
                       (not (rw.ccstep->provedp x))))
           (equal (logic.termp (rw.ccstep->t1prime x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep->provedp rw.ccstep->t1prime))))

(defthm forcing-logic.term-atblp-of-rw.ccstep->t1prime
  (implies (force (rw.trace-atblp (rw.ccstep->trace x) atbl))
           (equal (logic.term-atblp (rw.ccstep->t1prime x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep->provedp rw.ccstep->t1prime))))






;; Collecting forced hyps from ccsteps
;;
;; We now introduce the simple functions to extract the forced goals out of our
;; list of ccsteps.  We have put in a little effort to make this efficient, so
;; this is slightly long due to introducing fast functions and proving
;; equivalences.  Sorry.

(defsection rw.ccstep-forced-goals

  (definlined rw.ccstep-forced-goals (x)
    (declare (xargs :guard (rw.ccstepp x)
                    :guard-hints (("Goal" :in-theory (enable rw.ccstepp)))))
    (if (rw.ccstep->contradiction x)
        nil
      (rw.collect-forced-goals (rw.ccstep->trace x))))

  (defthm true-listp-of-rw.ccstep-forced-goals
    (equal (true-listp (rw.ccstep-forced-goals x))
           t)
    :hints(("Goal" :in-theory (enable rw.ccstep-forced-goals))))

  (defthm rw.ccstep-forced-goals-when-contradiction
    (implies (rw.ccstep->contradiction x)
             (equal (rw.ccstep-forced-goals x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.ccstep-forced-goals))))

  (defthm forcing-logic.formula-listp-of-rw.ccstep-forced-goals
    (implies (force (rw.ccstepp x))
             (equal (logic.formula-listp (rw.ccstep-forced-goals x))
                    t))
    :hints(("Goal" :in-theory (enable rw.ccstep-forced-goals))))

  (defthm forcing-logic.formula-list-atblp-of-rw.ccstep-forced-goals
    (implies (force (and (rw.ccstepp x)
                         (rw.trace-atblp (rw.ccstep->trace x) atbl)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)))
             (equal (logic.formula-list-atblp (rw.ccstep-forced-goals x) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.ccstep-forced-goals)))))



(defsection rw.fast-ccstep-list-forced-goals

  (defund rw.ccstep-list-forced-goals (x)
    (declare (xargs :guard (rw.ccstep-listp x)))
    (if (consp x)
        (fast-app (rw.ccstep-forced-goals (car x))
                  (rw.ccstep-list-forced-goals (cdr x)))
      nil))

  (defthm true-listp-of-rw.crewrite-clause-step-list-forced-goals
    (equal (true-listp (rw.ccstep-list-forced-goals x))
           t)
    :hints(("Goal" :in-theory (enable rw.ccstep-list-forced-goals))))

  (defthm rw.ccstep-list-forced-goals-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list-forced-goals x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-forced-goals))))

  (defthm rw.ccstep-list-forced-goals-of-cons
    (equal (rw.ccstep-list-forced-goals (cons a x))
           (app (rw.ccstep-forced-goals a)
                (rw.ccstep-list-forced-goals x)))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-forced-goals))))

  (defthm rw.ccstep-list-forced-goals-of-list-fix
    (equal (rw.ccstep-list-forced-goals (list-fix x))
           (rw.ccstep-list-forced-goals x))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm rw.ccstep-list-forced-goals-of-app
    (equal (rw.ccstep-list-forced-goals (app x y))
           (app (rw.ccstep-list-forced-goals x)
                (rw.ccstep-list-forced-goals y)))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm logic.formula-listp-of-rw.ccstep-list-forced-goals
    (implies (force (rw.ccstep-listp x))
             (equal (logic.formula-listp (rw.ccstep-list-forced-goals x))
                    t))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm logic.formula-list-atblp-of-rw.ccstep-list-forced-goals
    (implies (force (and (rw.ccstep-listp x)
                         (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)))
             (equal (logic.formula-list-atblp (rw.ccstep-list-forced-goals x) atbl)
                    t))
    :hints(("Goal" :induct (cdr-induction x)))))




(defsection rw.ccstep-list-list-forced-goals

  (defund rw.ccstep-list-list-forced-goals (x)
    (declare (xargs :guard (rw.ccstep-list-listp x)))
    (if (consp x)
        (fast-app (rw.ccstep-list-forced-goals (car x))
                  (rw.ccstep-list-list-forced-goals (cdr x)))
      nil))

  (defthm true-listp-of-rw.ccstep-list-list-forced-goals
    (equal (true-listp (rw.ccstep-list-list-forced-goals x))
           t)
    :hints(("Goal" :in-theory (enable rw.ccstep-list-list-forced-goals))))

  (defthm rw.ccstep-list-list-forced-goals-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list-list-forced-goals x)
                    nil))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-list-forced-goals))))

  (defthm rw.ccstep-list-list-forced-goals-of-cons
    (equal (rw.ccstep-list-list-forced-goals (cons a x))
           (app (rw.ccstep-list-forced-goals a)
                (rw.ccstep-list-list-forced-goals x)))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-list-forced-goals))))

  (defthm logic.formula-listp-of-rw.ccstep-list-list-forced-goals
    (implies (force (rw.ccstep-list-listp x))
             (equal (logic.formula-listp (rw.ccstep-list-list-forced-goals x))
                    t))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm logic.formula-list-atblp-of-rw.ccstep-list-list-forced-goals
    (implies (force (and (rw.ccstep-list-listp x)
                         (rw.trace-list-atblp (rw.ccstep-list-list-gather-traces x) atbl)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)))
             (equal (logic.formula-list-atblp (rw.ccstep-list-list-forced-goals x) atbl)
                    t))
    :hints(("Goal"
            :induct (cdr-induction x)))))




(defderiv rw.ccstep-lemma-1
  :derive (v (v (!= (? t1) nil) L) R)
  :from   ((proof x (v L (v (!= (? t2) nil) R)))
           (proof y (v (v L R) (= (iff (? t1) (? t2)) t))))
  :proof  (@derive
           ((v L (v (!= (? t2) nil) R))            (@given x))
           ((v L (v R (!= (? t2) nil)))            (build.disjoined-commute-or @-))
           ((v (v L R) (!= (? t2) nil))            (build.associativity @-))
           ((v (v L R) (= (iff (? t1) (? t2)) t))  (@given y))
           ((v (v L R) (!= (? t1) nil))            (clause.disjoined-substitute-iff-into-literal-bldr @-- @-))
           ((v (!= (? t1) nil) (v L R))            (build.commute-or @-))
           ((v (v (!= (? t1) nil) L) R)            (build.associativity @-))))

(defderiv rw.ccstep-lemma-2
  :derive (v (!= (? t1) nil) L)
  :from   ((proof x (v L (!= (? t2) nil)))
           (proof y (v L (= (iff (? t1) (? t2)) t))))
  :proof  (@derive
           ((v L (!= (? t2) nil))             (@given x))
           ((v L (= (iff (? t1) (? t2)) t))   (@given y))
           ((v L (!= (? t1) nil))             (clause.disjoined-substitute-iff-into-literal-bldr @-- @-))
           ((v (!= (? t1) nil) L)             (build.commute-or @-))))

(defderiv rw.ccstep-lemma-3
  :derive (v (!= (? t1) nil) R)
  :from   ((proof x (v (!= (? t2) nil) R))
           (proof y (v R (= (iff (? t1) (? t2)) t))))
  :proof  (@derive
           ((v (!= (? t2) nil) R)              (@given x))
           ((v R (!= (? t2) nil))              (build.commute-or @-))
           ((v R (= (iff (? t1) (? t2)) t))    (@given y))
           ((v R (!= (? t1) nil))              (clause.disjoined-substitute-iff-into-literal-bldr @-- @-))
           ((v (!= (? t1) nil) R)              (build.commute-or @-))))

(defderiv rw.ccstep-lemma-4
  :derive (v (!= (? t1) nil) P)
  :from   ((proof x (!= (? t2) nil))
           (proof y (v P (= (iff (? t1) (? t2)) t))))
  :proof  (@derive
           ((!= (? t2) nil)                   (@given x))
           ((v P (!= (? t2) nil))             (build.expansion (@formula P) @-))
           ((v P (= (iff (? t1) (? t2)) t))   (@given y))
           ((v P (!= (? t1) nil))             (clause.disjoined-substitute-iff-into-literal-bldr @-- @-))
           ((v (!= (? t1) nil) P)             (build.commute-or @-))))



(defsection rw.proved-ccstep-bldr

  (defund@ rw.proved-ccstep-bldr (x defs fproofs)
    ;; Prove the step's original goal, given a proof of its result goal if necessary.
    (declare (xargs :guard (and (rw.ccstepp x)
                                (rw.ccstep->provedp x)
                                (definition-listp defs)
                                (or (rw.ccstep->contradiction x)
                                    (rw.trace-okp (rw.ccstep->trace x) defs))
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs)))
                    :verify-guards nil))
    (let* ((t1            (rw.ccstep->term x))
           (hypbox        (rw.ccstep->hypbox x))
           (contradiction (rw.ccstep->contradiction x))
           (trace         (rw.ccstep->trace x))
           (left          (rw.hypbox->left hypbox))
           (right         (rw.hypbox->right hypbox)))
      (if contradiction
          ;; Note: at least one of left or right must be a consp.
          (if (and (consp left) (consp right))
              (@derive
               ((v L R)                       (rw.eqtrace-contradiction-bldr contradiction hypbox))
               ((v (!= t1 nil) (v L R))       (build.expansion (logic.term-formula t1) @-))
               ((v (v (!= t1 nil) L) R)       (build.associativity @-)))
            (@derive
             (LR                              (rw.eqtrace-contradiction-bldr contradiction hypbox))
             ((v (!= t1 nil) LR)              (build.expansion (logic.term-formula t1) @-))))
        (if (or (consp left)
                (consp right))
            (let ((lemma (rw.ccstep-lemma-4 (clause.obvious-term-bldr (rw.trace->rhs trace))
                                            (rw.compile-trace trace defs fproofs))))
              (if (and (consp left)
                       (consp right))
                  ;; Lemma is t1 != nil v (Left v Right)
                  (build.associativity lemma)
                ;; Lemma is t1 != nil v [Left | Right]
                lemma))
          ;; Else there are no assms.
          (@derive ((!= t1-prime nil)                         (clause.obvious-term-bldr (rw.trace->rhs trace)))
                   ((= (iff t1 t1-prime) t)                   (rw.compile-trace trace defs fproofs))
                   ((!= t1 nil)                               (clause.substitute-iff-into-literal-bldr @-- @-)))))))

  (defobligations rw.proved-ccstep-bldr
    (rw.eqtrace-contradiction-bldr
     clause.obvious-term-bldr
     rw.compile-trace
     clause.substitute-iff-into-literal-bldr))

  (local (in-theory (enable rw.proved-ccstep-bldr
                            rw.ccstep->result-goal
                            rw.ccstep->provedp
                            rw.ccstep->original-goal
                            rw.ccstep-forced-goals
                            rw.hypbox-formula
                            logic.term-formula
                            rw.trace-formula
                            rw.trace-conclusion-formula)))

  (defthm rw.proved-ccstep-bldr-under-iff
    (iff (rw.proved-ccstep-bldr x defs fproofs)
         t)
    :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

  (defthm forcing-logic.appealp-of-rw.proved-ccstep-bldr
    (implies (force (and (rw.ccstepp x)
                         (rw.ccstep->provedp x)
                         (definition-listp defs)
                         (or (rw.ccstep->contradiction x)
                             (rw.trace-okp (rw.ccstep->trace x) defs))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.appealp (rw.proved-ccstep-bldr x defs fproofs))
                    t)))

  (defthm forcing-logic.conclusion-of-rw.proved-ccstep-bldr
    (implies (force (and (rw.ccstepp x)
                         (rw.ccstep->provedp x)
                         (definition-listp defs)
                         (or (rw.ccstep->contradiction x)
                             (rw.trace-okp (rw.ccstep->trace x) defs))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.conclusion (rw.proved-ccstep-bldr x defs fproofs))
                    (rw.ccstep->original-goal x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm@ forcing-logic.proofp-of-rw.proved-ccstep-bldr
    (implies (force (and (rw.ccstepp x)
                         (rw.ccstep->provedp x)
                         (definition-listp defs)
                         (if (rw.ccstep->contradiction x)
                             (rw.eqtrace-atblp (rw.ccstep->contradiction x) atbl)
                           (and (rw.trace-okp (rw.ccstep->trace x) defs)
                                (rw.trace-atblp (rw.ccstep->trace x) atbl)
                                (rw.trace-env-okp (rw.ccstep->trace x) defs thms atbl)))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))
                         ;; ---
                         (logic.term-atblp (rw.ccstep->term x) atbl)
                         (rw.hypbox-atblp (rw.ccstep->hypbox x) atbl)
                         (logic.proof-listp fproofs axioms thms atbl)
                         (logic.formula-list-atblp defs atbl)
                         (subsetp defs axioms)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (@obligations rw.proved-ccstep-bldr)))
             (equal (logic.proofp (rw.proved-ccstep-bldr x defs fproofs) axioms thms atbl)
                    t)))

  (verify-guards rw.proved-ccstep-bldr))




(defsection rw.usual-ccstep-bldr

  (defund@ rw.usual-ccstep-bldr (x defs proof fproofs)
    ;; Prove the step's original goal, given a proof of its result goal if necessary.
    (declare (xargs :guard (and (rw.ccstepp x)
                                (not (rw.ccstep->provedp x))
                                (definition-listp defs)
                                (rw.trace-okp (rw.ccstep->trace x) defs)
                                (logic.appealp proof)
                                (equal (logic.conclusion proof) (rw.ccstep->result-goal x))
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs)))
                    :verify-guards nil))
    (let* ((hypbox        (rw.ccstep->hypbox x))
           (trace         (rw.ccstep->trace x))
           (left          (rw.hypbox->left hypbox))
           (right         (rw.hypbox->right hypbox)))
      (cond ((and (consp left) (consp right))
             (rw.ccstep-lemma-1 proof (rw.compile-trace trace defs fproofs)))
            ((consp left)
             (rw.ccstep-lemma-2 proof (rw.compile-trace trace defs fproofs)))
            ((consp right)
             (rw.ccstep-lemma-3 proof (rw.compile-trace trace defs fproofs)))
            (t
             (@derive ((!= t1-prime nil)                    (@given proof))
                      ((= (iff t1 t1-prime) t)              (rw.compile-trace trace defs fproofs))
                      ((!= t1 nil)                          (clause.substitute-iff-into-literal-bldr @-- @-)))))))

  (defobligations rw.usual-ccstep-bldr
    (rw.compile-trace
     clause.substitute-iff-into-literal-bldr))

  (local (in-theory (enable rw.usual-ccstep-bldr
                            rw.ccstep->result-goal
                            rw.ccstep->provedp
                            rw.ccstep->original-goal
                            rw.ccstep-forced-goals
                            rw.hypbox-formula
                            logic.term-formula
                            rw.trace-formula
                            rw.trace-conclusion-formula)))

  (defthm rw.usual-ccstep-bldr-under-iff
    (iff (rw.usual-ccstep-bldr x defs proof fproofs)
         t)
    :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

  (defthm forcing-logic.appealp-of-rw.usual-ccstep-bldr
    (implies (force (and (rw.ccstepp x)
                         (definition-listp defs)
                         (not (rw.ccstep->provedp x))
                         (rw.trace-okp (rw.ccstep->trace x) defs)
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal x))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.appealp (rw.usual-ccstep-bldr x defs proof fproofs))
                    t)))

  (defthm forcing-logic.conclusion-of-rw.usual-ccstep-bldr
    (implies (force (and (rw.ccstepp x)
                         (definition-listp defs)
                         (not (rw.ccstep->provedp x))
                         (rw.trace-okp (rw.ccstep->trace x) defs)
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal x))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.conclusion (rw.usual-ccstep-bldr x defs proof fproofs))
                    (rw.ccstep->original-goal x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm@ forcing-logic.proofp-of-rw.usual-ccstep-bldr
    (implies (force (and (rw.ccstepp x)
                         (definition-listp defs)
                         (not (rw.ccstep->provedp x))
                         (rw.trace-okp (rw.ccstep->trace x) defs)
                         (rw.trace-okp (rw.ccstep->trace x) defs)
                         (rw.trace-atblp (rw.ccstep->trace x) atbl)
                         (rw.trace-env-okp (rw.ccstep->trace x) defs thms atbl)
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal x))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal x))
                         (logic.proofp proof axioms thms atbl)
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-forced-goals x) (logic.strip-conclusions fproofs))
                         ;; ---
                         (logic.term-atblp (rw.ccstep->term x) atbl)
                         (rw.hypbox-atblp (rw.ccstep->hypbox x) atbl)
                         (logic.proof-listp fproofs axioms thms atbl)
                         (logic.formula-list-atblp defs atbl)
                         (subsetp defs axioms)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (@obligations rw.usual-ccstep-bldr)))
             (equal (logic.proofp (rw.usual-ccstep-bldr x defs proof fproofs) axioms thms atbl)
                    t)))

  (verify-guards rw.usual-ccstep-bldr))




(defund rw.ccstep-list->original-goal (x)
  ;; We say the original goal for a list of steps is the original goal of the
  ;; final step.
  (declare (xargs :guard (and (consp x)
                              (rw.ccstep-listp x))))
  (if (and (consp x)
           (consp (cdr x)))
      (rw.ccstep-list->original-goal (cdr x))
    (rw.ccstep->original-goal (car x))))



(defsection rw.ccstep-list->none-provedp

  (defund rw.ccstep-list->none-provedp (x)
    (declare (xargs :guard (rw.ccstep-listp x)))
    (if (consp x)
        (and (not (rw.ccstep->provedp (car x)))
             (rw.ccstep-list->none-provedp (cdr x)))
      t))

  (defthm rw.ccstep-list->none-provedp-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list->none-provedp x)
                    t))
    :hints(("Goal" :in-theory (enable rw.ccstep-list->none-provedp))))

  (defthm rw.ccstep-list->none-provedp-of-cons
    (equal (rw.ccstep-list->none-provedp (cons a x))
           (and (not (rw.ccstep->provedp a))
                (rw.ccstep-list->none-provedp x)))
    :hints(("Goal" :in-theory (enable rw.ccstep-list->none-provedp))))

  (defthm booleanp-of-rw.ccstep-list->none-provedp
    (equal (booleanp (rw.ccstep-list->none-provedp x))
           t)
    :hints(("Goal" :induct (cdr-induction x)))))



(defsection rw.ccstep-list->compatiblep

  (defund rw.ccstep-list->compatiblep (x)
    (declare (xargs :guard (rw.ccstep-listp x)))
    (if (and (consp x)
             (consp (cdr x)))
        (and (not (rw.ccstep->provedp (second x)))
             (equal (rw.ccstep->original-goal (first x))
                    (rw.ccstep->result-goal (second x)))
             (rw.ccstep-list->compatiblep (cdr x)))
      t))

  (local (in-theory (enable rw.ccstep-list->compatiblep)))

  (defthm booleanp-of-rw.ccstep-list->compatiblep
    (equal (booleanp (rw.ccstep-list->compatiblep x))
           t))

  (defthm rw.ccstep-list->compatiblep-when-not-consp
    (implies (not (consp x))
             (equal (rw.ccstep-list->compatiblep x)
                    t)))

  (defthm rw.ccstep-list->compatiblep-when-not-of-cdr
    (implies (not (consp (cdr x)))
             (equal (rw.ccstep-list->compatiblep x)
                    t))))



(defsection rw.usual-ccstep-list-bldr

  (defund rw.usual-ccstep-list-bldr (x defs proof fproofs)
    (declare (xargs :guard (and (consp x)
                                (rw.ccstep-listp x)
                                (rw.ccstep-list->none-provedp x)
                                (rw.ccstep-list->compatiblep x)
                                (definition-listp defs)
                                (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                                (logic.appealp proof)
                                (equal (logic.conclusion proof) (rw.ccstep->result-goal (first x)))
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs)))
                    :verify-guards nil))
    (if (and (consp x)
             (consp (cdr x)))
        (rw.usual-ccstep-list-bldr (cdr x)
                                   defs
                                   (rw.usual-ccstep-bldr (car x) defs proof fproofs)
                                   fproofs)
      (rw.usual-ccstep-bldr (car x) defs proof fproofs)))

  (defobligations rw.usual-ccstep-list-bldr
    (rw.usual-ccstep-bldr))

  (local (in-theory (enable rw.usual-ccstep-list-bldr
                            rw.ccstep->provedp
                            rw.ccstep-list->compatiblep
                            rw.ccstep-list->original-goal)))

  (defthm forcing-logic.appealp-of-rw.usual-ccstep-list-bldr
    (implies (force (and (consp x)
                         (rw.ccstep-listp x)
                         (rw.ccstep-list->none-provedp x)
                         (rw.ccstep-list->compatiblep x)
                         (definition-listp defs)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal (first x)))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.appealp (rw.usual-ccstep-list-bldr x defs proof fproofs))
                    t)))

  (defthm forcing-logic.conclusion-of-rw.usual-ccstep-list-bldr
    (implies (force (and (consp x)
                         (rw.ccstep-listp x)
                         (rw.ccstep-list->none-provedp x)
                         (rw.ccstep-list->compatiblep x)
                         (definition-listp defs)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal (first x)))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.conclusion (rw.usual-ccstep-list-bldr x defs proof fproofs))
                    (rw.ccstep-list->original-goal x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm@ forcing-logic.proofp-of-rw.usual-ccstep-list-bldr
    (implies (force (and (consp x)
                         (rw.ccstep-listp x)
                         (rw.ccstep-list->none-provedp x)
                         (rw.ccstep-list->compatiblep x)
                         (definition-listp defs)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                         (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl)
                         (rw.trace-list-env-okp (rw.ccstep-list-gather-traces x) defs thms atbl)
                         (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal (first x)))
                         (logic.proofp proof axioms thms atbl)
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))
                         ;; ---
                         (logic.term-list-atblp (rw.ccstep-list-terms x) atbl)
                         (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes x) atbl)
                         (logic.proof-listp fproofs axioms thms atbl)
                         (logic.formula-list-atblp defs atbl)
                         (subsetp defs axioms)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (@obligations rw.usual-ccstep-list-bldr)))
             (equal (logic.proofp (rw.usual-ccstep-list-bldr x defs proof fproofs) axioms thms atbl)
                    t)))

  (verify-guards rw.usual-ccstep-list-bldr))



(defsection rw.ccstep-list-bldr

  (defund rw.ccstep-list-bldr (x defs proof fproofs)
    (declare (xargs :guard (and (consp x)
                                (rw.ccstep-listp x)
                                (rw.ccstep-list->compatiblep x)
                                (definition-listp defs)
                                (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                                (if (rw.ccstep->provedp (first x))
                                    (not proof)
                                  (and (logic.appealp proof)
                                       (equal (logic.conclusion proof)
                                              (rw.ccstep->result-goal (first x)))))
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs)))
                    :verify-guards nil))
    (if (rw.ccstep->provedp (first x))
        (if (consp (cdr x))
            (rw.usual-ccstep-list-bldr (cdr x)
                                       defs
                                       (rw.proved-ccstep-bldr (first x) defs fproofs)
                                       fproofs)
          (rw.proved-ccstep-bldr (first x) defs fproofs))
      (rw.usual-ccstep-list-bldr x defs proof fproofs)))

  (defobligations rw.ccstep-list-bldr
    (rw.proved-ccstep-bldr
     rw.usual-ccstep-list-bldr))

  (local (in-theory (enable rw.ccstep-list-bldr
                            rw.ccstep-list->compatiblep
                            rw.ccstep-list->original-goal)))

  (defthmd lemma-1-for-rw.ccstep-list-bldr
    (implies (rw.ccstep-list->compatiblep x)
             (equal (rw.ccstep-list->none-provedp (cdr x))
                    t)))

  (defthmd lemma-2-for-rw.ccstep-list-bldr
    (implies (rw.ccstep-list->compatiblep x)
             (equal (rw.ccstep-list->none-provedp x)
                    (if (consp x)
                        (not (rw.ccstep->provedp (car x)))
                      t)))
    :hints(("goal"
            :in-theory (disable rw.ccstep-list->compatiblep)
            :use ((:instance lemma-1-for-rw.ccstep-list-bldr)))))

  (local (in-theory (enable lemma-2-for-rw.ccstep-list-bldr)))

  (defthm forcing-logic.appealp-of-rw.ccstep-list-bldr
    (implies (force (and (consp x)
                         (rw.ccstep-listp x)
                         (rw.ccstep-list->compatiblep x)
                         (definition-listp defs)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                         (if (rw.ccstep->provedp (first x))
                             (not proof)
                           (and (logic.appealp proof)
                                (equal (logic.conclusion proof)
                                       (rw.ccstep->result-goal (first x)))))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.appealp (rw.ccstep-list-bldr x defs proof fproofs))
                    t)))

  (defthm forcing-logic.conclusion-of-rw.ccstep-list-bldr
    (implies (force (and (consp x)
                         (rw.ccstep-listp x)
                         (rw.ccstep-list->compatiblep x)
                         (definition-listp defs)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                         (if (rw.ccstep->provedp (first x))
                             (not proof)
                           (and (logic.appealp proof)
                                (equal (logic.conclusion proof)
                                       (rw.ccstep->result-goal (first x)))))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))))
             (equal (logic.conclusion (rw.ccstep-list-bldr x defs proof fproofs))
                    (rw.ccstep-list->original-goal x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm@ forcing-logic.proofp-of-rw.ccstep-list-bldr
    (implies (force (and (consp x)
                         (rw.ccstep-listp x)
                         (rw.ccstep-list->compatiblep x)
                         (definition-listp defs)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                         (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl)
                         (rw.trace-list-env-okp (rw.ccstep-list-gather-traces x) defs thms atbl)
                         (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions x) atbl)
                         (if (rw.ccstep->provedp (first x))
                             (not proof)
                           (and (logic.appealp proof)
                                (equal (logic.conclusion proof)
                                       (rw.ccstep->result-goal (first x)))
                                (logic.proofp proof axioms thms atbl)))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))
                         ;; ---
                         (logic.term-list-atblp (rw.ccstep-list-terms x) atbl)
                         (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes x) atbl)
                         (logic.proof-listp fproofs axioms thms atbl)
                         (logic.formula-list-atblp defs atbl)
                         (subsetp defs axioms)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (@obligations rw.ccstep-list-bldr)))
             (equal (logic.proofp (rw.ccstep-list-bldr x defs proof fproofs) axioms thms atbl)
                    t)))

  (verify-guards rw.ccstep-list-bldr))

