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




; BOZO find these things a home.

(defthm true-list-listp-of-remove-supersets1
  (implies (and (true-list-listp acc)
                (true-list-listp x))
           (equal (true-list-listp (remove-supersets1 x acc))
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm true-list-listp-of-remove-supersets
  (implies (force (true-list-listp x))
           (equal (true-list-listp (remove-supersets x))
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets))))

(defthm true-list-listp-of-remove-duplicates-list
  (equal (true-list-listp (remove-duplicates-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-list-listp-of-third-of-clause.clean-clauses
  (implies (force (true-list-listp x))
           (equal (true-list-listp (third (clause.clean-clauses x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.clean-clauses))))

(defthm true-list-listp-of-third-of-clause.fast-clean-clauses
  (implies (force (true-list-listp x))
           (equal (true-list-listp (third (clause.fast-clean-clauses x)))
                  t))
  :hints(("Goal" :in-theory (e/d (clause.fast-clean-clauses)
                                 (clause.fast-clean-clauses-removal
                                  clause.fast-clean-part1-removal)))))

(defthm true-list-listp-of-revappend
  (implies (and (force (true-list-listp x))
                (force (true-list-listp acc)))
           (true-list-listp (revappend x acc)))
  :hints(("Goal" :in-theory (e/d (revappend)
                                 (forcing-revappend-removal)))))

(defthm true-list-listp-of-clause.aux-split
  (implies (and (true-listp todo)
                (true-listp done))
           (true-list-listp (clause.aux-split todo done)))
  :hints(("Goal" :in-theory (enable clause.aux-split))))

(defthm true-list-listp-of-clause.aux-limsplit
  (implies (and (true-listp todo)
                (true-listp done))
           (true-list-listp (clause.aux-limsplit todo done splitlimit)))
  :hints(("Goal" :in-theory (enable clause.aux-limsplit))))

(defthm true-list-listp-of-clause.simple-limsplit
  (implies (true-listp x)
           (equal (true-list-listp (clause.simple-limsplit x splitlimit))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-limsplit))))

(defthm true-list-listp-of-clause.simple-split
  (implies (true-listp x)
           (equal (true-list-listp (clause.simple-split x))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-split))))

(defthm true-list-listp-of-cdr-of-clause.split
  (implies (force (true-listp x))
           (equal (true-list-listp (cdr (clause.split liftp liftlimit splitlimit x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.split))))


(defthm logic.formula-listp-of-remove-duplicates-free
  (implies (and (equal x (remove-duplicates y))
                (logic.formula-listp y))
           (equal (logic.formula-listp x)
                  t)))

(defthm logic.formula-list-atblp-of-remove-duplicates-free
  (implies (and (equal x (remove-duplicates y))
                (logic.formula-list-atblp y atbl))
           (equal (logic.formula-list-atblp x atbl)
                  t)))

(defthm subsetp-of-remove-duplicates-one-indirect
  (implies (equal (remove-duplicates x) y)
           (equal (subsetp x y)
                  t))
  ;; Yikes, this rule is really expensive!
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm cons-listp-of-list-list-fix
  (equal (cons-listp (list-list-fix x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-list-listp-of-list-list-fix
  (equal (true-list-listp (list-list-fix x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-listp-of-list-list-fix
  (equal (logic.term-list-listp (list-list-fix x))
         (logic.term-list-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm list-list-fix-when-true-list-listp
  (implies (true-list-listp x)
           (equal (list-list-fix x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-list-atblp-of-list-list-fix
  (equal (logic.term-list-list-atblp (list-list-fix x) atbl)
         (logic.term-list-list-atblp x atbl))
  :hints(("Goal" :induct (cdr-induction x))))



; THE WATERFALL
;
; The waterfall here is named after ACL2's waterfall, although it is extemely
; limited in comparison.  The tactic system we have introduced is ordinarily
; used in a basically "breadth first" way, where some proof strategy is applied
; to every goal, producing a new list of goals, and then some other strategy is
; applied.  See, for instance, the %auto tactic.  By comparison, the waterfall
; is a "depth first" operation which, upon simplifying some goal clause,
; immediately begins working to simplify the subgoals which were just produced.
;
; The breadth-first approach is often sufficient, especially since generally
; our techniques will gracefully fail when no progress can be made.  That is,
; it does not hurt to apply "split" to a fully-split goal, because it just
; becomes a no-op.  On the other hand, this simplicity sometimes comes at a
; high performance cost when just a few goals are very complicated and other
; goals are simple.  One must continually revisit the simple goals instead of
; focusing on the main, challenging goals.  In such cases the waterfall can
; sometimes perform much better.
;
; To justify the waterfall, we build a record of what has occurred to the goal.
; Waterfall steps are somewhat similar to tactic skeletons, except that the
; depth-first nature of the waterfall makes things more difficult.  In
; particular, we are building a tree rather than a linear structure.
;
; Every node in this tree is a waterfall step.  Each such step is an aggreate
; which includes
;
;   - METHOD is which one is being used
;   - CLAUSE is the clause being proven
;   - EXTRAS are any extra info we need
;   - SUBSTEPS, steps for the subgoals which are introduced by method
;
; This structure is straightforward and is easy to compile into proofs.  The
; difficulty comes in creating such structures, where we need to recursively
; build the substeps and then stuff them into the step we are producing.  None
; of this is particularly bad, it just makes rw.flag-waterfall more complex.
;
; We begin with the usual drivel needed to introduce a structure, accessors,
; etc.

(defund rw.flag-waterstepp (flag x)
  (declare (xargs :guard t))
  (if (equal flag 'clause)
      (let ((method   (car (car x)))
            (clause   (cdr (car x)))
            ;(extras   (car (cdr x)))
            (substeps (cdr (cdr x))))
        (and (symbolp method)
             (logic.term-listp clause)
             (consp clause)
             (true-listp clause)
             (rw.flag-waterstepp 'list substeps)))
    (if (consp x)
        (and (rw.flag-waterstepp 'clause (car x))
             (rw.flag-waterstepp 'list (cdr x)))
      t)))

(defund rw.waterstepp (x)
  (declare (xargs :guard t))
  (rw.flag-waterstepp 'clause x))

(defund rw.waterstep-listp (x)
  (declare (xargs :guard t))
  (rw.flag-waterstepp 'list x))

(defthmd definition-of-rw.waterstepp
  (equal (rw.waterstepp x)
         (let ((method   (car (car x)))
               (clause   (cdr (car x)))
               ;(extras  (car (cdr x))))
               (substeps (cdr (cdr x))))
           (and (symbolp method)
                (logic.term-listp clause)
                (consp clause)
                (true-listp clause)
                (rw.waterstep-listp substeps))))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstepp rw.waterstep-listp)
          :expand ((rw.flag-waterstepp 'clause x)))))

(defthmd definition-of-rw.waterstep-listp
  (equal (rw.waterstep-listp x)
         (if (consp x)
             (and (rw.waterstepp (car x))
                  (rw.waterstep-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstepp rw.waterstep-listp)
          :expand ((rw.flag-waterstepp 'list x)))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstepp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-listp))))

(defthm rw.waterstep-listp-when-not-consp
  (implies (not (consp x))
           (equal (rw.waterstep-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-listp))))

(defthm rw.waterstep-listp-of-cons
  (equal (rw.waterstep-listp (cons a x))
         (and (rw.waterstepp a)
              (rw.waterstep-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-listp))))

(defun rw.raw-waterstep-induction (flag x)
  (declare (xargs :verify-guards nil
                  :measure (two-nats-measure (rank x) (if (equal flag 'clause) 1 0))))
  (if (equal flag 'clause)
      (rw.raw-waterstep-induction 'list (cdr (cdr x)))
    (if (consp x)
        (list (rw.raw-waterstep-induction 'clause (car x))
              (rw.raw-waterstep-induction 'list (cdr x)))
      nil)))

(defthms-flag
  :thms ((clause booleanp-of-rw.waterstepp
                 (equal (booleanp (rw.waterstepp x))
                        t))
         (t booleanp-of-rw.waterstep-listp
            (equal (booleanp (rw.waterstep-listp x))
                   t)))
  :hints (("Goal"
           :in-theory (enable definition-of-rw.waterstepp)
           :induct (rw.raw-waterstep-induction flag x))))

(deflist rw.waterstep-listp (x)
  (rw.waterstepp x)
  :elementp-of-nil nil
  :already-definedp t)



(defund rw.waterstep (method clause extras substeps)
  (declare (xargs :guard (and (symbolp method)
                              (logic.term-listp clause)
                              (consp clause)
                              (rw.waterstep-listp substeps))))
  (cons (cons method clause)
        (cons extras substeps)))

(defund rw.waterstep->method (x)
  (declare (xargs :guard (rw.waterstepp x)))
  (car (car x)))

(defund rw.waterstep->clause (x)
  (declare (xargs :guard (rw.waterstepp x)))
  (cdr (car x)))

(defund rw.waterstep->extras (x)
  (declare (xargs :guard (rw.waterstepp x)))
  (car (cdr x)))

(defund rw.waterstep->substeps (x)
  (declare (xargs :guard (rw.waterstepp x)))
  (cdr (cdr x)))

(defthm rw.waterstep->method-of-rw.waterstep
  (equal (rw.waterstep->method (rw.waterstep method clause extras substeps))
         method)
  :hints(("Goal" :in-theory (enable rw.waterstep rw.waterstep->method))))

(defthm rw.waterstep->clause-of-rw.waterstep
  (equal (rw.waterstep->clause (rw.waterstep method clause extras substeps))
         clause)
  :hints(("Goal" :in-theory (enable rw.waterstep rw.waterstep->clause))))

(defthm rw.waterstep->extras-of-rw.waterstep
  (equal (rw.waterstep->extras (rw.waterstep method clause extras substeps))
         extras)
  :hints(("Goal" :in-theory (enable rw.waterstep rw.waterstep->extras))))

(defthm rw.waterstep->substeps-of-rw.waterstep
  (equal (rw.waterstep->substeps (rw.waterstep method clause extras substeps))
         substeps)
  :hints(("Goal" :in-theory (enable rw.waterstep rw.waterstep->substeps))))

(defthm rank-of-rw.waterstep->substeps
  (equal (< (rank x) (rank (rw.waterstep->substeps x)))
         nil)
  :hints(("Goal" :in-theory (enable rw.waterstep->substeps))))

(defthm rw.waterstepp-of-rw.waterstep
  (implies (and (force (symbolp method))
                (force (logic.term-listp clause))
                (force (consp clause))
                (force (true-listp clause))
                (force (rw.waterstep-listp substeps)))
           (rw.waterstepp (rw.waterstep method clause extras substeps)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstepp rw.waterstep))))

(defthm symbolp-of-rw.waterstep->method
  (implies (force (rw.waterstepp x))
           (equal (symbolp (rw.waterstep->method x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstepp
                                    rw.waterstep->method))))

(defthm logic.term-listp-of-rw.waterstep->clause
  (implies (force (rw.waterstepp x))
           (equal (logic.term-listp (rw.waterstep->clause x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstepp
                                    rw.waterstep->clause))))

(defthm consp-of-rw.waterstep->clause
  (implies (force (rw.waterstepp x))
           (equal (consp (rw.waterstep->clause x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstepp
                                    rw.waterstep->clause))))

(defthm true-listp-of-rw.waterstep->clause
  (implies (force (rw.waterstepp x))
           (equal (true-listp (rw.waterstep->clause x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstepp
                                    rw.waterstep->clause))))

(defthm rw.waterstep-listp-of-rw.waterstep->substeps
  (implies (force (rw.waterstepp x))
           (equal (rw.waterstep-listp (rw.waterstep->substeps x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstepp
                                    rw.waterstep->substeps))))


(defprojection
  :list (rw.waterstep-list->clauses x)
  :element (rw.waterstep->clause x)
  :guard (rw.waterstep-listp x)
  :nil-preservingp t)

(defthm cons-listp-of-rw.waterstep-list->clauses
  (implies (force (rw.waterstep-listp x))
           (equal (cons-listp (rw.waterstep-list->clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-list-listp-of-rw.waterstep-list->clauses
  (implies (force (rw.waterstep-listp x))
           (equal (true-list-listp (rw.waterstep-list->clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-listp-of-rw.waterstep-list->clauses
  (implies (force (rw.waterstep-listp x))
           (equal (logic.term-list-listp (rw.waterstep-list->clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(defun rw.waterstep-induction (flag x)
  (declare (xargs :measure (two-nats-measure (rank x) (if (equal flag 'clause) 1 0))
                  :verify-guards nil))
  (if (equal flag 'clause)
      (rw.waterstep-induction 'list (rw.waterstep->substeps x))
    (if (consp x)
        (list (rw.waterstep-induction 'clause (car x))
              (rw.waterstep-induction 'list (cdr x)))
      t)))






(defun rw.flag-waterstep-atblp (flag x atbl)
  (declare (xargs :guard (and (if (equal flag 'clause)
                                  (rw.waterstepp x)
                                (rw.waterstep-listp x))
                              (logic.arity-tablep atbl))
                  :measure (two-nats-measure (rank x) (if (equal flag 'clause) 1 0))))

; We walk through the waterfall steps, collecting the clause for each STOP
; step.  These are the clauses that still need to be proven before we can
; compile this waterfall step into a real proof.

  (if (equal flag 'clause)
      (and (logic.term-list-atblp (rw.waterstep->clause x) atbl)
           (rw.flag-waterstep-atblp 'list (rw.waterstep->substeps x) atbl))
    (if (consp x)
        (and (rw.flag-waterstep-atblp 'clause (car x) atbl)
             (rw.flag-waterstep-atblp 'list (cdr x) atbl))
      t)))

(defund rw.waterstep-atblp (x atbl)
  (declare (xargs :guard (and (rw.waterstepp x)
                              (logic.arity-tablep atbl))))
  (rw.flag-waterstep-atblp 'clause x atbl))

(defund rw.waterstep-list-atblp (x atbl)
  (declare (xargs :guard (and (rw.waterstep-listp x)
                              (logic.arity-tablep atbl))))
  (rw.flag-waterstep-atblp 'list x atbl))

(defthmd definition-of-rw.waterstep-atblp
  (equal (rw.waterstep-atblp x atbl)
         (and (logic.term-list-atblp (rw.waterstep->clause x) atbl)
              (rw.waterstep-list-atblp (rw.waterstep->substeps x) atbl)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstep-atblp rw.waterstep-list-atblp)
          :expand ((rw.flag-waterstep-atblp 'clause x atbl)))))

(defthmd definition-of-rw.waterstep-list-atblp
  (equal (rw.waterstep-list-atblp x atbl)
         (if (consp x)
             (and (rw.waterstep-atblp (car x) atbl)
                  (rw.waterstep-list-atblp (cdr x) atbl))
           t))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstep-atblp rw.waterstep-list-atblp)
          :expand ((rw.flag-waterstep-atblp 'list x atbl)))))

(defthm rw.flag-waterstep-atblp-of-clause
  (equal (rw.flag-waterstep-atblp 'clause x atbl)
         (rw.waterstep-atblp x atbl))
  :hints(("Goal" :in-theory (enable rw.waterstep-atblp))))

(defthm rw.flag-waterstep-list-atblp-of-clause
  (equal (rw.flag-waterstep-atblp 'list x atbl)
         (rw.waterstep-list-atblp x atbl))
  :hints(("Goal" :in-theory (enable rw.waterstep-list-atblp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-atblp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-list-atblp))))

(defthm rw.waterstep-list-atblp-when-not-consp
  (implies (not (consp x))
           (equal (rw.waterstep-list-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-list-atblp))))

(defthm rw.waterstep-list-atblp-of-cons
  (equal (rw.waterstep-list-atblp (cons a x) atbl)
         (and (rw.waterstep-atblp a atbl)
              (rw.waterstep-list-atblp x atbl)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-list-atblp))))

(defthm rw.waterstep-atblp-of-nil
  (equal (rw.waterstep-atblp nil atbl)
         t)
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-atblp))))

(defthms-flag
  :thms ((clause booleanp-of-rw.waterstep-atblp
                 (equal (booleanp (rw.waterstep-atblp x atbl))
                        t))
         (t booleanp-of-rw.waterstep-list-atblp
            (equal (booleanp (rw.waterstep-list-atblp x atbl))
                   t)))
  :hints(("Goal"
          :induct (rw.waterstep-induction flag x)
          :in-theory (enable definition-of-rw.waterstep-atblp))))

(deflist rw.waterstep-list-atblp (x atbl)
  (rw.waterstep-atblp x atbl)
  :guard (and (rw.waterstep-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil t
  :already-definedp t)

(defthm logic.term-list-atblp-of-rw.waterstep->clause
  (implies (force (rw.waterstep-atblp x atbl))
           (equal (logic.term-list-atblp (rw.waterstep->clause x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-atblp))))

(defthm rw.waterstep-list-atblp-of-rw.waterstep->substeps
  (implies (force (rw.waterstep-atblp x atbl))
           (equal (rw.waterstep-list-atblp (rw.waterstep->substeps x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-atblp))))

(defthm rw.waterstep-atblp-of-rw.waterstep
  (implies (force (and (logic.term-list-atblp clause atbl)
                       (rw.waterstep-list-atblp substeps atbl)))
           (equal (rw.waterstep-atblp (rw.waterstep method clause extras substeps) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-atblp))))






; VALID WATERFALL STEPS.
;
; At the moment our waterfall is not very flexible, and the only steps it knows
; about are
;
;   STOP,           make no more progress,
;   UREWRITE,       simplify a clause with unconditional rewriting,
;   CREWRITE,       simplify a clause with conditional rewriting,
;   SPLIT,          break up a clause with if-lifting and if-splitting.
;
; But the format is pretty flexible and we could add other steps, just by
; adding more recognizers here, extending the compiler, etc.

(defund rw.stop-waterstep-okp (x)
  (declare (xargs :guard (rw.waterstepp x)))

; STOP steps are used when we cannot make any more progress or are forced to
; "artificially" terminate due to hitting the maximum depth.  Their clauses are
; left outstanding.  See also rw.waterfall-subgoals, which collects up the stop
; steps so that we can try to prove them later.

  (let ((method   (rw.waterstep->method x))
        (extras   (rw.waterstep->extras x))
        (substeps (rw.waterstep->substeps x)))
    (and (equal method 'stop)
         (not extras)
         (not substeps))))

(defthm booleanp-of-rw.stop-waterstep-okp
  (equal (booleanp (rw.stop-waterstep-okp x))
         t)
  :hints(("Goal" :in-theory (enable rw.stop-waterstep-okp))))




(defund rw.urewrite-waterstep-okp (x world)
  (declare (xargs :guard (and (rw.waterstepp x)
                              (tactic.worldp world))))
  (let ((method   (rw.waterstep->method x))
        (clause   (rw.waterstep->clause x))
        (extras   (rw.waterstep->extras x))
        (substeps (rw.waterstep->substeps x)))
    (and (equal method 'urewrite)
         ;; extras are (theoryname fastp traces), like in urewrite-first but
         ;; without the world index (since that's resolved at a higher level)
         (tuplep 3 extras)
         (let ((theoryname (first extras))
               (fastp      (second extras))
               (traces     (third extras)))  ;; nil when fastp
           (and (booleanp fastp)
                (if fastp
                    (let* ((rhses     (rw.fast-world-urewrite-list clause theoryname world))
                           (progressp (not (equal clause rhses))))
                      (and progressp
                           (equal (rw.waterstep-list->clauses substeps) (list rhses))))
                  (let* ((clause-rw (rw.world-urewrite-list clause theoryname world))
                         (rhses     (rw.trace-list-rhses clause-rw))
                         (progressp (not (equal clause rhses))))
                    (and progressp
                         (equal traces clause-rw)
                         (equal (rw.waterstep-list->clauses substeps) (list rhses))))))))))

(defthm booleanp-of-rw.urewrite-waterstep-okp
  (equal (booleanp (rw.urewrite-waterstep-okp x world))
         t)
  :hints(("Goal" :in-theory (e/d (rw.urewrite-waterstep-okp)
                                 ((:executable-counterpart acl2::force))))))




(defund rw.crewrite-waterstep-okp (x world)
  (declare (xargs :guard (and (rw.waterstepp x)
                              (tactic.worldp world))))

; CREWRITE steps are our uses of the rewriter.  We build the control structure
; out of the world using the named theory.  This doesn't permit much in the way
; of staged simplification, but that can be achieved by combining the waterfall
; with our regular breadth-first tactics.

  (let ((method   (rw.waterstep->method x))
        (clause   (rw.waterstep->clause x))
        (extras   (rw.waterstep->extras x))
        (substeps (rw.waterstep->substeps x)))
    (and (equal method 'crewrite)

; The extras are similar to those in tactic.crewrite-first-okp.  They are a
; 4-tuple of the form (theoryname ccsteps clause-prime forced-goals).

         (let ((plan extras))
           (and
            (rw.crewrite-clause-planp plan)
            (rw.crewrite-clause-plan-okp plan world)
            (rw.crewrite-clause-plan->progressp plan)
            (equal (rw.crewrite-clause-plan->clause plan) clause)
            (let* ((fgoals   (rw.crewrite-clause-plan->forced-goals plan))
                   (fclauses (clause.make-clauses-from-arbitrary-formulas fgoals)))
              (equal (rw.waterstep-list->clauses substeps)
                     (if (rw.crewrite-clause-plan->provedp plan)
                         fclauses
                       (cons (rw.crewrite-clause-plan->clause-prime plan)
                             fclauses)))))))))

(defthm booleanp-of-rw.crewrite-waterstep-okp
  (equal (booleanp (rw.crewrite-waterstep-okp x world))
         t)
  :hints(("Goal" :in-theory (enable rw.crewrite-waterstep-okp))))



(defund rw.split-waterstep-okp (x)
  (declare (xargs :guard (rw.waterstepp x)))
  (let ((method   (rw.waterstep->method x))
        (clause   (rw.waterstep->clause x))
        (extras   (rw.waterstep->extras x))
        (substeps (rw.waterstep->substeps x)))
    (and (equal method 'split)
         (tuplep 3 extras)
         (let ((liftp      (first extras))
               (liftlimit  (second extras))
               (splitlimit (third extras)))
           (and (booleanp liftp)
                (natp liftlimit)
                (natp splitlimit)
                (let ((result (clause.split liftp liftlimit splitlimit clause)))
                  (and (car result)
                       (equal (rw.waterstep-list->clauses substeps)
                              (cdr result)))))))))

(defthm booleanp-of-rw.split-waterstep-okp
  (equal (booleanp (rw.split-waterstep-okp x))
         t)
  :hints(("Goal" :in-theory (enable rw.split-waterstep-okp))))



(defund rw.flag-waterstep-okp (flag x world)
  (declare (xargs :guard (and (if (equal flag 'clause)
                                  (rw.waterstepp x)
                                (rw.waterstep-listp x))
                              (tactic.worldp world))
                  :measure (two-nats-measure (rank x) (if (equal flag 'clause) 1 0))))
  (if (equal flag 'clause)
      (and (let ((method (rw.waterstep->method x)))
             (cond ((equal method 'stop)     (rw.stop-waterstep-okp x))
                   ((equal method 'urewrite) (rw.urewrite-waterstep-okp x world))
                   ((equal method 'crewrite) (rw.crewrite-waterstep-okp x world))
                   ((equal method 'split)    (rw.split-waterstep-okp x))
                   (t nil)))
           (rw.flag-waterstep-okp 'list (rw.waterstep->substeps x) world))
    (if (consp x)
        (and (rw.flag-waterstep-okp 'clause (car x) world)
             (rw.flag-waterstep-okp 'list (cdr x) world))
      t)))

(defund rw.waterstep-okp (x world)
  (declare (xargs :guard (and (rw.waterstepp x)
                              (tactic.worldp world))))
  (rw.flag-waterstep-okp 'clause x world))

(defund rw.waterstep-list-okp (x world)
  (declare (xargs :guard (and (rw.waterstep-listp x)
                              (tactic.worldp world))))
  (rw.flag-waterstep-okp 'list x world))

(defthmd definition-of-rw.waterstep-okp
  (equal (rw.waterstep-okp x world)
         (and (let ((method (rw.waterstep->method x)))
                (cond ((equal method 'stop)     (rw.stop-waterstep-okp x))
                      ((equal method 'urewrite) (rw.urewrite-waterstep-okp x world))
                      ((equal method 'crewrite) (rw.crewrite-waterstep-okp x world))
                      ((equal method 'split)    (rw.split-waterstep-okp x))
                      (t nil)))
              (rw.waterstep-list-okp (rw.waterstep->substeps x) world)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstep-okp rw.waterstep-list-okp)
          :expand ((rw.flag-waterstep-okp 'clause x world)))))

(defthmd definition-of-rw.waterstep-list-okp
  (equal (rw.waterstep-list-okp x world)
         (if (consp x)
             (and (rw.waterstep-okp (car x) world)
                  (rw.waterstep-list-okp (cdr x) world))
           t))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstep-okp rw.waterstep-list-okp)
          :expand ((rw.flag-waterstep-okp 'list x world)))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-okp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-list-okp))))

(defthm rw.waterstep-list-okp-when-not-consp
  (implies (not (consp x))
           (equal (rw.waterstep-list-okp x world)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-list-okp))))

(defthm rw.waterstep-list-okp-of-cons
  (equal (rw.waterstep-list-okp (cons a x) world)
         (and (rw.waterstep-okp a world)
              (rw.waterstep-list-okp x world)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-list-okp))))

(defthm rw.waterstep-okp-of-nil
  (equal (rw.waterstep-okp nil world)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-okp))))

(defthms-flag
  :thms ((clause booleanp-of-rw.waterstep-okp
                 (equal (booleanp (rw.waterstep-okp x world))
                        t))
         (t booleanp-of-rw.waterstep-list-okp
            (equal (booleanp (rw.waterstep-list-okp x world))
                   t)))
  :hints(("Goal"
          :induct (rw.waterstep-induction flag x)
          :expand ((rw.waterstep-okp x world)))))

(deflist rw.waterstep-list-okp (x world)
  (rw.waterstep-okp x world)
  :guard (and (rw.waterstep-listp x)
              (symbolp theoryname)
              (tactic.worldp world))
  :elementp-of-nil nil
  :already-definedp t)



; THE WATERFALL

(defun rw.flag-waterfall (flag x theoryname cfastp ufastp world steps strategy n)
  (declare (xargs :guard (and (if (equal flag 'clause)
                                  (and (logic.term-listp x)
                                       (true-listp x)
                                       (consp x))
                                (and (logic.term-list-listp x)
                                     (true-list-listp x)
                                     (cons-listp x)))
                              (symbolp theoryname)
                              (booleanp ufastp)
                              (booleanp cfastp)
                              (tactic.worldp world)
                              (natp n))
                  :measure (three-nats-measure (nfix n) (len steps) (rank x))
                  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force))))
                  :verify-guards nil))

; This is a depth-first way of applying some tactics.
;
; The Inputs.
;
;  - Flag,       are we working on a 'clause or a 'list of clauses,
;  - X,          the clause(-list) we are working on,
;  - Theoryname, the name of the theory to use for rewriting,
;  - Cfastp,     whether to use fast or slow crewrite,
;  - Ufastp,     whether to use fast or slow urewrite,
;  - World,      the world we are in (for rewriting controls, etc.),
;  - Steps,      the current steps remaining in this application of the strategy
;  - Strategy,   the (fixed) strategy we are applying
;  - N,          the maximum depth we can descend to.
;
; Basically the idea is that the strategy says what we are going to try to do
; to each clause.  The strategy is a list of names of techniques to apply, and
; currently the only supported names are UREWRITE, CREWRITE, CREWRITE-ONCE,
; SPLIT, and NOLIFT-SPLIT.  The strategy is like a "waterfall", so that, e.g.,
; given the strategy (crewrite split), we will always try to apply crewrite
; until the clause is stable under crewrite, then we'll split once and
; immediatley go back to trying crewrite.  See also the %auto tactic, which
; uses a similar thing.

  (if (equal flag 'clause)
      (cond ((zp n)
             (ACL2::prog2$ (ACL2::cw "; rw.flag-waterfall: ran out of steps~%")
                           (rw.waterstep 'stop x nil nil)))

            ((not (consp steps))
             ;; The waterfall has been exhausted, no more steps can be applied
             (rw.waterstep 'stop x nil nil))

            ((equal (car steps) 'urewrite)
             (if ufastp
                 (let* ((x-prime   (rw.fast-world-urewrite-list x theoryname world))
                        (progressp (not (equal x x-prime))))
                   (if progressp
                       (rw.waterstep 'urewrite
                                     x
                                     (list theoryname ufastp nil)
                                     ;; This is like crewerite-once, we fall transparently
                                     ;; through to the next step since urewrite should pretty
                                     ;; much canonicalize in one pass.
                                     (rw.flag-waterfall 'list (list x-prime) theoryname cfastp ufastp
                                                        world (cdr steps) strategy (- n 1)))
                     (rw.flag-waterfall 'clause x theoryname cfastp ufastp world (cdr steps) strategy n)))

               (let* ((traces    (rw.world-urewrite-list x theoryname world))
                      (x-prime   (rw.trace-list-rhses traces))
                      (progressp (not (equal x x-prime))))
                 (if progressp
                     (rw.waterstep 'urewrite
                                   x
                                   (list theoryname ufastp traces)
                                   (rw.flag-waterfall 'list (list x-prime) theoryname cfastp ufastp
                                                      world (cdr steps) strategy (- n 1)))
                   (rw.flag-waterfall 'clause x theoryname cfastp ufastp world (cdr steps) strategy n)))))

            ((or (equal (car steps) 'crewrite)      ;; to a fixed-point
                 (equal (car steps) 'crewrite-once) ;; only once then go on
                 )
             (let* ((plan (rw.make-crewrite-clause-plan x cfastp theoryname world)))
               (if (rw.crewrite-clause-plan->progressp plan)
                   (let* ((provedp   (rw.crewrite-clause-plan->provedp plan))
                          (fgoals    (rw.crewrite-clause-plan->forced-goals plan))
                          (fclauses  (clause.make-clauses-from-arbitrary-formulas fgoals))
                          (new-goals (if provedp
                                         fclauses
                                       (cons (rw.crewrite-clause-plan->clause-prime plan)
                                             fclauses))))
                     (rw.waterstep 'crewrite
                                   x
                                   plan
                                   (if (equal (car steps) 'crewrite)
                                       ;; Restart the waterfall, decreasing depth
                                       (rw.flag-waterfall 'list new-goals theoryname cfastp ufastp world
                                                          strategy strategy (- n 1))
                                     ;; Go on to the next steps.
                                     (rw.flag-waterfall 'list new-goals theoryname cfastp ufastp world
                                                        (cdr steps) strategy n))))
                 ;; Failed to achieve anything.  Continue to the subsequent steps.
                 (rw.flag-waterfall 'clause x theoryname cfastp ufastp world (cdr steps) strategy n))))

            ((or (equal (car steps) 'split)
                 (equal (car steps) 'nolift-split))
             (let* ((liftp       (equal (car steps) 'split))
                    (liftlimit   (tactic.world->liftlimit world))
                    (splitlimit  (tactic.world->splitlimit world))
                    (result      (clause.split liftp liftlimit splitlimit x))
                    (progressp   (car result))
                    (new-goals   (cdr result)))
               (if progressp
                   ;; Restart the waterfall on the new-goals, decreasing depth.
                   (rw.waterstep 'split x (list liftp liftlimit splitlimit)
                                 (rw.flag-waterfall 'list new-goals theoryname cfastp ufastp
                                                    world strategy strategy (- n 1)))
                 ;; Failed, continue
                 (rw.flag-waterfall 'clause x theoryname cfastp ufastp world (cdr steps) strategy n))))

            (t
             ;; Just keep going if we don't recognize the step.
             (ACL2::prog2$
              (ACL2::cw ";; flag-water-clause: skipping unknown step: ~x0.~%" (car steps))
              (rw.flag-waterfall 'clause x theoryname cfastp ufastp world (cdr steps) strategy n))))

    (if (consp x)
        (cons (rw.flag-waterfall 'clause (car x) theoryname cfastp ufastp world steps strategy n)
              (rw.flag-waterfall 'list (cdr x) theoryname cfastp ufastp world steps strategy n))
      nil)))

(defund rw.waterfall (x theoryname cfastp ufastp world steps strategy n)
  (declare (xargs :guard (and (logic.term-listp x)
                              (true-listp x)
                              (consp x)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (tactic.worldp world)
                              (natp n))
                  :verify-guards nil))
  (rw.flag-waterfall 'clause x theoryname cfastp ufastp world steps strategy n))

(defund rw.waterfall-list (x theoryname cfastp ufastp world steps strategy n)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (true-list-listp x)
                              (cons-listp x)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (tactic.worldp world)
                              (natp n))
                  :verify-guards nil))
  (rw.flag-waterfall 'list x theoryname cfastp ufastp world steps strategy n))

(defthmd definition-of-rw.waterfall
  (equal (rw.waterfall x theoryname cfastp ufastp world steps strategy n)
         (cond ((zp n)
                (rw.waterstep 'stop x nil nil))

               ((not (consp steps))
                (rw.waterstep 'stop x nil nil))

               ((equal (car steps) 'urewrite)
                (if ufastp
                    (let* ((x-prime   (rw.fast-world-urewrite-list x theoryname world))
                           (progressp (not (equal x x-prime))))
                      (if progressp
                          (rw.waterstep 'urewrite
                                        x
                                        (list theoryname ufastp nil)
                                        (rw.waterfall-list (list x-prime) theoryname cfastp ufastp
                                                           world (cdr steps) strategy (- n 1)))
                        (rw.waterfall x theoryname cfastp ufastp world (cdr steps) strategy n)))

               (let* ((traces    (rw.world-urewrite-list x theoryname world))
                      (x-prime   (rw.trace-list-rhses traces))
                      (progressp (not (equal x x-prime))))
                 (if progressp
                     (rw.waterstep 'urewrite
                                   x
                                   (list theoryname ufastp traces)
                                   (rw.waterfall-list (list x-prime) theoryname cfastp ufastp
                                                      world (cdr steps) strategy (- n 1)))
                   (rw.waterfall x theoryname cfastp ufastp world (cdr steps) strategy n)))))

               ((or (equal (car steps) 'crewrite)
                    (equal (car steps) 'crewrite-once))
                (let* ((plan (rw.make-crewrite-clause-plan x cfastp theoryname world)))
                  (if (rw.crewrite-clause-plan->progressp plan)
                      (let* ((provedp   (rw.crewrite-clause-plan->provedp plan))
                             (fgoals    (rw.crewrite-clause-plan->forced-goals plan))
                             (fclauses  (clause.make-clauses-from-arbitrary-formulas fgoals))
                             (new-goals (if provedp
                                            fclauses
                                          (cons (rw.crewrite-clause-plan->clause-prime plan)
                                                fclauses))))
                        (rw.waterstep 'crewrite
                                      x
                                      plan
                                      (if (equal (car steps) 'crewrite)
                                          (rw.waterfall-list new-goals theoryname cfastp ufastp world
                                                             strategy strategy (- n 1))
                                        (rw.waterfall-list new-goals theoryname cfastp ufastp world
                                                           (cdr steps) strategy n))))
                    (rw.waterfall x theoryname cfastp ufastp world (cdr steps) strategy n))))

               ((or (equal (car steps) 'split)
                    (equal (car steps) 'nolift-split))
                (let* ((liftp       (equal (car steps) 'split))
                       (liftlimit   (tactic.world->liftlimit world))
                       (splitlimit  (tactic.world->splitlimit world))
                       (result      (clause.split liftp liftlimit splitlimit x))
                       (progressp   (car result))
                       (new-goals   (cdr result)))
                  (if progressp
                      (rw.waterstep 'split x (list liftp liftlimit splitlimit)
                                    (rw.waterfall-list new-goals theoryname cfastp ufastp world
                                                       strategy strategy (- n 1)))
                    (rw.waterfall x theoryname cfastp ufastp world (cdr steps) strategy n))))

               (t
                (rw.waterfall x theoryname cfastp ufastp world (cdr steps) strategy n))))
  :rule-classes :definition
  :hints(("Goal"
          :expand ((rw.flag-waterfall 'clause x theoryname cfastp ufastp world steps strategy n))
          :in-theory (enable rw.waterfall rw.waterfall-list))))

(defthmd definition-of-rw.waterfall-list
  (equal (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n)
         (if (consp x)
             (cons (rw.waterfall (car x) theoryname cfastp ufastp world steps strategy n)
                   (rw.waterfall-list (cdr x) theoryname cfastp ufastp world steps strategy n))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :expand ((rw.flag-waterfall 'list x theoryname cfastp ufastp world steps strategy n))
          :in-theory (enable rw.waterfall rw.waterfall-list))))

(defthm rw.flag-waterfall-of-clause
  (equal (rw.flag-waterfall 'clause x theoryname cfastp ufastp world steps strategy n)
         (rw.waterfall x theoryname cfastp ufastp world steps strategy n))
  :hints(("Goal" :in-theory (enable rw.waterfall))))

(defthm rw.flag-waterfall-of-list
  (equal (rw.flag-waterfall 'list x theoryname cfastp ufastp world steps strategy n)
         (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n))
  :hints(("Goal" :in-theory (enable rw.waterfall-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterfall))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterfall-list))))

(defthm rw.waterfall-list-when-not-consp
  (implies (not (consp x))
           (equal (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterfall-list))))

(defthm rw.waterfall-list-of-cons
  (equal (rw.waterfall-list (cons a x) theoryname cfastp ufastp world steps strategy n)
         (cons (rw.waterfall a theoryname cfastp ufastp world steps strategy n)
               (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterfall-list))))

(defprojection
  :list (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n)
  :element (rw.waterfall x theoryname cfastp ufastp world steps strategy n)
  :nil-preservingp nil
  :already-definedp t)

(defthm true-listp-of-clause.make-clause-from-arbitrary-formula
  (equal (true-listp (clause.make-clause-from-arbitrary-formula x))
         t)
  :hints(("Goal" :in-theory (enable clause.make-clause-from-arbitrary-formula))))

(defthm true-list-listp-of-clause.make-clauses-from-arbitrary-formulas
  (equal (true-list-listp (clause.make-clauses-from-arbitrary-formulas x))
         t)
  :hints(("Goal" :in-theory (enable clause.make-clauses-from-arbitrary-formulas))))




(defthmd lemma-2-for-rw.waterstepp-of-rw.waterfall
  ;; wow horrible gross
  (implies (force (and (true-listp x)
                       (logic.term-listp x)
                       (consp x)
                       (tactic.worldp world)))
           (equal (true-listp (rw.crewrite-clause-plan->clause-prime
                               (rw.make-crewrite-clause-plan x cfastp theoryname world)))
                  t))
  :hints(("Goal"
          :in-theory (e/d (rw.make-crewrite-clause-plan
                           rw.crewrite-clause-plan->clause-prime)))))

(defthms-flag
  :shared-hyp (force (and (symbolp theoryname)
                          (tactic.worldp world)
                          (natp n)))
  :thms ((clause rw.waterstepp-of-rw.waterfall
                 (implies (force (and (logic.term-listp x)
                                      (true-listp x)
                                      (consp x)))
                          (rw.waterstepp (rw.waterfall x theoryname cfastp ufastp world steps strategy n))))
         (t rw.waterstep-listp-of-rw.waterfall-list
            (implies (force (and (logic.term-list-listp x)
                                 (true-list-listp x)
                                 (cons-listp x)))
                     (rw.waterstep-listp (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n)))))
  :hints(("Goal"
          :induct (rw.flag-waterfall flag x theoryname cfastp ufastp world steps strategy n)
          :in-theory (enable definition-of-rw.waterfall
                             lemma-2-for-rw.waterstepp-of-rw.waterfall))))



(defthmd lemma-1-for-rw.waterstep-atblp-of-rw.waterfall
  ;; GROSS !!!! Horrible lemmas.  Stupid ccsteps.
  (implies (force (and (rw.trace-atblp (rw.ccstep->trace x) atbl)
                       (rw.hypbox-atblp (rw.ccstep->hypbox x) atbl)))
           (equal (logic.term-list-atblp (rw.ccstep->clause-prime x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep->clause-prime))))

(defthmd lemma-2-for-rw.waterstep-atblp-of-rw.waterfall
  ;; GROSS !!!! Horrible lemmas.  Stupid ccsteps.
  (implies (force (and (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl)
                       (not (rw.ccstep->provedp (car x)))
                       (consp x)))
           (equal (rw.trace-atblp (rw.ccstep->trace (car x)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-gather-traces
                                    rw.ccstep->provedp
                                    rw.ccstep->contradiction))))

(defthmd lemma-3-for-rw.waterstep-atblp-of-rw.waterfall
  ;; GROSS !!!! Horrible lemmas.  Stupid ccsteps.
  (implies (force (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes x) atbl))
           (equal (rw.hypbox-atblp (rw.ccstep->hypbox (car x)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-hypboxes))))

(defthmd lemma-4-for-rw.waterstep-atblp-of-rw.waterfall
  (implies (and (equal free (rw.ccstep->clause-prime x))
                (force (rw.trace-atblp (rw.ccstep->trace x) atbl))
                (force (rw.hypbox-atblp (rw.ccstep->hypbox x) atbl)))
           (equal (logic.term-list-atblp free atbl)
                  t))
  :hints(("Goal" :in-theory (enable lemma-1-for-rw.waterstep-atblp-of-rw.waterfall))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthmd lemma-5-for-rw.waterstep-atblp-of-rw.waterfall
   (implies (force (and (rw.crewrite-clause-planp x)
                        (rw.crewrite-clause-plan-atblp x atbl)
                        (rw.crewrite-clause-plan-okp x world)
                        (tactic.worldp world)
                        (tactic.world-atblp world atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (logic.term-list-atblp (rw.crewrite-clause-plan->clause-prime x) atbl)
                   t))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-clause-planp
                              rw.crewrite-clause-plan-atblp
                              rw.crewrite-clause-plan-okp
                              rw.crewrite-clause-plan->clause
                              rw.crewrite-clause-plan->clause-prime
                              lemma-1-for-rw.waterstep-atblp-of-rw.waterfall
                              lemma-2-for-rw.waterstep-atblp-of-rw.waterfall
                              lemma-3-for-rw.waterstep-atblp-of-rw.waterfall
                              lemma-4-for-rw.waterstep-atblp-of-rw.waterfall)))))

(defthms-flag
  :shared-hyp (force (and (symbolp theoryname)
                          (tactic.worldp world)
                          (tactic.world-atblp world atbl)
                          (equal (cdr (lookup 'not atbl)) 1)
                          (equal (cdr (lookup 'equal atbl)) 2)
                          (equal (cdr (lookup 'iff atbl)) 2)
                          (equal (cdr (lookup 'if atbl)) 3)
                          (natp n)))
  :thms ((clause rw.waterstep-atblp-of-rw.waterfall
                 (implies (force (and (logic.term-listp x)
                                      (logic.term-list-atblp x atbl)
                                      (true-listp x)
                                      (consp x)))
                          (rw.waterstep-atblp (rw.waterfall x theoryname cfastp ufastp world steps strategy n)
                                              atbl)))
         (t rw.waterstep-list-atblp-of-rw.waterfall-list
            (implies (force (and (logic.term-list-listp x)
                                 (logic.term-list-list-atblp x atbl)
                                 (true-list-listp x)
                                 (cons-listp x)))
                     (rw.waterstep-list-atblp (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n)
                                              atbl))))
  :hints(("Goal"
          :induct (rw.flag-waterfall flag x theoryname cfastp ufastp world steps strategy n)
          :in-theory (enable lemma-1-for-rw.waterstep-atblp-of-rw.waterfall
                             lemma-2-for-rw.waterstep-atblp-of-rw.waterfall
                             lemma-3-for-rw.waterstep-atblp-of-rw.waterfall
                             lemma-4-for-rw.waterstep-atblp-of-rw.waterfall
                             lemma-5-for-rw.waterstep-atblp-of-rw.waterfall
                             lemma-2-for-rw.waterstepp-of-rw.waterfall
                             )
          :restrict ((lemma-5-for-rw.waterstep-atblp-of-rw.waterfall
                      ((world world)))
                     (logic.formula-list-atblp-of-rw.crewrite-clause-plan->forced-goals
                      ((world world))))
          :expand ((:free (n cfastp ufastp)
                          (rw.waterfall x theoryname cfastp ufastp world steps strategy n))))))

(defthms-flag
  :thms ((clause rw.waterstep->clause-of-rw.waterfall
                 (equal (rw.waterstep->clause (rw.waterfall x theoryname cfastp ufastp world steps strategy n))
                        x))
         (t rw.waterstep-list->clauses-of-rw.waterfall-list
            (equal (rw.waterstep-list->clauses (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n))
                   (list-fix x))))
  :hints(("Goal"
          :induct (rw.flag-waterfall flag x theoryname cfastp ufastp world steps strategy n)
          :in-theory (e/d (definition-of-rw.waterfall)
                          ((:executable-counterpart acl2::force))))))


(ACL2::with-output
 :gag-mode :goals
 (defthms-flag

; This proof is kind of lousy.  We don't have a very good way to encapsulate
; the various steps, so we end up proving them all at once.

   :shared-hyp (force (and (tactic.worldp world)
                           (booleanp ufastp)
                           (booleanp cfastp)
                           (symbolp theoryname)
                           (natp n)))
   :thms ((clause rw.waterstep-okp-of-rw.waterfall
                  (implies (force (and (logic.term-listp x)
                                       (true-listp x)
                                       (consp x)))
                           (rw.waterstep-okp (rw.waterfall x theoryname cfastp ufastp world steps strategy n) world)))
          (t rw.waterstep-list-okp-of-rw.waterfall-list
             (implies (force (and (logic.term-list-listp x)
                                  (true-list-listp x)
                                  (cons-listp x)))
                      (rw.waterstep-list-okp (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n) world))))
   :hints(("Goal"
           :induct (rw.flag-waterfall flag x theoryname cfastp ufastp world steps strategy n)
           :in-theory (enable definition-of-rw.waterfall)
           :expand ((:free (cfastp ufastp) (rw.waterfall x theoryname cfastp ufastp world steps strategy n))))
          (and ACL2::stable-under-simplificationp
               '(:in-theory (enable definition-of-rw.waterstep-okp
                                    rw.stop-waterstep-okp
                                    rw.crewrite-waterstep-okp
                                    rw.split-waterstep-okp
                                    rw.urewrite-waterstep-okp
                                    lemma-2-for-rw.waterstepp-of-rw.waterfall))))))

(verify-guards rw.flag-waterfall
               :hints(("Goal" :in-theory (enable lemma-2-for-rw.waterstepp-of-rw.waterfall))))

(verify-guards rw.waterfall)
(verify-guards rw.waterfall-list)




(defun rw.flag-waterfall-subgoals (flag x)
  (declare (xargs :guard (if (equal flag 'clause)
                             (rw.waterstepp x)
                           (rw.waterstep-listp x))
                  :measure (two-nats-measure (rank x) (if (equal flag 'clause) 1 0))))

; We walk through the waterfall steps, collecting the clause for each STOP
; step.  These are the clauses that still need to be proven before we can
; compile this waterfall step into a real proof.

  (if (equal flag 'clause)
      (let ((method (rw.waterstep->method x)))
        (if (equal method 'stop)
            (list (rw.waterstep->clause x))
          (rw.flag-waterfall-subgoals 'list (rw.waterstep->substeps x))))
    (if (consp x)
        ;; BOZO potentially slow.  On the other hand, maybe there aren't all that many
        ;; unproven subgoals in practice.  Could optimize using an accumulator, per usual.
        (app (rw.flag-waterfall-subgoals 'clause (car x))
             (rw.flag-waterfall-subgoals 'list (cdr x)))
      nil)))

(defund rw.waterfall-subgoals (x)
  (declare (xargs :guard (rw.waterstepp x)))
  (rw.flag-waterfall-subgoals 'clause x))

(defund rw.waterfall-list-subgoals (x)
  (declare (xargs :guard (rw.waterstep-listp x)))
  (rw.flag-waterfall-subgoals 'list x))

(defthmd definition-of-rw.waterfall-subgoals
  (equal (rw.waterfall-subgoals x)
         (let ((method (rw.waterstep->method x)))
           (if (equal method 'stop)
               (list (rw.waterstep->clause x))
             (rw.waterfall-list-subgoals (rw.waterstep->substeps x)))))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterfall-subgoals
                             rw.waterfall-list-subgoals)
          :expand ((rw.flag-waterfall-subgoals 'clause x)))))

(defthmd definition-of-rw.waterfall-list-subgoals
  (equal (rw.waterfall-list-subgoals x)
         (if (consp x)
             (app (rw.waterfall-subgoals (car x))
                  (rw.waterfall-list-subgoals (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterfall-subgoals
                             rw.waterfall-list-subgoals)
          :expand ((rw.flag-waterfall-subgoals 'list x)))))

(defthm rw.flag-waterfall-subgoals-of-clause
  (equal (rw.flag-waterfall-subgoals 'clause x)
         (rw.waterfall-subgoals x))
  :hints(("Goal" :in-theory (enable rw.waterfall-subgoals))))

(defthm rw.flag-waterfall-list-subgoals-of-clause
  (equal (rw.flag-waterfall-subgoals 'list x)
         (rw.waterfall-list-subgoals x))
  :hints(("Goal" :in-theory (enable rw.waterfall-list-subgoals))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterfall-subgoals))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterfall-list-subgoals))))

(defthm rw.waterfall-list-subgoals-when-not-consp
  (implies (not (consp x))
           (equal (rw.waterfall-list-subgoals x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterfall-list-subgoals))))

(defthm rw.waterfall-list-subgoals-of-cons
  (equal (rw.waterfall-list-subgoals (cons a x))
         (app (rw.waterfall-subgoals a)
              (rw.waterfall-list-subgoals x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterfall-list-subgoals))))

(defthms-flag
  :thms ((clause logic.term-list-listp-of-rw.waterfall-subgoals
                 (implies (force (rw.waterstepp x))
                          (equal (logic.term-list-listp (rw.waterfall-subgoals x))
                                 t)))
         (t logic.term-list-listp-of-rw.waterfall-list-subgoals
            (implies (force (rw.waterstep-listp x))
                     (equal (logic.term-list-listp (rw.waterfall-list-subgoals x))
                            t))))
  :hints(("Goal"
          :induct (rw.flag-waterfall-subgoals flag x)
          :in-theory (enable definition-of-rw.waterfall-subgoals))))

(defthms-flag
  :thms ((clause cons-listp-of-rw.waterfall-subgoals
                 (implies (force (rw.waterstepp x))
                          (equal (cons-listp (rw.waterfall-subgoals x))
                                 t)))
         (t cons-listp-of-rw.waterfall-list-subgoals
            (implies (force (rw.waterstep-listp x))
                     (equal (cons-listp (rw.waterfall-list-subgoals x))
                            t))))
  :hints(("Goal"
          :induct (rw.flag-waterfall-subgoals flag x)
          :in-theory (enable definition-of-rw.waterfall-subgoals))))

(defthms-flag
  :thms ((clause true-list-listp-of-rw.waterfall-subgoals
                 (implies (force (rw.waterstepp x))
                          (equal (true-list-listp (rw.waterfall-subgoals x))
                                 t)))
         (t true-list-listp-rw.waterfall-list-subgoals
            (implies (force (rw.waterstep-listp x))
                     (equal (true-list-listp (rw.waterfall-list-subgoals x))
                            t))))
  :hints(("Goal"
          :induct (rw.flag-waterfall-subgoals flag x)
          :in-theory (enable definition-of-rw.waterfall-subgoals))))

(defthms-flag
  :thms ((clause true-listp-of-rw.waterfall-subgoals
                 (equal (true-listp (rw.waterfall-subgoals x))
                        t))
         (t true-listp-rw.waterfall-list-subgoals
            (equal (true-listp (rw.waterfall-list-subgoals x))
                   t)))
  :hints(("Goal"
          :induct (rw.flag-waterfall-subgoals flag x)
          :in-theory (enable definition-of-rw.waterfall-subgoals))))





; WATERFALL STEP COMPILER
;
; As might be expected, we just introduce a compiler for each kind of step.  We
; show that given proofs of all of the remaining waterfall-subgoals, we can
; construct a proof of the clause for this step.
;
; In these compilers, we distinguish between RPROOFS and SPROOFS.
;
;   RPROOFS are the "remaining proofs" after the entire waterfall completes.
;   That is, they are the proofs of all the waterfall-subgoals.
;
;   SPROOFS are, for non-atomic proof steps, the proofs of the clauses
;   of the substeps.

(defsection rw.stop-waterstep-compiler

  (defund rw.stop-waterstep-compiler (x rproofs)
    (declare (xargs :guard (and (rw.waterstepp x)
                                (rw.stop-waterstep-okp x)
                                (logic.appeal-listp rproofs)
                                (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                         (logic.strip-conclusions rproofs)))))
    (logic.find-proof (clause.clause-formula (rw.waterstep->clause x))
                      rproofs))

  (local (in-theory (enable rw.stop-waterstep-compiler
                            rw.stop-waterstep-okp
                            definition-of-rw.waterfall-subgoals)))

  (defthm logic.appealp-of-rw.stop-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (rw.stop-waterstep-okp x)
                         (logic.appeal-listp rproofs)
                         (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                  (logic.strip-conclusions rproofs))))
             (equal (logic.appealp (rw.stop-waterstep-compiler x rproofs))
                    t)))

  (defthm logic.conclusion-of-rw.stop-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (rw.stop-waterstep-okp x)
                         (logic.appeal-listp rproofs)
                         (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                  (logic.strip-conclusions rproofs))))
             (equal (logic.conclusion (rw.stop-waterstep-compiler x rproofs))
                    (clause.clause-formula (rw.waterstep->clause x)))))

  (defthm logic.proofp-of-rw.stop-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (rw.stop-waterstep-okp x)
                         (logic.appeal-listp rproofs)
                         (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                  (logic.strip-conclusions rproofs))
                         ;; ---
                         (logic.proof-listp rproofs axioms thms atbl)))
             (equal (logic.proofp (rw.stop-waterstep-compiler x rproofs) axioms thms atbl)
                    t))))



(defsection rw.urewrite-waterstep-compiler

  (defund rw.urewrite-waterstep-compiler (x world sproofs)
    (declare (xargs :guard (and (rw.waterstepp x)
                                (tactic.worldp world)
                                (rw.urewrite-waterstep-okp x world)
                                (logic.appeal-listp sproofs)
                                (equal (logic.strip-conclusions sproofs)
                                       (clause.clause-list-formulas
                                        (rw.waterstep-list->clauses
                                         (rw.waterstep->substeps x)))))
                    :verify-guards nil))
    (let* ((clause       (rw.waterstep->clause x))
           (extras       (rw.waterstep->extras x))
           (substeps     (rw.waterstep->substeps x))
           (clause-prime (rw.waterstep->clause (car substeps)))
           (theoryname   (first extras))
           (fastp        (second extras))
           (traces       (third extras)))
      (rw.world-urewrite-list-bldr clause clause-prime fastp theoryname world traces (car sproofs))))

  (defobligations rw.urewrite-waterstep-compiler
    (rw.world-urewrite-list-bldr))

  (local (in-theory (enable rw.urewrite-waterstep-compiler
                            rw.urewrite-waterstep-okp)))

  (verify-guards rw.urewrite-waterstep-compiler)

  (defthm logic.appealp-of-rw.urewrite-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (tactic.worldp world)
                         (rw.urewrite-waterstep-okp x world)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))))
             (equal (logic.appealp (rw.urewrite-waterstep-compiler x world sproofs))
                    t)))

  (defthm logic.conclusion-of-rw.urewrite-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (tactic.worldp world)
                         (rw.urewrite-waterstep-okp x world)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))))
             (equal (logic.conclusion (rw.urewrite-waterstep-compiler x world sproofs))
                    (clause.clause-formula (rw.waterstep->clause x)))))

  (defthm@ logic.proofp-of-rw.urewrite-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (tactic.worldp world)
                         (rw.urewrite-waterstep-okp x world)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))
                         ;; ---
                         (rw.waterstep-atblp x atbl)
                         (tactic.world-atblp world atbl)
                         (tactic.world-env-okp world axioms thms)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (logic.proof-listp sproofs axioms thms atbl)
                         (@obligations rw.urewrite-waterstep-compiler)
                         ))
             (equal (logic.proofp (rw.urewrite-waterstep-compiler x world sproofs) axioms thms atbl)
                    t))))


(defsection rw.crewrite-waterstep-compiler

  (defund rw.crewrite-waterstep-compiler (x world sproofs)
    (declare (xargs :guard (and (rw.waterstepp x)
                                (tactic.worldp world)
                                (rw.crewrite-waterstep-okp x world)
                                (logic.appeal-listp sproofs)
                                (equal (logic.strip-conclusions sproofs)
                                       (clause.clause-list-formulas
                                        (rw.waterstep-list->clauses
                                         (rw.waterstep->substeps x)))))
                    :verify-guards nil))
    (let* ( ;(clause  (rw.waterstep->clause x))
           (plan    (rw.waterstep->extras x))
           (provedp (rw.crewrite-clause-plan->provedp plan))
           (fgoals  (rw.crewrite-clause-plan->forced-goals plan)))
      (if provedp
          (let ((fproofs (clause.prove-arbitrary-formulas-from-their-clauses fgoals sproofs)))
            (rw.crewrite-clause-plan-compiler plan world nil fproofs))
        (let ((proof1  (car sproofs))
              (fproofs (clause.prove-arbitrary-formulas-from-their-clauses fgoals (cdr sproofs))))
          (rw.crewrite-clause-plan-compiler plan world proof1 fproofs)))))


  (defobligations rw.crewrite-waterstep-compiler
    (rw.crewrite-clause-bldr
     clause.prove-arbitrary-formulas-from-their-clauses))

  (local (in-theory (enable rw.crewrite-waterstep-compiler rw.crewrite-waterstep-okp)))

  (verify-guards rw.crewrite-waterstep-compiler)

  (defthm logic.appealp-of-rw.crewrite-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (tactic.worldp world)
                         (rw.crewrite-waterstep-okp x world)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))))
             (equal (logic.appealp (rw.crewrite-waterstep-compiler x world sproofs))
                    t)))

  (defthm logic.conclusion-of-rw.crewrite-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (tactic.worldp world)
                         (rw.crewrite-waterstep-okp x world)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))))
             (equal (logic.conclusion (rw.crewrite-waterstep-compiler x world sproofs))
                    (clause.clause-formula (rw.waterstep->clause x)))))

  (defthm@ logic.proofp-of-rw.crewrite-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (tactic.worldp world)
                         (rw.crewrite-waterstep-okp x world)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))
                         ;; ---
                         (rw.waterstep-atblp x atbl)
                         (tactic.world-atblp world atbl)
                         (tactic.world-env-okp world axioms thms)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (logic.proof-listp sproofs axioms thms atbl)
                         (@obligations rw.crewrite-waterstep-compiler)
                         ))
             (equal (logic.proofp (rw.crewrite-waterstep-compiler x world sproofs) axioms thms atbl)
                    t))))



(defsection rw.split-waterstep-compiler

  (defund rw.split-waterstep-compiler (x sproofs)
    (declare (xargs :guard (and (rw.waterstepp x)
                                (rw.split-waterstep-okp x)
                                (logic.appeal-listp sproofs)
                                (equal (logic.strip-conclusions sproofs)
                                       (clause.clause-list-formulas
                                        (rw.waterstep-list->clauses
                                         (rw.waterstep->substeps x)))))
                    :verify-guards nil))
    (let* ((clause     (rw.waterstep->clause x))
           (extras     (rw.waterstep->extras x))
           (liftp      (first extras))
           (liftlimit  (second extras))
           (splitlimit (third extras)))
      (clause.split-bldr liftp liftlimit splitlimit clause sproofs)))

  (defobligations rw.split-waterstep-compiler
    (clause.split-bldr))

  (local (in-theory (enable rw.split-waterstep-okp rw.split-waterstep-compiler)))

  (verify-guards rw.split-waterstep-compiler)

  (defthm logic.appealp-of-rw.split-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (rw.split-waterstep-okp x)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))))
             (equal (logic.appealp (rw.split-waterstep-compiler x sproofs))
                    t)))

  (defthm logic.conclusion-of-rw.split-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (rw.split-waterstep-okp x)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))))
             (equal (logic.conclusion (rw.split-waterstep-compiler x sproofs))
                    (clause.clause-formula (rw.waterstep->clause x)))))

  (defthm@ logic.proofp-of-rw.split-waterstep-compiler
    (implies (force (and (rw.waterstepp x)
                         (rw.split-waterstep-okp x)
                         (logic.appeal-listp sproofs)
                         (equal (logic.strip-conclusions sproofs)
                                (clause.clause-list-formulas
                                 (rw.waterstep-list->clauses
                                  (rw.waterstep->substeps x))))
                         ;; ---
                         (rw.waterstep-atblp x atbl)
                         (logic.proof-listp sproofs axioms thms atbl)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (@obligations rw.split-waterstep-compiler)
                         ))
             (equal (logic.proofp (rw.split-waterstep-compiler x sproofs) axioms thms atbl)
                    t))))



(defund rw.flag-waterstep-compiler (flag x world rproofs)
  (declare (xargs :guard (and (logic.appeal-listp rproofs)
                              (tactic.worldp world)
                              (if (equal flag 'clause)
                                  (and (rw.waterstepp x)
                                       (rw.waterstep-okp x world)
                                       (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                                (logic.strip-conclusions rproofs)))
                                (and (rw.waterstep-listp x)
                                     (rw.waterstep-list-okp x world)
                                     (subsetp (clause.clause-list-formulas (rw.waterfall-list-subgoals x))
                                              (logic.strip-conclusions rproofs)))))
                  :measure (two-nats-measure (rank x) (if (equal flag 'clause) 1 0))
                  :verify-guards nil))
  (if (equal flag 'clause)
      (let* ((method   (rw.waterstep->method x))
             (substeps (rw.waterstep->substeps x))
             (sproofs  (rw.flag-waterstep-compiler 'list substeps world rproofs)))
        (cond ((equal method 'stop)
               (rw.stop-waterstep-compiler x rproofs))
              ((equal method 'urewrite)
               (rw.urewrite-waterstep-compiler x world sproofs))
              ((equal method 'crewrite)
               (rw.crewrite-waterstep-compiler x world sproofs))
              ((equal method 'split)
               (rw.split-waterstep-compiler x sproofs))))
    (if (consp x)
        (cons (rw.flag-waterstep-compiler 'clause (car x) world rproofs)
              (rw.flag-waterstep-compiler 'list (cdr x) world rproofs))
      nil)))

(defobligations rw.flag-waterstep-compiler
  (rw.stop-waterstep-compiler
   rw.urewrite-waterstep-compiler
   rw.crewrite-waterstep-compiler
   rw.split-waterstep-compiler))

(defund rw.waterstep-compiler (x world rproofs)
  (declare (xargs :guard (and (logic.appeal-listp rproofs)
                              (tactic.worldp world)
                              (rw.waterstepp x)
                              (rw.waterstep-okp x world)
                              (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                       (logic.strip-conclusions rproofs)))
                  :verify-guards nil))
  (rw.flag-waterstep-compiler 'clause x world rproofs))

(defund rw.waterstep-list-compiler (x world rproofs)
  (declare (xargs :guard (and (logic.appeal-listp rproofs)
                              (tactic.worldp world)
                              (rw.waterstep-listp x)
                              (rw.waterstep-list-okp x world)
                              (subsetp (clause.clause-list-formulas (rw.waterfall-list-subgoals x))
                                       (logic.strip-conclusions rproofs)))
                  :verify-guards nil))
  (rw.flag-waterstep-compiler 'list x world rproofs))

(defobligations rw.waterstep-compiler
  (rw.flag-waterstep-compiler))

(defobligations rw.waterstep-list-compiler
  (rw.flag-waterstep-compiler))

(defthmd definition-of-rw.waterstep-compiler
  (equal (rw.waterstep-compiler x world rproofs)
         (let* ((method   (rw.waterstep->method x))
                (substeps (rw.waterstep->substeps x))
                (sproofs  (rw.waterstep-list-compiler substeps world rproofs)))
           (cond ((equal method 'stop)
                  (rw.stop-waterstep-compiler x rproofs))
                 ((equal method 'urewrite)
                  (rw.urewrite-waterstep-compiler x world sproofs))
                 ((equal method 'crewrite)
                  (rw.crewrite-waterstep-compiler x world sproofs))
                 ((equal method 'split)
                  (rw.split-waterstep-compiler x sproofs)))))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstep-compiler rw.waterstep-list-compiler)
          :expand (rw.flag-waterstep-compiler 'clause x world rproofs))))

(defthmd definition-of-rw.waterstep-list-compiler
  (equal (rw.waterstep-list-compiler x world rproofs)
         (if (consp x)
             (cons (rw.waterstep-compiler (car x) world rproofs)
                   (rw.waterstep-list-compiler (cdr x) world rproofs))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.waterstep-compiler rw.waterstep-list-compiler)
          :expand (rw.flag-waterstep-compiler 'list x world rproofs))))

(defthm rw.flag-waterstep-compiler-of-clause
  (equal (rw.flag-waterstep-compiler 'clause x world rproofs)
         (rw.waterstep-compiler x world rproofs))
  :hints(("Goal" :in-theory (enable rw.waterstep-compiler))))

(defthm rw.flag-waterstep-compiler-of-list
  (equal (rw.flag-waterstep-compiler 'list x world rproofs)
         (rw.waterstep-list-compiler x world rproofs))
  :hints(("Goal" :in-theory (enable rw.waterstep-list-compiler))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-compiler))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.waterstep-list-compiler))))

(defthm rw.waterstep-compiler-of-nil
  (equal (rw.waterstep-compiler nil world rproofs)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-compiler))))

(defthm rw.waterstep-list-compiler-when-not-consp
  (implies (not (consp x))
           (equal (rw.waterstep-list-compiler x world rproofs)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-list-compiler))))

(defthm rw.waterstep-list-compiler-of-cons
  (equal (rw.waterstep-list-compiler (cons a x) world rproofs)
         (cons (rw.waterstep-compiler a world rproofs)
               (rw.waterstep-list-compiler x world rproofs)))
  :hints(("Goal" :in-theory (enable definition-of-rw.waterstep-list-compiler))))

(defprojection
  :list (rw.waterstep-list-compiler x world rproofs)
  :element (rw.waterstep-compiler x world rproofs)
  :nil-preservingp t
  :already-definedp t)

(defthms-flag
  :shared-hyp (force (and (tactic.worldp world)
                          (logic.appeal-listp rproofs)))
  :thms ((clause logic.appealp-of-rw.waterstep-compiler
                 (implies (force (and (rw.waterstepp x)
                                      (rw.waterstep-okp x world)
                                      (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                               (logic.strip-conclusions rproofs))))
                          (equal (logic.appealp (rw.waterstep-compiler x world rproofs))
                                 t)))
         (clause logic.conclusion-of-rw.waterstep-compiler
                 (implies (force (and (rw.waterstepp x)
                                      (rw.waterstep-okp x world)
                                      (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                               (logic.strip-conclusions rproofs))))
                          (equal (logic.conclusion (rw.waterstep-compiler x world rproofs))
                                 (clause.clause-formula (rw.waterstep->clause x)))))
         (t logic.appeal-listp-of-rw.waterstep-list-compiler
            (implies (force (and (rw.waterstep-listp x)
                                 (rw.waterstep-list-okp x world)
                                 (subsetp (clause.clause-list-formulas (rw.waterfall-list-subgoals x))
                                          (logic.strip-conclusions rproofs))))
                     (equal (logic.appeal-listp (rw.waterstep-list-compiler x world rproofs))
                            t)))
         (t logic.strip-conclusions-of-rw.waterstep-list-compiler
            (implies (force (and (rw.waterstep-listp x)
                                 (rw.waterstep-list-okp x world)
                                 (subsetp (clause.clause-list-formulas (rw.waterfall-list-subgoals x))
                                          (logic.strip-conclusions rproofs))))
                     (equal (logic.strip-conclusions (rw.waterstep-list-compiler x world rproofs))
                            (clause.clause-list-formulas (rw.waterstep-list->clauses x))))))
  :hints(("Goal"
          :induct (rw.waterstep-induction flag x)
          :expand ((rw.waterstep-compiler x world rproofs)
                   (rw.waterfall-subgoals x)
                   (rw.waterstep-okp x world)))))

(defthms-flag
  :@contextp t
  :shared-hyp (force (and (tactic.worldp world)
                          (logic.appeal-listp rproofs)
                          (tactic.world-atblp world atbl)
                          (tactic.world-env-okp world axioms thms)
                          (equal (cdr (lookup 'if atbl)) 3)
                          (equal (cdr (lookup 'equal atbl)) 2)
                          (equal (cdr (lookup 'iff atbl)) 2)
                          (equal (cdr (lookup 'not atbl)) 1)
                          (logic.proof-listp rproofs axioms thms atbl)
                          (@obligations rw.waterstep-compiler)))
  :thms ((clause logic.proofp-of-rw.waterstep-compiler
                 (implies (force (and (rw.waterstepp x)
                                      (rw.waterstep-atblp x atbl)
                                      (rw.waterstep-okp x world)
                                      (subsetp (clause.clause-list-formulas (rw.waterfall-subgoals x))
                                               (logic.strip-conclusions rproofs))))
                          (equal (logic.proofp (rw.waterstep-compiler x world rproofs) axioms thms atbl)
                                 t)))
         (t logic.proof-listp-of-rw.waterstep-list-compiler
            (implies (force (and (rw.waterstep-listp x)
                                 (rw.waterstep-list-atblp x atbl)
                                 (rw.waterstep-list-okp x world)
                                 (subsetp (clause.clause-list-formulas (rw.waterfall-list-subgoals x))
                                          (logic.strip-conclusions rproofs))))
                     (equal (logic.proof-listp (rw.waterstep-list-compiler x world rproofs) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (rw.waterstep-induction flag x)
          :expand ((rw.waterstep-compiler x world rproofs)
                   (rw.waterfall-subgoals x)
                   (rw.waterstep-okp x world)))))

(verify-guards rw.flag-waterstep-compiler
               :hints(("Goal"
                       :in-theory (enable rw.flag-waterstep-compiler)
                       :expand ((rw.waterstep-okp x world)
                                (rw.waterfall-subgoals x)
                                (rw.stop-waterstep-okp x)))))

(verify-guards rw.waterstep-compiler)
(verify-guards rw.waterstep-list-compiler)


; Finally, there is the remaining matter of integrating the waterfall into the
; breadth-first tactic system.  We think of waterfall-tac as just applying to
; every goal.


(defund tactic.waterfall-okp (x worlds)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds))))
  (let* ((goals    (tactic.skeleton->goals x))
         (tacname  (tactic.skeleton->tacname x))
         ;; The extras are (wsteps theoryname strategy maxdepth windex), which
         ;; allows us to "recreate" the wsteps here and check they are right.
         ;; This lets us avoid a separate atbl checker as in fertilize, etc.
         (extras   (tactic.skeleton->extras x))
         (history  (tactic.skeleton->history x)))
    (and (equal tacname 'waterfall)
         (tuplep 7 extras)
         (let* ((oldgoals   (list-list-fix (tactic.skeleton->goals history)))
                (wsteps     (first extras))
                (theoryname (second extras))
                (strategy   (third extras))
                (maxdepth   (fourth extras))
                (windex     (fifth extras))
                (ufastp     (nth 5 extras))
                (cfastp     (nth 6 extras))
                (world      (tactic.find-world windex worlds)))
           (and world
                (booleanp ufastp)
                (booleanp cfastp)
                (rw.waterstep-listp wsteps)
                (equal oldgoals (rw.waterstep-list->clauses wsteps))
                (equal goals (rw.waterfall-list-subgoals wsteps))
                (not (equal goals oldgoals))
                (symbolp theoryname)
                (natp maxdepth)
                (equal wsteps
                       (rw.waterfall-list oldgoals theoryname cfastp ufastp world strategy strategy maxdepth)))))))

(defthm booleanp-of-tactic.waterfall-okp
  (equal (booleanp (tactic.waterfall-okp x worlds))
         t)
  :hints(("Goal" :in-theory (enable tactic.waterfall-okp))))



(defun rw.waterfall-list-wrapper (x theoryname cfastp ufastp world steps strategy n)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (true-list-listp x)
                              (cons-listp x)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (tactic.worldp world)
                              (natp n))))

; We introduce this stupid wrapper so that we can redefine it and report some
; timing information.

  (rw.waterfall-list x theoryname cfastp ufastp world steps strategy n))

(defund tactic.waterfall-tac (x strategy maxdepth theoryname cfastp ufastp world warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.worldp world)
                              (symbolp theoryname)
                              (booleanp cfastp)
                              (booleanp ufastp)
                              (natp maxdepth)
                              (booleanp warnp))))
  (let* ((goals      (list-list-fix (tactic.skeleton->goals x)))
         (findtheory (lookup theoryname (tactic.world->theories world)))
         (windex     (tactic.world->index world)))
    (cond ((not (consp goals))
           (and warnp
                (ACL2::cw "~s0waterfall-tac failure~s1: all clauses have already been proven.~%" *red* *black*)))
          ((not findtheory)
           (and warnp
                (ACL2::cw "~s0waterfall-tac failure~s1: no theory named ~s2 is defined.~%" *red* *black* theoryname)))
          (t
           (let* ((wsteps    (acl2::time$
                              (rw.waterfall-list-wrapper goals theoryname cfastp ufastp world strategy strategy maxdepth)))
                  (new-goals (rw.waterfall-list-subgoals wsteps))
                  (progressp (not (equal goals new-goals))))
             (cond ((not progressp)
                    (and warnp
                         (ACL2::cw "~s0waterfall-tac failure~s1: no progress was made.~%" *red* *black*)))
                   (t
                    (ACL2::prog2$
                     (ACL2::cw "; Applied waterfall to ~x0 clauses; ~x1 remain~%"
                               (fast-len goals 0)
                               (fast-len new-goals 0))
                     (tactic.extend-skeleton new-goals
                                             'waterfall
                                             (list wsteps theoryname strategy maxdepth windex ufastp cfastp)
                                             x)))))))))

(defthm forcing-tactic.skeletonp-of-tactic.waterfall-tac
  (implies (and (tactic.waterfall-tac x strategy maxdepth theoryname cfastp ufastp world warnp)
                (force (tactic.skeletonp x))
                (force (tactic.worldp world))
                (force (symbolp theoryname))
                (force (natp maxdepth)))
           (equal (tactic.skeletonp (tactic.waterfall-tac x strategy maxdepth theoryname cfastp ufastp world warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.waterfall-tac))))

(defthm forcing-tactic.waterfall-okp-of-tactic.waterfall-tac
  (implies (and (tactic.waterfall-tac x strategy maxdepth theoryname cfastp ufastp world warnp)
                (force (tactic.skeletonp x))
                (force (tactic.worldp world))
                (force (tactic.world-listp worlds))
                (force (symbolp theoryname))
                (force (booleanp cfastp))
                (force (booleanp ufastp))
                (force (natp maxdepth))
                (force (equal world (tactic.find-world (tactic.world->index world) worlds))))
           (equal (tactic.waterfall-okp
                   (tactic.waterfall-tac x strategy maxdepth theoryname cfastp ufastp world warnp)
                   worlds)
                  t))
  :hints(("Goal" :in-theory (enable tactic.waterfall-tac
                                    tactic.waterfall-okp
                                    nth))))



(defund tactic.waterfall-compile (x worlds proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.world-listp worlds)
                              (tactic.waterfall-okp x worlds)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras (tactic.skeleton->extras x))
         (wsteps (first extras))
         (windex (fifth extras))
         (world  (tactic.find-world windex worlds)))
    (rw.waterstep-list-compiler wsteps world proofs)))

(defobligations tactic.waterfall-compile
  (rw.waterstep-list-compiler))

(encapsulate
 ()
 (local (in-theory (enable tactic.waterfall-okp
                           tactic.waterfall-compile)))

 (local (ACL2::allow-fertilize t))

 (verify-guards tactic.waterfall-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.waterfall-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.waterfall-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.waterfall-compile x worlds proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.waterfall-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.waterfall-okp x worlds)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.waterfall-compile x worlds proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.waterfall-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.world-listp worlds)
                        (tactic.waterfall-okp x worlds)
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
                        (@obligations tactic.waterfall-compile)))
            (equal (logic.proof-listp (tactic.waterfall-compile x worlds proofs) axioms thms atbl)
                   t))))



