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
(include-book "aux-split")
(include-book "aux-limsplit")
(include-book "if-lifting/lift")
(include-book "if-lifting/limlift")
(include-book "clean-clauses")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO move this stuff to clean-clauses

(defthm true-listp-of-clause.clean-clauses
  (equal (true-listp (clause.clean-clauses x))
         t)
  :hints(("Goal" :in-theory (enable clause.clean-clauses))))

(defthm forcing-logic.term-list-list-atblp-of-remove-supersets1
  (implies (force (and (logic.term-list-list-atblp x atbl)
                       (logic.term-list-list-atblp acc atbl)))
           (equal (logic.term-list-list-atblp (remove-supersets1 x acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm forcing-logic.term-list-list-atblp-of-remove-supersets
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (logic.term-list-list-atblp (remove-supersets x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets))))

(defthm forcing-logic.term-list-list-atblp-of-remove-duplicates-list
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (logic.term-list-list-atblp (remove-duplicates-list x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-clause.remove-absurd-terms-from-clauses
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (logic.term-list-list-atblp (clause.remove-absurd-terms-from-clauses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-list-atblp-of-third-of-clause.clean-clauses
  (implies (force (and (logic.term-list-listp x)
                       (logic.term-list-list-atblp x atbl)
                       (equal 1 (cdr (lookup 'not atbl)))))
           (equal (logic.term-list-list-atblp (third (clause.clean-clauses x)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.clean-clauses disabled-equal))))





(defthm forcing-clause.simple-term-list-listp-of-remove-supersets1
  (implies (force (and (clause.simple-term-list-listp x)
                       (clause.simple-term-list-listp acc)))
           (equal (clause.simple-term-list-listp (remove-supersets1 x acc))
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm forcing-clause.simple-term-list-listp-of-remove-supersets
  (implies (force (clause.simple-term-list-listp x))
           (equal (clause.simple-term-list-listp (remove-supersets x))
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets))))

(defthm forcing-clause.simple-term-list-listp-of-remove-duplicates-list
  (implies (force (clause.simple-term-list-listp x))
           (equal (clause.simple-term-list-listp (remove-duplicates-list x))
                  t))
  :hints(("Goal" :in-theory (enable remove-duplicates-list))))

(defthm forcing-clause.simple-term-list-listp-of-clause.remove-absurd-terms-from-clauses
  (implies (force (clause.simple-term-list-listp x))
           (equal (clause.simple-term-list-listp (clause.remove-absurd-terms-from-clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-clause.simple-term-list-listp-of-clause.remove-complement-clauses
  (implies (force (clause.simple-term-list-listp x))
           (equal (clause.simple-term-list-listp (clause.remove-complement-clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-clause.simple-term-list-listp-of-clause.remove-obvious-clauses
  (implies (force (clause.simple-term-list-listp x))
           (equal (clause.simple-term-list-listp (clause.remove-obvious-clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-clause.simple-termp-of-clause.negative-term-guts
  (implies (force (and (clause.simple-termp x)
                       (clause.negative-termp x)
                       (logic.termp x)))
           (equal (clause.simple-termp (clause.negative-term-guts x))
                  t))
  :hints(("Goal" :in-theory (enable clause.negative-termp
                                    clause.negative-term-guts))))

(defthm forcing-clause.simple-termp-of-clause.normalize-nots-term
  (implies (force (and (clause.simple-termp x)
                       (logic.termp x)))
           (equal (clause.simple-termp (clause.normalize-nots-term x))
                  t))
  :hints(("Goal" :in-theory (enable clause.normalize-nots-term))))

(defthm forcing-clause.simple-term-listp-of-clause.normalize-nots-term-list
  (implies (force (and (clause.simple-term-listp x)
                       (logic.term-listp x)))
           (equal (clause.simple-term-listp (clause.normalize-nots-term-list x))
                  t))
  :hints(("Goal" :in-theory (enable clause.normalize-nots-term-list))))

(defthm forcing-clause.simple-term-list-listp-of-clause.normalize-nots-clauses
  (implies (force (and (clause.simple-term-list-listp x)
                       (logic.term-list-listp x)))
           (equal (clause.simple-term-list-listp (clause.normalize-nots-clauses x))
                  t))
  :hints(("Goal" :in-theory (enable clause.normalize-nots-clauses))))

(defthm clause.simple-term-list-listp-of-third-of-clause.clean-clauses
  (implies (force (and (clause.simple-term-list-listp x)
                       (logic.term-list-listp x)))
           (equal (clause.simple-term-list-listp (third (clause.clean-clauses x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.clean-clauses))))




(defund clause.split (liftp liftlimit splitlimit x)
  ;; Clause Splitting.
  ;;
  ;; Clause splitting is a fundamental reduction which splits up a single goal
  ;; clause into several, simpler clauses based on its if-expressions.  Proving
  ;; all of these simpler clauses is sufficient to show that the original clause
  ;; was true.
  ;;
  ;; Clause splitting is implemented in three phases:
  ;;
  ;;   1.  A "lifting" pass is used to transform literals in the clause such as
  ;;       (foo (if a b c)) into the form (if (foo a) (foo b) (foo c)).
  ;;
  ;;   2.  A "splitting" pass is then used to split the clause into subclauses,
  ;;       based on the top-level tests of its literals.
  ;;
  ;;   3.  A "cleanup" pass finally eliminates any obvious and redundant
  ;;       subclauses, eliminates useless literals, normalizes nots, and the
  ;;       like.
  ;;
  ;; We return a pair of the form (progressp . new-clauses).
  ;;
  ;; Controlling Splitting.
  ;;
  ;; The lifting/splitting passes are occasionally too aggressive and can result
  ;; in excessive numbers of clauses being created.  This is especially apparent
  ;; during the early stages of bootstrapping, when proof sizes are at a premium.
  ;; To address this, the liftp, liftlimit, and splitlimit options can be used.
  ;;
  ;; Liftp is a boolean flag which can be set to nil in order to completely
  ;; stop any if-lifting from occurring.  This can result in fewer top-level
  ;; if-expressions, which means fewer literals being split.
  ;;
  ;; Alternately, when liftp is enabled, a liftlimit can be imposed to reduce
  ;; the number of if-expressions which will be percolated up through other
  ;; function calls, which again has the effect of reducing the number of
  ;; top-level ifs that will be generated.  Use 0 to indicate "no limit", or
  ;; any positive number to impose a limit.
  ;;
  ;; Finally, the splitlimit can be used to stop the splitting pass early,
  ;; before it has had a chance to process all of the top-level tests.  As with
  ;; the liftlimit, you can use 0 to indicate "no limit", or any positive
  ;; number to impose a limit.
  ;;
  ;; Despite all these features, a nice theorem about clause splitting is the
  ;; following: when unlimited lifting and splitting are allowed, the splitting
  ;; process is "complete."  That is, the resulting clauses will not have any
  ;; if-expressions anywhere within them.
  (declare (xargs :guard (and (logic.term-listp x)
                              (true-listp x)
                              (consp x)
                              (natp liftlimit)
                              (natp splitlimit))))
  (let* ((lifted-clause     (if liftp
                                (if (equal liftlimit 0)
                                    (clause.fast-lift-term-list$ x nil)
                                  (clause.fast-limlift-term-list$ x liftlimit nil))
                              x))
         (split-clauses     (if (equal splitlimit 0)
                                (clause.simple-split lifted-clause)
                              (clause.simple-limsplit lifted-clause splitlimit)))
         (clean-tuple       (clause.fast-clean-clauses split-clauses))
         (clean-unprovablep (first clean-tuple))
         (clean-progressp   (second clean-tuple))
         (clean-clauses     (third clean-tuple))
         (progressp         (or ;; We are happy as long as there has been any kind of progress.
                                ;; It's particularly easy to check for cleaning progress.
                                clean-progressp

                                ;; If splitting made no progress, it returns (list (rev lifted-clause)).
                                ;; The below check is the same as
                                ;;   (not (equal split-clauses) (list (rev lifted-clause)))
                                ;;
                                ;; But we just optimize for some common cases.  First, if 0 or 2+ clauses
                                ;; have been returned, clearly some progress has been made.  Also, if the
                                ;; returned clause is not the same length, then again we have progress.
                                (not split-clauses)
                                (consp (cdr split-clauses))
                                (not (same-lengthp (car split-clauses) lifted-clause))
                                (not (equal split-clauses (list (fast-rev lifted-clause))))

                                ;; Finally, lifting might have made progress without causing splits.
                                ;; For example, (foo (if a b b)) becomes (foo b) when lifted.  If there
                                ;; has been no progress, then the lifted-clause will be the same as
                                ;; (rev x).  We check this below.

                                (and liftp
                                     (or (not (same-lengthp lifted-clause x))
                                         (not (equal lifted-clause (fast-rev x))))))))
    (ACL2::prog2$
     ;; As a convenience, we print a warning if an unprovable clause is discovered.
     ;; But this really doesn't bother us -- who cares if the user can't prove the
     ;; subgoal.  That's his or her problem.  It doesn't affect our soundness.
     (if clean-unprovablep
         (ACL2::cw ";; Unprovable clause discovered in clause.split: ~%~x0~%" (fast-rev lifted-clause))
       nil)
     (cons progressp clean-clauses))))

(defthm true-listp-of-clause.split
  (implies (force (and (logic.term-listp x)
                       (true-listp x)))
           (equal (true-listp (clause.split liftp liftlimit splitlimit x))
                  t))
  :hints(("Goal" :in-theory (enable clause.split))))

(defthm forcing-logic.term-list-listp-of-cdr-of-clause.split
  (implies (force (and (logic.term-listp x)
                       (true-listp x)))
           (equal (logic.term-list-listp (cdr (clause.split liftp liftlimit splitlimit x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.split))))

(defthm forcing-logic.term-list-list-atblp-of-cdr-of-clause.split
  (implies (force (and (logic.term-listp x)
                       (logic.term-list-atblp x atbl)
                       (true-listp x)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-list-atblp (cdr (clause.split liftp limitlimit splitlimit x)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.split))))

(defthm forcing-cons-listp-of-cdr-of-clause.split
  (implies (force (and (consp x)
                       (true-listp x)
                       (logic.term-listp x)))
           (equal (cons-listp (cdr (clause.split liftp liftlimit splitlimit x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.split))))

(defthm forcing-clause.simple-term-list-listp-of-cdr-of-clause.split-of-clause.lift-clause
  ;; This is the claim that splitting is complete.
  (implies (force (and (logic.term-listp x)
                       (clause.lifted-term-listp x)))
           (equal (clause.simple-term-list-listp (cdr (clause.split t 0 0 x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.split))))




(defund clause.split-list (liftp liftlimit splitlimit x)
  ;; We are given a list of clauses, x, to try to split.  We return a pair,
  ;; (progressp . new-clauses), where progressp is set if any of the clauses
  ;; can be split, and new-clauses are a list of clause lists.
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (true-list-listp x)
                              (cons-listp x)
                              (natp liftlimit)
                              (natp splitlimit))))
  (if (consp x)
      (ACL2::prog2$ (ACL2::cw "; Splitting clause ~x0.~%" (fast-len x 0))
                    (let ((split-car (clause.split liftp liftlimit splitlimit (car x)))
                          (split-cdr (clause.split-list liftp liftlimit splitlimit (cdr x))))
                      (cons (or (car split-car)
                                (car split-cdr))
                            (cons (cdr split-car)
                                  (cdr split-cdr)))))
    (cons nil nil)))

(defthm true-listp-of-cdr-of-clause.split-list
  (equal (true-listp (cdr (clause.split-list liftp liftlimit splitlimit x)))
         t)
  :hints(("Goal" :in-theory (enable clause.split-list))))

(defthm clause.split-list-when-not-consp
  (implies (not (consp x))
           (equal (clause.split-list liftp liftlimit splitlimit x)
                  (cons nil nil)))
  :hints(("Goal" :in-theory (enable clause.split-list))))

(defthm clause.split-list-of-cons
  (equal (clause.split-list liftp liftlimit splitlimit (cons a x))
         (cons (or (car (clause.split liftp liftlimit splitlimit a))
                   (car (clause.split-list liftp liftlimit splitlimit x)))
               (cons (cdr (clause.split liftp liftlimit splitlimit a))
                     (cdr (clause.split-list liftp liftlimit splitlimit x)))))
  :hints(("Goal" :in-theory (enable clause.split-list))))

(deflist logic.term-list-list-listp (x)
  ;; BOZO find me a home
  (logic.term-list-listp x)
  :elementp-of-nil t)

(deflist logic.term-list-list-list-atblp (x atbl)
  ;; BOZO find me a home
  (logic.term-list-list-atblp x atbl)
  :guard (and (logic.term-list-list-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil t)

(defthm forcing-logic.term-list-list-listp-of-cdr-of-clause.split-list
  (implies (force (and (logic.term-list-listp x)
                       (true-list-listp x)))
           (equal (logic.term-list-list-listp (cdr (clause.split-list liftp liftlimit splitlimit x)))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-list-atblp-of-cdr-of-clause.split-list
  (implies (force (and (logic.term-list-listp x)
                       (logic.term-list-list-atblp x atbl)
                       (true-list-listp x)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-list-list-atblp (cdr (clause.split-list liftp liftlimit splitlimit x)) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(deflist cons-list-listp (x)
  ;; BOZO find me a home
  (cons-listp x)
  :elementp-of-nil t)

(defthm forcing-cons-list-listp-of-cdr-of-clause.split-list
  (implies (force (and (cons-listp x)
                       (true-list-listp x)
                       (logic.term-list-listp x)))
           (equal (cons-list-listp (cdr (clause.split-list liftp liftlimit splitlimit x)))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
