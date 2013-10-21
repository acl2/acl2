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
(include-book "skeletonp")
(include-book "colors")
(include-book "../clauses/split-bldr")
(include-book "partition")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; BOZO all this stuff belongs somewhere else.

(defthm firstn-of-nfix
  (equal (firstn (nfix n) x)
         (firstn n x))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm restn-of-nfix
  (equal (restn (nfix n) x)
         (restn n x))
  :hints(("Goal" :in-theory (enable restn))))

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

(defthm logic.term-list-list-atblp-of-list-list-fix
  (equal (logic.term-list-list-atblp (list-list-fix x) atbl)
         (logic.term-list-list-atblp x atbl))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.strip-conclusions-list-of-partition
  (equal (logic.strip-conclusions-list (partition lens x))
         (partition lens (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable partition))))

(defthm nat-listp-of-strip-lens-free
  (implies (equal (strip-lens x) free)
           (equal (nat-listp free)
                  t)))

(defthm logic.appeal-list-listp-of-partition
  (implies (force (logic.appeal-listp proofs))
           (equal (logic.appeal-list-listp (partition lens proofs))
                  t))
  :hints(("Goal" :in-theory (enable partition))))

(defthm true-list-listp-of-cdr-of-clause.split-list
  (implies (force (and (true-list-listp x)
                       (logic.term-list-listp x)))
           (equal (true-list-listp (cdr (clause.split-list liftp liftlimit splitlimit x)))
                  t))
  :hints(("Goal" :in-theory (enable clause.split-list))))

(defthm list-list-fix-when-true-list-listp
  (implies (true-list-listp x)
           (equal (list-list-fix x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.clause-list-list-formulas-of-partition
  (equal (clause.clause-list-list-formulas (partition lens x))
         (partition lens (clause.clause-list-formulas x)))
  :hints(("Goal" :in-theory (enable partition))))

(defthm logic.proof-list-listp-of-partition
  (implies (force (logic.proof-listp x axioms thms atbl))
           (equal (logic.proof-list-listp (partition lens x) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (enable partition))))




(defund tactic.split-all-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'split-all)
         (tuplep 4 extras)
         (let ((liftp      (first extras))
               (liftlimit  (second extras))
               (splitlimit (third extras))
               (lens       (fourth extras)))
           (and (booleanp liftp)
                (natp liftlimit)
                (natp splitlimit)
                (let* ((old-goals (list-list-fix (tactic.skeleton->goals history)))
                       (split     (clause.split-list liftp liftlimit splitlimit old-goals))
                       (new-goals (simple-flatten (cdr split))))
                  (and (car split)
                       (equal lens (strip-lens (cdr split)))
                       (equal goals new-goals))))))))

(defthm booleanp-of-tactic.split-all-okp
  (equal (booleanp (tactic.split-all-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.split-all-okp)
                                 ((:executable-counterpart acl2::force))))))






(defthm forcing-cons-listp-of-simple-flatten
  (implies (force (cons-list-listp x))
           (equal (cons-listp (simple-flatten x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-simple-flatten
  (implies (force (logic.term-list-list-listp x))
           (equal (logic.term-list-listp (simple-flatten x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(defund tactic.split-all-tac (liftp liftlimit splitlimit x warnp)
  (declare (xargs :guard (and (booleanp liftp)
                              (natp liftlimit)
                              (natp splitlimit)
                              (tactic.skeletonp x)
                              (booleanp warnp))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (and warnp
             (ACL2::cw "~s0Split-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*))
      (let* ((split     (clause.split-list liftp liftlimit splitlimit (list-list-fix goals)))
             (new-goals (simple-flatten (cdr split))))
        (if (not (car split))
            (and warnp
                 (ACL2::cw "~s0split-all-tac failure~s1: the clauses cannot be split further.~%" *red* *black*))
          (tactic.extend-skeleton new-goals
                                  'split-all
                                  (list liftp liftlimit splitlimit (strip-lens (cdr split)))
                                  x))))))

(defthm forcing-tactic.skeletonp-of-tactic.split-all-tac
  (implies (and (tactic.split-all-tac liftp liftlimit splitlimit x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.split-all-tac liftp liftlimit splitlimit x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.split-all-tac))))

(defthm forcing-tactic.split-all-okp-of-tactic.split-all-tac
  (implies (and (tactic.split-all-tac liftp liftlimit splitlimit x warnp)
                (force (natp liftlimit))
                (force (natp splitlimit))
                (force (booleanp liftp))
                (force (tactic.skeletonp x)))
           (equal (tactic.split-all-okp (tactic.split-all-tac liftp liftlimit splitlimit x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.split-all-tac tactic.split-all-okp))))






(defund tactic.split-all-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.split-all-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history            (tactic.skeleton->history x))
         (old-goals          (list-list-fix (tactic.skeleton->goals history)))
         (extras             (tactic.skeleton->extras x))
         (liftp              (first extras))
         (liftlimit          (second extras))
         (splitlimit         (third extras))
         (lens               (fourth extras))
         (partitioned-proofs (partition lens proofs)))
    (clause.split-list-bldr liftp liftlimit splitlimit old-goals partitioned-proofs)))

(defobligations tactic.split-all-compile
  (clause.split-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.split-all-okp tactic.split-all-compile)))

 (defthm forcing-logic.appeal-listp-of-tactic.split-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.split-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.split-all-compile x proofs))
                   t))
   :hints(("[1]Goal"
           :in-theory (disable partition-of-simple-flatten)
           :use ((:instance partition-of-simple-flatten
                            (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                                       (second (tactic.skeleton->extras x))
                                                       (third (tactic.skeleton->extras x))
                                                       (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))))

 (defthm forcing-logic.strip-conclusions-of-tactic.split-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.split-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.split-all-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x)))))
   :hints(("[1]Goal"
           :in-theory (disable partition-of-simple-flatten)
           :use ((:instance partition-of-simple-flatten
                            (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                                       (second (tactic.skeleton->extras x))
                                                       (third (tactic.skeleton->extras x))
                                                       (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.split-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.split-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.split-all-compile)))
            (equal (logic.proof-listp (tactic.split-all-compile x proofs) axioms thms atbl)
                   t))
   :hints(("[1]Goal"
           :in-theory (disable partition-of-simple-flatten)
           :use ((:instance partition-of-simple-flatten
                            (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                                       (second (tactic.skeleton->extras x))
                                                       (third (tactic.skeleton->extras x))
                                                       (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))))

 (local (defthm crock
          (implies (equal (logic.disjoin-each-formula-list
                           (logic.term-list-list-formulas (tactic.skeleton->goals x)))
                          (logic.strip-conclusions proofs))
                   (equal (len proofs)
                          (len (tactic.skeleton->goals x))))
          :hints(("goal"
                  :in-theory (disable len-of-logic.disjoin-each-formula-list)
                  :use ((:instance len-of-logic.disjoin-each-formula-list
                                   (x (logic.term-list-list-formulas (tactic.skeleton->goals x)))))))))

 (local (defthm crock2
          (equal (sum-list (strip-lens x))
                 (len (simple-flatten x)))
          :hints(("Goal" :induct (cdr-induction x)))))

 (local (ACL2::allow-fertilize t))

 (verify-guards tactic.split-all-compile
                :hints(("Goal"
                        :in-theory (disable partition-of-simple-flatten)
                        :use ((:instance partition-of-simple-flatten
                                         (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                                                    (second (tactic.skeleton->extras x))
                                                                    (third (tactic.skeleton->extras x))
                                                                    (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x))))))))))))

