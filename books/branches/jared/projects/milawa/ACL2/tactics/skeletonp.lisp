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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Proof skeletons.
;;
;; Skeletons are used by our tactics to keep track of our progress and our
;; remaining obligations during a goal-directed proof attempt.
;;
;; Each skeleton includes a list of goals, which are clauses, which we still
;; need to prove.  If this list is empty, we have proven everything we wanted
;; to show and we are done.  Otherwise, we should try to apply more tactics to
;; finish the proof.
;;
;; When we begin a proof attempt and we want to prove some clause, Phi, we
;; create an "initial skeleton" whose only goal is Phi.  Each time we apply a
;; tactic, we create an "extended skeleton" which aggregates:
;;
;;   - A new set of goals to prove,
;;   - The skeleton for our current goals,
;;   - The name of the tactic we used,
;;   - Any additional information the tactic needs to prove the current
;;     goals, given proofs of the new goals.
;;
;; We represent skeletons as simple tuples of the form (goals tacname extras
;; history), and the initial skeleton uses nil for its name and extras.

(defund tactic.skeletonp (x)
  (declare (xargs :guard t))
  (and (tuplep 4 x)
       (let ((goals   (first x))
             (tacname (second x))
             (history (fourth x)))
         (and (logic.term-list-listp goals)
              (cons-listp goals)
              (true-listp goals)
              (symbolp tacname)
              (or (not tacname)
                  (tactic.skeletonp history))))))

(definlined tactic.skeleton->goals (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (first x))

(definlined tactic.skeleton->tacname (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (second x))

(definlined tactic.skeleton->extras (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (third x))

(definlined tactic.skeleton->history (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (fourth x))



(defthm booleanp-of-tactic.skeletonp
  (equal (booleanp (tactic.skeletonp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeletonp))))

(defthm forcing-logic.term-list-listp-of-tactic.skeleton->goals
  (implies (force (tactic.skeletonp x))
           (equal (logic.term-list-listp (tactic.skeleton->goals x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeletonp tactic.skeleton->goals))))

(defthm forcing-cons-listp-of-tactic.skeleton->goals
  (implies (force (tactic.skeletonp x))
           (equal (cons-listp (tactic.skeleton->goals x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeletonp tactic.skeleton->goals))))

(defthm forcing-true-listp-of-tactic.skeleton->goals
  (implies (force (tactic.skeletonp x))
           (equal (true-listp (tactic.skeleton->goals x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeletonp tactic.skeleton->goals))))

(defthm forcing-symbolp-of-tactic.skeleton->tacname
  (implies (force (tactic.skeletonp x))
           (equal (symbolp (tactic.skeleton->tacname x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeletonp tactic.skeleton->tacname))))

(defthm forcing-tactic.skeletonp-of-tactic.skeleton->history
  (implies (and (tactic.skeleton->tacname x)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.skeleton->history x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeletonp
                                    tactic.skeleton->history
                                    tactic.skeleton->tacname))))

(defthm rank-of-tactic.skeleton->history-when-tactic.skeleton->tacname
  (implies (tactic.skeleton->tacname x)
           (< (rank (tactic.skeleton->history x))
              (rank x)))
  :hints(("Goal" :in-theory (enable tactic.skeleton->tacname tactic.skeleton->history))))




(definlined tactic.initial-skeleton (goals)
  (declare (xargs :guard (and (logic.term-list-listp goals)
                              (cons-listp goals)
                              (true-listp goals))))
  (list goals nil nil nil))

(defthm tactic.skeleton->goals-of-tactic.initial-skeleton
  (equal (tactic.skeleton->goals (tactic.initial-skeleton goals))
         goals)
  :hints(("Goal" :in-theory (enable tactic.initial-skeleton tactic.skeleton->goals))))

(defthm tactic.skeleton->tacname-of-tactic.initial-skeleton
  (equal (tactic.skeleton->tacname (tactic.initial-skeleton goals))
         nil)
  :hints(("Goal" :in-theory (enable tactic.initial-skeleton tactic.skeleton->tacname))))

(defthm forcing-tactic.skeletonp-of-tactic.initial.skeleton
  (implies (force (and (logic.term-list-listp goals)
                       (cons-listp goals)
                       (true-listp goals)))
           (equal (tactic.skeletonp (tactic.initial-skeleton goals))
                  t))
  :hints(("Goal" :in-theory (enable tactic.initial-skeleton tactic.skeletonp))))




(definlined tactic.extend-skeleton (goals tacname extras history)
  (declare (xargs :guard (and (logic.term-list-listp goals)
                              (cons-listp goals)
                              (true-listp goals)
                              (symbolp tacname)
                              tacname
                              (tactic.skeletonp history))))
  (list goals tacname extras history))

(defthm tactic.skeleton->goals-of-tactic.extend-skeleton
  (equal (tactic.skeleton->goals (tactic.extend-skeleton goals tacname extras history))
         goals)
  :hints(("Goal" :in-theory (enable tactic.extend-skeleton tactic.skeleton->goals))))

(defthm tactic.skeleton->tacname-of-tactic.extend-skeleton
  (equal (tactic.skeleton->tacname (tactic.extend-skeleton goals tacname extras history))
         tacname)
  :hints(("Goal" :in-theory (enable tactic.extend-skeleton tactic.skeleton->tacname))))

(defthm tactic.skeleton->extras-of-tactic.extend-skeleton
  (equal (tactic.skeleton->extras (tactic.extend-skeleton goals tacname extras history))
         extras)
  :hints(("Goal" :in-theory (enable tactic.extend-skeleton tactic.skeleton->extras))))

(defthm tactic.skeleton->history-of-tactic.extend-skeleton
  (equal (tactic.skeleton->history (tactic.extend-skeleton goals tacname extras history))
         history)
  :hints(("Goal" :in-theory (enable tactic.extend-skeleton tactic.skeleton->history))))

(defthm forcing-tactic.skeletonp-of-tactic.extend.skeleton
  (implies (force (and (logic.term-list-listp goals)
                       (cons-listp goals)
                       (true-listp goals)
                       (symbolp tacname)
                       tacname
                       (tactic.skeletonp history)))
           (equal (tactic.skeletonp (tactic.extend-skeleton goals tacname extras history))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeletonp tactic.extend-skeleton))))




(defund tactic.original-conclusions (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (if (tactic.skeleton->tacname x)
      (tactic.original-conclusions (tactic.skeleton->history x))
    (tactic.skeleton->goals x)))

(defthm forcing-logic.term-list-listp-of-tactic.original-conclusion
  (implies (force (tactic.skeletonp x))
           (equal (logic.term-list-listp (tactic.original-conclusions x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.original-conclusions))))

(defthm forcing-cons-listp-of-tactic.original-conclusion
  (implies (force (tactic.skeletonp x))
           (equal (cons-listp (tactic.original-conclusions x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.original-conclusions))))

(defthm forcing-true-listp-of-tactic.original-conclusion
  (implies (force (tactic.skeletonp x))
           (equal (true-listp (tactic.original-conclusions x))
                  t))
  :hints(("Goal" :in-theory (enable tactic.original-conclusions))))

(defthm tactic.original-conclusions-of-tactic.initial-skeleton
  (equal (tactic.original-conclusions (tactic.initial-skeleton goals))
         goals)
  :hints(("Goal" :in-theory (enable tactic.original-conclusions))))

(defthm forcing-tactic.original-conclusions-of-tactic.extend-skeleton
  (implies (force tacname)
           (equal (tactic.original-conclusions (tactic.extend-skeleton goals tacname extras history))
                  (tactic.original-conclusions history)))
  :hints(("Goal" :in-theory (enable tactic.original-conclusions))))




(defund tactic.skeleton-atblp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.arity-tablep atbl))))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (history (tactic.skeleton->history x)))
    (and (logic.term-list-list-atblp goals atbl)
         (or (not tacname)
             (tactic.skeleton-atblp history atbl)))))

(defthm booleanp-of-tactic.skeleton-atbp
  (equal (booleanp (tactic.skeleton-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton-atblp))))

(defthm forcing-logic.term-list-list-atblp-of-tactic.skeleton->goals
  (implies (force (tactic.skeleton-atblp x atbl))
           (equal (logic.term-list-list-atblp (tactic.skeleton->goals x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeleton-atblp))))

(defthm forcing-tactic.skeleton-atblp-of-tactic.skeleton->history
  (implies (force (and (tactic.skeleton-atblp x atbl)
                       (tactic.skeleton->tacname x)))
           (equal (tactic.skeleton-atblp (tactic.skeleton->history x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (tactic.skeleton-atblp)
                                 (forcing-logic.term-list-list-atblp-of-tactic.skeleton->goals)))))

(defthm forcing-tactic.skeleton-atblp-of-tactic.initial.skeleton
  (implies (force (logic.term-list-list-atblp goals atbl))
           (equal (tactic.skeleton-atblp (tactic.initial-skeleton goals) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeleton-atblp))))

(defthm forcing-tactic.skeleton-atblp-of-tactic.extend.skeleton
  (implies (force (and (logic.term-list-list-atblp goals atbl)
                       (tactic.skeleton-atblp history atbl)))
           (equal (tactic.skeleton-atblp (tactic.extend-skeleton goals tacname extras history) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (tactic.skeleton-atblp)
                                 (forcing-logic.term-list-list-atblp-of-tactic.skeleton->goals
                                  forcing-tactic.skeleton-atblp-of-tactic.skeleton->history)))))

(defthm forcing-logic.term-list-list-atblp-of-tactic.original-conclusion
  (implies (force (tactic.skeleton-atblp x atbl))
           (equal (logic.term-list-list-atblp (tactic.original-conclusions x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.original-conclusions))))




(defund tactic.skeleton->len (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (if (tactic.skeleton->tacname x)
      (+ 1 (tactic.skeleton->len (tactic.skeleton->history x)))
    1))

(defthm natp-of-tactic.skeleton->len
  (equal (natp (tactic.skeleton->len x))
         t)
  :hints(("Goal" :in-theory (enable tactic.skeleton->len))))

(defthm tactic.skeleton->len-nonzero
  (equal (equal 0 (tactic.skeleton->len x))
         nil)
  :hints(("Goal" :in-theory (enable tactic.skeleton->len))))

(defthm tactic.skeleton->len-when-not-tacname
  (implies (not (tactic.skeleton->tacname x))
           (equal (tactic.skeleton->len x)
                  1))
  :hints(("Goal" :in-theory (enable tactic.skeleton->len))))




(defund logic.slow-term-list-list-arities (x)
  (declare (xargs :guard (logic.term-list-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (logic.slow-term-list-list-arities (cdr x))
           (logic.slow-term-list-arities (car x)))
    nil))

(defund logic.term-list-list-arities (x acc)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (true-listp acc))))
  (if (consp x)
      (logic.term-list-list-arities (cdr x)
                                  (logic.term-list-arities (car x) acc))
    acc))

(defthm true-listp-of-logic.term-list-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (logic.term-list-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable logic.term-list-list-arities))))

(defthm logic.term-list-list-arities-removal
  (implies (force (true-listp acc))
           (equal (logic.term-list-list-arities x acc)
                  (app (logic.slow-term-list-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable logic.term-list-list-arities
                                    logic.slow-term-list-list-arities))))

(defthm logic.slow-term-list-list-arities-correct
  (implies (force (logic.term-list-listp x))
           (equal (logic.arities-okp (logic.slow-term-list-list-arities x) atbl)
                  (logic.term-list-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((logic.term-list-list-atblp x atbl)
                   (logic.slow-term-list-list-arities x)))))



(defund tactic.slow-skeleton-arities (x)
  (declare (xargs :guard (tactic.skeletonp x)
                  :measure (rank x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (history (tactic.skeleton->history x)))
    (if (not tacname)
        (logic.slow-term-list-list-arities goals)
      (app (tactic.slow-skeleton-arities history)
           (logic.slow-term-list-list-arities goals)))))

(defund tactic.skeleton-arities (x acc)
   (declare (xargs :guard (and (tactic.skeletonp x)
                               (true-listp acc))))
   (let ((goals   (tactic.skeleton->goals x))
         (tacname (tactic.skeleton->tacname x))
         (history (tactic.skeleton->history x)))
     (if (not tacname)
         (logic.term-list-list-arities goals acc)
       (tactic.skeleton-arities history
                                (logic.term-list-list-arities goals acc)))))

(defthm true-listp-of-tactic.skeleton-arities
  (implies (force (true-listp acc))
           (equal (true-listp (tactic.skeleton-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable tactic.skeleton-arities))))

(defthm tactic.skeleton-arities-removal
  (implies (force (true-listp acc))
           (equal (tactic.skeleton-arities x acc)
                  (app (tactic.slow-skeleton-arities x) acc)))
  :hints(("Goal" :in-theory (enable tactic.skeleton-arities
                                    tactic.slow-skeleton-arities))))

(defthm logic.slow-skeleton-arities-correct
  (implies (force (tactic.skeletonp x))
           (equal (logic.arities-okp (tactic.slow-skeleton-arities x) atbl)
                  (tactic.skeleton-atblp x atbl)))
  :hints(("Goal"
          :induct (tactic.skeleton-atblp x atbl)
          :expand ((tactic.slow-skeleton-arities x)
                   (tactic.skeleton-atblp x atbl))
          :in-theory (e/d (tactic.skeleton-atblp)
                          (FORCING-TACTIC.SKELETON-ATBLP-OF-TACTIC.SKELETON->HISTORY
                           FORCING-LOGIC.TERM-LIST-LIST-ATBLP-OF-TACTIC.SKELETON->GOALS
                           )))))

(defund tactic.fast-skeleton-atblp (x atbl)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.arity-tablep atbl))))
  (logic.fast-arities-okp (tactic.skeleton-arities x nil) atbl))

(defthm tactic.fast-skeleton-atblp-correct
  (implies (and (force (tactic.skeletonp x))
                (force (mapp atbl)))
           (equal (tactic.fast-skeleton-atblp x atbl)
                  (tactic.skeleton-atblp x atbl)))
  :hints(("Goal" :in-theory (enable tactic.fast-skeleton-atblp))))
