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
(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund logic.flag-subtermp (flag x y)
  ;; X is a subterm of y if it occurs somewhere inside of y.  Every term is a
  ;; subterm of itself.  We treat lambda bodies as "opaque" and do not look
  ;; inside of them, so (+ 1 2) is not a subterm of ((lambda (x) (+ x (+ 1 2)))
  ;; 3), because it only occurs inside the body of a lambda.  We make no effort
  ;; to detect alpha-equivalent lambdas.
  (declare (xargs :guard (if (equal flag 'term)
                             (and (logic.termp x)
                                  (logic.termp y))
                           (and (equal flag 'list)
                                (logic.termp x)
                                (logic.term-listp y)))
                  :measure (rank y)))
  (if (equal flag 'term)
      ;; Check if x is a subterm of y.
      (cond ((logic.variablep y)
             (equal x y))
            ((logic.constantp y)
             (equal x y))
            ((logic.functionp y)
             (or (equal x y)
                 (logic.flag-subtermp 'list x (logic.function-args y))))
            ((logic.lambdap y)
             (or (equal x y)
                 (logic.flag-subtermp 'list x (logic.lambda-actuals y))))
            (t
             ;; Sneaky hack for hypless reflexivity
             (equal x y)))
    ;; Check if x is a subterm of any member of y.
    (if (consp y)
        (or (logic.flag-subtermp 'term x (car y))
            (logic.flag-subtermp 'list x (cdr y)))
      nil)))

(definlined logic.subtermp (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  (logic.flag-subtermp 'term x y))

(definlined logic.subterm-of-somep (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.term-listp y))))
  (logic.flag-subtermp 'list x y))

(defthmd definition-of-logic.subtermp
  (equal (logic.subtermp x y)
         (cond ((logic.variablep y)
                (equal x y))
               ((logic.constantp y)
                (equal x y))
               ((logic.functionp y)
                (or (equal x y)
                    (logic.subterm-of-somep x (logic.function-args y))))
               ((logic.lambdap y)
                (or (equal x y)
                    (logic.subterm-of-somep x (logic.lambda-actuals y))))
               (t
                (equal x y))))
  :rule-classes :rewrite
  :hints(("Goal" :in-theory (enable logic.subtermp
                                    logic.subterm-of-somep
                                    logic.flag-subtermp))))

(defthmd definition-of-logic.subterm-of-somep
  (equal (logic.subterm-of-somep x y)
         (if (consp y)
             (or (logic.subtermp x (car y))
                 (logic.subterm-of-somep x (cdr y)))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.subtermp
                                    logic.subterm-of-somep
                                    logic.flag-subtermp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.subtermp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.subterm-of-somep))))

(defthm logic.subterm-of-somep-when-not-consp
  (implies (not (consp x))
           (equal (logic.subterm-of-somep a x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.subterm-of-somep))))

(defthm logic.subterm-of-somep-of-cons
  (equal (logic.subterm-of-somep a (cons b y))
         (or (logic.subtermp a b)
             (logic.subterm-of-somep a y)))
  :hints(("Goal" :in-theory (enable definition-of-logic.subterm-of-somep))))



(defthms-flag
  :thms ((term booleanp-of-logic.subtermp
               (equal (booleanp (logic.subtermp x y))
                      t))
         (t booleanp-of-logic.subterm-of-somep
            (equal (booleanp (logic.subterm-of-somep x y))
                   t)))
  :hints (("Goal"
           :induct (logic.term-induction flag y)
           :in-theory (enable definition-of-logic.subtermp))))

(defthm logic.subterm-of-somep-when-memberp-is-logic.subtermp
  (implies (and (logic.subtermp a b)
                (memberp b x))
           (equal (logic.subterm-of-somep a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.subterm-of-somep-when-memberp-is-logic.subtermp-alt
  (implies (and (memberp b x)
                (logic.subtermp a b))
           (equal (logic.subterm-of-somep a x)
                  t)))

(defthm logic.subtermp-is-reflexive
  (equal (logic.subtermp x x)
         t)
  :hints(("Goal" :in-theory (enable definition-of-logic.subtermp))))



(defthms-flag
  :thms ((term logic.subtermp-is-transitive
               (implies (and (logic.subtermp x y)
                             (logic.subtermp y z))
                        (equal (logic.subtermp x z)
                               t)))
         (t logic.subterm-of-somep-when-logic.subtermp-and-logic.subterm-of-somep
            (implies (and (logic.subtermp x y)
                          (logic.subterm-of-somep y z))
                     (equal (logic.subterm-of-somep x z)
                            t))))
  :hints (("Goal"
           :induct (logic.term-induction flag z)
           :in-theory (enable definition-of-logic.subtermp))))

(defthm logic.subtermp-is-transitive-two
  (implies (and (logic.subtermp y z)
                (logic.subtermp x y))
           (equal (logic.subtermp x z)
                  t)))

(defthm logic.subterm-of-somep-when-logic.subtermp-and-logic.subterm-of-somep-alt
  (implies (and (logic.subterm-of-somep y z)
                (logic.subtermp x y))
           (equal (logic.subterm-of-somep x z)
                  t)))


;; The easiest way I could think of showing that logic.subtermp is antisymmetric was
;; to consider the size of terms.

(defthms-flag
  :thms ((term rank-when-logic.subtermp-weak
               (implies (logic.subtermp x y)
                        (equal (< (rank y) (rank x))
                               nil)))
         (t rank-when-logic.subterm-of-somep
            (implies (logic.subterm-of-somep x y)
                     (equal (< (rank x) (rank y))
                            t))))
  :hints (("Goal"
           :induct (logic.term-induction flag y)
           :in-theory (enable definition-of-logic.subtermp))))

(defthm rank-when-logic.subterm-of-somep-weak
  (implies (logic.subterm-of-somep x y)
           (equal (< (rank y) (rank x))
                  nil)))



(defthm rank-when-logic.subtermp
  (implies (logic.subtermp x y)
           (equal (< (rank x) (rank y))
                  (not (equal x y))))
  :hints(("Goal"
          :in-theory (enable definition-of-logic.subtermp))
         ("Subgoal 3"  ;; Yuck!
          :in-theory (disable rank-when-logic.subterm-of-somep)
          :use ((:instance rank-when-logic.subterm-of-somep
                           (x x)
                           (y (logic.function-args y)))))
         ("Subgoal 1"  ;; Yuck!
          :in-theory (disable rank-when-logic.subterm-of-somep)
          :use ((:instance rank-when-logic.subterm-of-somep
                           (x x)
                           (y (logic.lambda-actuals y)))))))

(defthm logic.subtermp-is-weakly-antisymmetric
  (implies (logic.subtermp x y)
           (equal (logic.subtermp y x)
                  (equal x y)))
  :hints(("Goal"
          :in-theory (disable rank-when-logic.subtermp)
          :use ((:instance rank-when-logic.subtermp)))))

(defthm logic.subtermp-of-logic.functionp
  (implies (and (force (logic.function-namep fn))
                (force (logic.term-listp args))
                (force (true-listp args)))
           (equal (logic.subtermp x (logic.function fn args))
                  (or (equal x (logic.function fn args))
                      (logic.subterm-of-somep x args))))
  :hints(("Goal" :in-theory (enable definition-of-logic.subtermp))))

(defthm logic.subtermp-of-logic.lambda
  (equal (logic.subtermp x (logic.lambda xs b ts))
         (or (equal x (logic.lambda xs b ts))
             (logic.subterm-of-somep x ts)))
  :hints(("Goal" :in-theory (enable definition-of-logic.subtermp))))





(defthm logic.subterm-of-somep-of-list-fix
  (equal (logic.subterm-of-somep a (list-fix x))
         (logic.subterm-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.subterm-of-somep-of-app
  (equal (logic.subterm-of-somep a (app x y))
         (or (logic.subterm-of-somep a x)
             (logic.subterm-of-somep a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.subterm-of-somep-of-rev
  (equal (logic.subterm-of-somep a (rev x))
         (logic.subterm-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))





(deflist logic.all-subterm-of-somep (x others)
  (logic.subterm-of-somep x others)
  :guard (and (logic.term-listp x)
              (logic.term-listp others)))

(defthm logic.all-subterm-of-somep-when-not-consp-two
  (implies (not (consp y))
           (equal (logic.all-subterm-of-somep x y)
                  (not (consp x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-of-cons-two
  (implies (logic.all-subterm-of-somep x y)
           (equal (logic.all-subterm-of-somep x (cons a y))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-of-list-fix-two
  (equal (logic.all-subterm-of-somep x (list-fix y))
         (logic.all-subterm-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-of-app-two
  (implies (logic.all-subterm-of-somep x y)
           (equal (logic.all-subterm-of-somep x (app y z))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-of-app-two-alt
  (implies (logic.all-subterm-of-somep x y)
           (equal (logic.all-subterm-of-somep x (app z y))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-of-rev-two
  (equal (logic.all-subterm-of-somep x (rev y))
         (logic.all-subterm-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-is-reflexive
  (equal (logic.all-subterm-of-somep x x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.subterm-of-somep-when-subterm-and-logic.all-subterm-of-somep
  (implies (and (logic.subterm-of-somep a x)
                (logic.all-subterm-of-somep x y))
           (equal (logic.subterm-of-somep a y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.subterm-of-somep-when-subterm-and-logic.all-subterm-of-somep-alt
  (implies (and (logic.all-subterm-of-somep x y)
                (logic.subterm-of-somep a x))
           (equal (logic.subterm-of-somep a y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-is-transitive
  (implies (and (logic.all-subterm-of-somep x y)
                (logic.all-subterm-of-somep y z))
           (equal (logic.all-subterm-of-somep x z)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.all-subterm-of-somep-is-transitive-alt
  (implies (and (logic.all-subterm-of-somep y z)
                (logic.all-subterm-of-somep x y))
           (equal (logic.all-subterm-of-somep x z)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
