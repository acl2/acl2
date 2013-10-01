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


;; (logic.formulap x) recognizes the encoded formulas of our logic.
;; Formulas are either:
;;
;;   - Equalities between terms t1 = t2, written as ('pequal* t1 t2),
;;   - Negations of other formulas ~F, written as ('pnot* F), or
;;   - Disjunctions of other formulas F v G, written as ('por* F G).

(defund logic.formulap (x)
  (declare (xargs :guard t))
  (cond ((equal (first x) 'pequal*)
         (and (tuplep 3 x)
              (logic.termp (second x))
              (logic.termp (third x))))
        ((equal (first x) 'pnot*)
         (and (tuplep 2 x)
              (logic.formulap (second x))))
        ((equal (first x) 'por*)
         (and (tuplep 3 x)
              (logic.formulap (second x))
              (logic.formulap (third x))))
        (t nil)))

(defthm booleanp-of-logic.formulap
  (equal (booleanp (logic.formulap x))
         t)
  :hints(("Goal" :in-theory (enable logic.formulap))))

(defthm logic.formulap-when-not-consp
  (implies (not (consp x))
           (equal (logic.formulap x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.formulap))))

(deflist logic.formula-listp (x)
  (logic.formulap x)
  :elementp-of-nil nil)

(defthm forcing-logic.formula-listp-of-app
  ;; BOZO, I prefer this more aggressive rule for app.  Maybe we want to add
  ;; an :aggressivep flag to deflist to support this?
  (implies (and (force (logic.formula-listp x))
                (force (logic.formula-listp y)))
           (equal (logic.formula-listp (app x y))
                  t)))

(in-theory (disable logic.formula-listp-of-app))

(defthm logic.formulap-of-second-when-logic.formula-listp
  ;; BOZO consider adding something like this to deflist.
  (implies (logic.formula-listp x)
           (equal (logic.formulap (second x))
                  (consp (cdr x)))))


(defthm logic.formula-listp-of-ordered-subsetp
  ;; BOZO consider reorganizing so that deflist can know about this
  (implies (and (ordered-subsetp x y)
                (logic.formula-listp y))
           (equal (logic.formula-listp x)
                  t)))


(deflist logic.formula-list-listp (x)
  (logic.formula-listp x)
  :elementp-of-nil t)

(defthm forcing-logic.formula-listp-of-simple-flatten
  (implies (force (logic.formula-list-listp x))
           (equal (logic.formula-listp (simple-flatten x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(encapsulate
 ()
 ;; Theorem: the formulas and terms are distinct.  This is true because we have
 ;; required that the special symbols pequal*, pnot*, and por* are not allowed
 ;; to be function names.
 (defthm lemma-1-for-logic.formulap-when-logic.termp
   (implies (logic.formulap x)
            (or (equal (first x) 'pequal*)
                (equal (first x) 'pnot*)
                (equal (first x) 'por*)))
   :rule-classes nil
   :hints(("Goal" :in-theory (enable logic.formulap))))

 (defthm lemma-2-for-logic.formulap-when-logic.termp
   (implies (logic.termp x)
            (or (not (first x))
                (equal (first x) 'quote)
                (logic.function-namep (first x))
                (consp (first x))))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (e/d (definition-of-logic.termp logic.variablep logic.constantp)
                           (logic.lambdap-when-not-anything-else-maybe-expensive)))))

 (defthm logic.formulap-when-logic.termp
   (implies (logic.termp x)
            (equal (logic.formulap x)
                   nil))
   :hints(("Goal" :use ((:instance lemma-1-for-logic.formulap-when-logic.termp)
                        (:instance lemma-2-for-logic.formulap-when-logic.termp))))))

(defthm logic.termp-when-logic.formulap
  (implies (logic.formulap x)
           (equal (logic.termp x)
                  nil)))



(definlined logic.fmtype (x)
  ;; Returns the type of the formula, i.e., pequal*, pnot*, or por*.
  (declare (xargs :guard (logic.formulap x)
                  :guard-hints(("Goal" :in-theory (enable logic.formulap)))))
  (first x))



(defthmd logic.fmtype-normalizer-cheap
  ;; BOZO i am really doubting that we want this stupid rule.
  ;; BOZO try to disable it
  ;; BOZO trying to disable it; took it out of the Milawa model
  ;;
  ;; We occassionally write functions that need to consider what kind of formula
  ;; they have been given.  Such functions might be written something like this:
  ;;
  ;; (cond ((equal (logic.fmtype x) 'por*) ...)
  ;;       ((equal (logic.fmtype x) 'pnot*) ...)
  ;;       (t ...))
  ;;
  ;; In this "otherwise" case, we would like to know that the logic.fmtype of x is
  ;; actually 'pequal*.  (This will be true as long as we can show that x is a
  ;; logic.formulap.)  Unfortunately, it's hard to actually get this to
  ;; happen, because we usually see this as our goal:
  ;;
  ;; (implies (and (not (equal (logic.fmtype x) 'por*))
  ;;               (not (equal (logic.fmtype x) 'pnot*))
  ;;               ...)
  ;;          ...)
  ;;
  ;; Unfortunately there is no easy way to target these hypotheses with a rewrite
  ;; rule.  I call this the "logic.fmtype normalization problem" and discuss a few
  ;; solutions to it in the file three-values.lisp found in the junk directory.
  ;;
  ;; I have not found any solution which is really acceptable for all cases.  So,
  ;; I try to write such functions using the case structure above, that is, where
  ;; the 'pequal* case is always the implicit one.  That way, we don't need to
  ;; actually normalize the other cases, and we can get away with just the rule
  ;; logic.fmtype-normalizer-cheap.
  (implies (and (force (logic.formulap x))
                (not (equal (logic.fmtype x) 'por*)))
           (equal (equal (logic.fmtype x) 'pnot*)
                  (not (equal (logic.fmtype x) 'pequal*))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.formulap logic.fmtype))))




(definlined logic.pequal (a b)
  ;; Constructs an equality formula, i.e., a = b
  (declare (xargs :guard (and (logic.termp a)
                              (logic.termp b))))
  (list 'pequal* a b))

(definlined logic.pnot (a)
  ;; Constructs a negation formula, i.e., !a
  (declare (xargs :guard (logic.formulap a)))
  (list 'pnot* a))

(definlined logic.por (a b)
  ;; Constructs a disjunction formula, i.e., a v b
  (declare (xargs :guard (and (logic.formulap a)
                              (logic.formulap b))))
  (list 'por* a b))

(in-theory (disable (:e logic.pequal)))
(in-theory (disable (:e logic.pnot)))
(in-theory (disable (:e logic.por)))



(defthm logic.pequal-under-iff
  (iff (logic.pequal x y)
       t)
  :hints(("Goal" :in-theory (enable logic.pequal))))

(defthm logic.pnot-under-iff
  (iff (logic.pnot x)
       t)
  :hints(("Goal" :in-theory (enable logic.pnot))))

(defthm logic.por-under-iff
  (iff (logic.por x y)
       t)
  :hints(("Goal" :in-theory (enable logic.por))))



(definlined logic.=lhs (x)
  ;; Retrieves lhs from lhs = rhs.
  (declare (xargs :guard (and (logic.formulap x)
                              (equal (logic.fmtype x) 'pequal*))
                  :guard-hints(("Goal" :in-theory (enable logic.formulap
                                                          logic.fmtype)))))
  (second x))

(definlined logic.=rhs (x)
  ;; Retrieves rhs from lhs = rhs.
  (declare (xargs :guard (and (logic.formulap x)
                              (equal (logic.fmtype x) 'pequal*))
                  :guard-hints(("Goal" :in-theory (enable logic.formulap
                                                          logic.fmtype)))))
  (third x))

(definlined logic.~arg (x)
  ;; Retrieves F from !F.
  (declare (xargs :guard (and (logic.formulap x)
                              (equal (logic.fmtype x) 'pnot*))
                  :guard-hints(("Goal" :in-theory (enable logic.formulap
                                                          logic.fmtype)))))
  (second x))

(definlined logic.vlhs (x)
  ;; Retrieves lhs from lhs v rhs.
  (declare (xargs :guard (and (logic.formulap x)
                              (equal (logic.fmtype x) 'por*))
                  :guard-hints(("Goal" :in-theory (enable logic.formulap
                                                          logic.fmtype)))))
  (second x))

(definlined logic.vrhs (x)
  ;; Retrieves rhs from lhs v rhs.
  (declare (xargs :guard (and (logic.formulap x)
                              (equal (logic.fmtype x) 'por*))
                  :guard-hints(("Goal" :in-theory (enable logic.formulap
                                                          logic.fmtype)))))
  (third x))





;; Measure Theorems for Recursion on Formulas

(defthm rank-of-logic.=lhs-strong
  ;; BOZO we used to use case-split on all these rank-strong theormes;
  ;; trying to get rid of it.
  (implies (equal (logic.fmtype x) 'pequal*)
           (equal (< (rank (logic.=lhs x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.=lhs logic.fmtype logic.formulap))))

(defthm rank-of-logic.=rhs-strong
  (implies (equal (logic.fmtype x) 'pequal*)
           (equal (< (rank (logic.=rhs x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.=rhs logic.fmtype logic.formulap))))

(defthm rank-of-logic.~arg-strong
  (implies (equal (logic.fmtype x) 'pnot*)
           (equal (< (rank (logic.~arg x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.~arg logic.fmtype logic.formulap))))

(defthm rank-of-logic.vlhs-strong
  (implies (equal (logic.fmtype x) 'por*)
           (equal (< (rank (logic.vlhs x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.vlhs logic.fmtype logic.formulap))))

(defthm rank-of-logic.vrhs-strong
  (implies (equal (logic.fmtype x) 'por*)
           (equal (< (rank (logic.vrhs x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.vrhs logic.fmtype logic.formulap))))



(defthm rank-of-logic.pnot
  (equal (rank (logic.pnot x))
         (+ 2 (rank x)))
  :hints(("Goal" :in-theory (enable logic.pnot))))

(defthm rank-of-logic.pequal
  (equal (rank (logic.pequal x y))
         (+ 3 (+ (rank x) (rank y))))
  :hints(("Goal" :in-theory (enable logic.pequal))))

(defthm rank-of-logic.por
  (equal (rank (logic.por x y))
         (+ 3 (+ (rank x) (rank y))))
  :hints(("Goal" :in-theory (enable logic.por))))




(defthm forcing-logic.termp-of-logic.=lhs
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.termp (logic.=lhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formulap logic.fmtype logic.=lhs))))

(defthm forcing-logic.termp-of-logic.=rhs
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.termp (logic.=rhs x))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.=rhs)
                                 (forcing-logic.termp-of-logic.=lhs)))))

(defthm forcing-logic.formulap-of-logic.~arg
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pnot*)))
           (equal (logic.formulap (logic.~arg x))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.~arg)
                                 (forcing-logic.termp-of-logic.=lhs
                                  forcing-logic.termp-of-logic.=rhs)))))

(defthm forcing-logic.formulap-of-logic.vlhs
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'por*)))
           (equal (logic.formulap (logic.vlhs x))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.vlhs)
                                 (forcing-logic.formulap-of-logic.~arg
                                  forcing-logic.termp-of-logic.=rhs
                                  forcing-logic.termp-of-logic.=lhs)))))

(defthm forcing-logic.formulap-of-logic.vrhs
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'por*)))
           (equal (logic.formulap (logic.vrhs x))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.vrhs)
                                 (forcing-logic.formulap-of-logic.vlhs
                                  forcing-logic.formulap-of-logic.~arg
                                  forcing-logic.termp-of-logic.=rhs
                                  forcing-logic.termp-of-logic.=lhs)))))

(defthm forcing-logic.=lhs-under-iff
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (iff (logic.=lhs x)
                t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.=lhs)))))

(defthm forcing-logic.=rhs-under-iff
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (iff (logic.=rhs x)
                t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.=rhs)))))

(defthm forcing-logic.~arg-under-iff
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pnot*)))
           (iff (logic.~arg x)
                t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.~arg)))))

(defthm forcing-logic.vlhs-under-iff
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'por*)))
           (iff (logic.vlhs x)
                t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.vlhs)))))

(defthm forcing-logic.vrhs-under-iff
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'por*)))
           (iff (logic.vrhs x)
                t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.fmtype logic.vrhs)))))

(defthm forcing-logic.formulap-of-logic.pequal
  (implies (and (force (logic.termp a))
                (force (logic.termp b)))
           (equal (logic.formulap (logic.pequal a b))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.pequal)))))

(defthm forcing-logic.formulap-of-logic.pnot
  (implies (force (logic.formulap a))
           (equal (logic.formulap (logic.pnot a))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.pnot logic.formulap)))))

(defthm forcing-logic.formulap-of-logic.por
  (implies (and (force (logic.formulap a))
                (force (logic.formulap b)))
           (equal (logic.formulap (logic.por a b))
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formulap logic.por)))))


(defthm logic.fmtype-of-logic.pequal
  (equal (logic.fmtype (logic.pequal a b))
         'pequal*)
  :hints(("Goal" :in-theory (enable logic.fmtype logic.pequal))))

(defthm logic.fmtype-of-logic.pnot
  (equal (logic.fmtype (logic.pnot a))
         'pnot*)
  :hints(("Goal" :in-theory (enable logic.fmtype logic.pnot))))

(defthm logic.fmtype-of-logic.por
  (equal (logic.fmtype (logic.por a b))
         'por*)
  :hints(("Goal" :in-theory (enable logic.fmtype logic.por))))

(defthm logic.=lhs-of-logic.pequal
  (equal (logic.=lhs (logic.pequal a b))
         a)
  :hints(("Goal" :in-theory (enable logic.=lhs logic.pequal))))

(defthm logic.=rhs-of-logic.pequal
  (equal (logic.=rhs (logic.pequal a b))
         b)
  :hints(("Goal" :in-theory (enable logic.=rhs logic.pequal))))

(defthm logic.~arg-of-logic.pnot
  (equal (logic.~arg (logic.pnot a))
         a)
  :hints(("Goal" :in-theory (enable logic.~arg logic.pnot))))

(defthm logic.vlhs-of-logic.por
  (equal (logic.vlhs (logic.por a b))
         a)
  :hints(("Goal" :in-theory (enable logic.vlhs logic.por))))

(defthm logic.vrhs-of-logic.por
  (equal (logic.vrhs (logic.por a b))
         b)
  :hints(("Goal" :in-theory (enable logic.vrhs logic.por))))

(defthm logic.=lhs-of-logic.pequal-free
  (implies (equal x (logic.pequal lhs rhs))
           (equal (logic.=lhs x)
                  lhs)))

(defthm logic.=rhs-of-logic.pequal-free
  (implies (equal x (logic.pequal lhs rhs))
           (equal (logic.=rhs x)
                  rhs)))

(defthm logic.fmtype-of-logic.pequal-free
  (implies (equal x (logic.pequal lhs rhs))
           (equal (logic.fmtype x)
                  'pequal*)))





(defthm forcing-equal-of-logic.pequal-rewrite
  (implies (and (force (logic.termp a))
                (force (logic.termp b)))
           (equal (equal (logic.pequal a b) x)
                  (and (logic.formulap x)
                       (equal (logic.fmtype x) 'pequal*)
                       (equal (logic.=lhs x) a)
                       (equal (logic.=rhs x) b))))
  :hints(("Goal" :in-theory (enable logic.formulap tuplep logic.fmtype logic.pequal
                                    logic.=lhs logic.=rhs))))

(defthm forcing-equal-of-logic.pequal-rewrite-two
  (implies (and (force (logic.termp a))
                (force (logic.termp b)))
           (equal (equal x (logic.pequal a b))
                  (and (logic.formulap x)
                       (equal (logic.fmtype x) 'pequal*)
                       (equal (logic.=lhs x) a)
                       (equal (logic.=rhs x) b)))))

(defthm forcing-equal-of-logic.pnot-rewrite
  (implies (force (logic.formulap a))
           (equal (equal (logic.pnot a) x)
                  (and (logic.formulap x)
                       (equal (logic.fmtype x) 'pnot*)
                       (equal (logic.~arg x) a))))
  :hints(("Goal" :in-theory (enable logic.formulap
                                    tuplep logic.fmtype logic.pnot logic.~arg))))

(defthm forcing-equal-of-logic.pnot-rewrite-two
  (implies (force (logic.formulap a))
           (equal (equal x (logic.pnot a))
                  (and (logic.formulap x)
                       (equal (logic.fmtype x) 'pnot*)
                       (equal (logic.~arg x) a)))))

(defthm forcing-equal-of-logic.por-rewrite
  (implies (and (force (logic.formulap a))
                (force (logic.formulap b)))
           (equal (equal (logic.por a b) x)
                  (and (logic.formulap x)
                       (equal (logic.fmtype x) 'por*)
                       (equal (logic.vlhs x) a)
                       (equal (logic.vrhs x) b))))
  :hints(("Goal" :in-theory (enable logic.formulap
                                    tuplep logic.fmtype logic.vlhs logic.vrhs logic.por))))

(defthm forcing-equal-of-logic.por-rewrite-two
  (implies (and (force (logic.formulap a))
                (force (logic.formulap b)))
           (equal (equal x (logic.por a b))
                  (and (logic.formulap x)
                       (equal (logic.fmtype x) 'por*)
                       (equal (logic.vlhs x) a)
                       (equal (logic.vrhs x) b)))))


(defthm aggressive-equal-of-logic.pors
  (implies (and (equal (logic.fmtype x) 'por*)
                (equal (logic.fmtype y) 'por*)
                (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (equal x y)
                  (and (equal (logic.vlhs x) (logic.vlhs y))
                       (equal (logic.vrhs x) (logic.vrhs y)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.formulap logic.fmtype logic.vlhs logic.vrhs))))

(defthm aggressive-equal-of-logic.pnots
  (implies (and (equal (logic.fmtype x) 'pnot*)
                (equal (logic.fmtype y) 'pnot*)
                (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (equal x y)
                  (equal (logic.~arg x) (logic.~arg y))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.formulap logic.fmtype logic.~arg))))

(defthm aggressive-equal-of-logic.pequals
  (implies (and (equal (logic.fmtype x) 'pequal*)
                (equal (logic.fmtype y) 'pequal*)
                (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (equal x y)
                  (and (equal (logic.=lhs x) (logic.=lhs y))
                       (equal (logic.=rhs x) (logic.=rhs y)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.formulap logic.fmtype logic.=lhs logic.=rhs))))




(defthm forcing-logic.pnot-of-logic.~arg
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pnot*)))
           (equal (logic.pnot (logic.~arg x))
                  x)))

(defthm forcing-logic.por-of-logic.vlhs-and-logic.vrhs
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'por*)))
           (equal (logic.por (logic.vlhs x) (logic.vrhs x))
                  x)))

(defthm forcing-logic.pequal-of-logic.=lhs-and-logic.=rhs
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.pequal (logic.=lhs x) (logic.=rhs x))
                  x)))



(defthm equal-logic.pequal-logic.pequal-rewrite
  (equal (equal (logic.pequal a b) (logic.pequal c d))
         (and (equal a c)
              (equal b d)))
  :hints(("Goal" :in-theory (enable logic.pequal))))

(defthm equal-logic.pnot-logic.pnot-rewrite
  (equal (equal (logic.pnot a) (logic.pnot b))
         (equal a b))
  :hints(("Goal" :in-theory (enable logic.pnot))))

(defthm equal-logic.por-logic.por-rewrite
  (equal (equal (logic.por a b) (logic.por c d))
         (and (equal a c)
              (equal b d)))
  :hints(("Goal" :in-theory (enable logic.por))))



;; These rules fix some problems with overly aggressive forcing which arise in
;; bizarre cases.

(defthm logic.formulap-of-logic.pequal-of-nil-one
  (equal (logic.formulap (logic.pequal nil x))
         nil)
  :hints(("Goal" :in-theory (enable logic.formulap logic.pequal))))

(defthm logic.formulap-of-logic.pequal-of-nil-two
  (equal (logic.formulap (logic.pequal x nil))
         nil)
  :hints(("Goal" :in-theory (enable logic.formulap logic.pequal))))

(defthm logic.formulap-of-logic.pnot-of-logic.pequal-of-nil-one
  (equal (logic.formulap (logic.pnot (logic.pequal nil x)))
         nil)
  :hints(("Goal" :in-theory (enable logic.formulap logic.pnot))))

(defthm logic.formulap-of-logic.pnot-of-logic.pequal-of-nil-two
  (equal (logic.formulap (logic.pnot (logic.pequal x nil)))
         nil)
  :hints(("Goal" :in-theory (enable logic.formulap logic.pnot))))





(defthmd logic.formulap-of-logic.por-expensive
  (equal (logic.formulap (logic.por x y))
         (and (logic.formulap x)
              (logic.formulap y)))
  :hints(("Goal" :in-theory (enable logic.formulap logic.por))))




(defund logic.formula-atblp (x atbl)
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.arity-tablep atbl))))
  (let ((type (logic.fmtype x)))
    (cond ((equal type 'por*)
           (and (logic.formula-atblp (logic.vlhs x) atbl)
                (logic.formula-atblp (logic.vrhs x) atbl)))
          ((equal type 'pnot*)
           (logic.formula-atblp (logic.~arg x) atbl))
          ((equal type 'pequal*)
           (and (logic.term-atblp (logic.=lhs x) atbl)
                (logic.term-atblp (logic.=rhs x) atbl)))
          (t nil))))

(defthm booleanp-of-logic.formula-atblp
  (equal (booleanp (logic.formula-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (logic.formula-atblp)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm logic.formula-atblp-when-not-consp
  (implies (not (consp x))
           (equal (logic.formula-atblp x atbl)
                  nil))
  ;; We're a little sloppy here and just allow fmtype to open up
  :hints(("Goal" :in-theory (enable logic.formula-atblp logic.fmtype))))

(deflist logic.formula-list-atblp (x atbl)
  (logic.formula-atblp x atbl)
  :elementp-of-nil nil
  :guard (and (logic.formula-listp x)
              (logic.arity-tablep atbl)))

(defthm forcing-logic.formula-list-atblp-of-app
  ;; BOZO we prefer this more aggressive app rule.  Add a :aggressivep to deflist?
  (implies (and (force (logic.formula-list-atblp x atbl))
                (force (logic.formula-list-atblp y atbl)))
           (equal (logic.formula-list-atblp (app x y) atbl)
                  t)))

(in-theory (disable logic.formula-list-atblp-of-app))

(defthm logic.formula-atblp-of-second-when-logic.formula-list-atblp
  ;; BOZO consider adding something like this to deflist.
  (implies (logic.formula-list-atblp x atbl)
           (equal (logic.formula-atblp (second x) atbl)
                  (consp (cdr x)))))

(defthm logic.formula-atbl-listp-of-ordered-subsetp
  ;; BOZO consider figuring out how to add something like this to deflist.
  (implies (and (ordered-subsetp x y)
                (logic.formula-list-atblp y atbl))
           (equal (logic.formula-list-atblp x atbl)
                  t)))

(deflist logic.formula-list-list-atblp (x atbl)
  (logic.formula-list-atblp x atbl)
  :elementp-of-nil t
  :guard (and (logic.formula-list-listp x)
              (logic.arity-tablep atbl)))

(defthm forcing-logic.term-atblp-of-logic.=lhs
  (implies (and (force (logic.formula-atblp x atbl))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.term-atblp (logic.=lhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-atblp))))

(defthm forcing-logic.term-atblp-of-logic.=rhs
  (implies (and (force (logic.formula-atblp x atbl))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.term-atblp (logic.=rhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formula-atblp)
                                 (forcing-logic.term-atblp-of-logic.=lhs)))))

(defthm forcing-logic.formula-atblp-of-logic.~arg
  (implies (and (force (logic.formula-atblp x atbl))
                (force (equal (logic.fmtype x) 'pnot*)))
           (equal (logic.formula-atblp (logic.~arg x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-atblp))))

(defthm forcing-logic.formula-atblp-of-logic.vlhs
  (implies (and (force (logic.formula-atblp x atbl))
                (force (equal (logic.fmtype x) 'por*)))
           (equal (logic.formula-atblp (logic.vlhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-atblp))))

(defthm forcing-logic.formula-atblp-of-logic.vrhs
  (implies (and (force (logic.formula-atblp x atbl))
                (force (equal (logic.fmtype x) 'por*)))
           (equal (logic.formula-atblp (logic.vrhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formula-atblp)
                                 (forcing-logic.formula-atblp-of-logic.vlhs)))))




(defthm forcing-logic.formula-atblp-of-logic.pequal
  (implies (and (force (logic.term-atblp a atbl))
                (force (logic.term-atblp b atbl)))
           (equal (logic.formula-atblp (logic.pequal a b) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-atblp))))

(defthm forcing-logic.formula-atblp-of-logic.pnot
  (implies (force (logic.formula-atblp a atbl))
           (equal (logic.formula-atblp (logic.pnot a) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formula-atblp)
                                 (forcing-logic.formula-atblp-of-logic.~arg)))))

(defthm forcing-logic.formula-atblp-of-logic.por
  (implies (and (force (logic.formula-atblp a atbl))
                (force (logic.formula-atblp b atbl)))
           (equal (logic.formula-atblp (logic.por a b) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.formula-atblp)
                                 (forcing-logic.formula-atblp-of-logic.vlhs
                                  forcing-logic.formula-atblp-of-logic.vrhs)))))



(defthm logic.formulap-when-malformed-cheap
  (implies (and (not (equal (logic.fmtype x) 'por*))
                (not (equal (logic.fmtype x) 'pnot*))
                (not (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.formulap x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.formulap logic.fmtype))))

(defthm logic.formula-atblp-when-malformed-cheap
  (implies (and (not (equal (logic.fmtype x) 'por*))
                (not (equal (logic.fmtype x) 'pnot*))
                (not (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.formula-atblp x atbl)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (e/d (logic.formula-atblp)
                                 (logic.fmtype-normalizer-cheap)))))



(deftheory forcing-logic.formula-atblp-rules
  '(forcing-logic.term-atblp-of-logic.=lhs
    forcing-logic.term-atblp-of-logic.=rhs
    forcing-logic.formula-atblp-of-logic.~arg
    forcing-logic.formula-atblp-of-logic.vlhs
    forcing-logic.formula-atblp-of-logic.vrhs
    forcing-logic.formula-atblp-of-logic.pequal
    forcing-logic.formula-atblp-of-logic.pnot
    forcing-logic.formula-atblp-of-logic.por))


(encapsulate
 ()
 (local (in-theory (e/d (logic.formula-atblp)
                        (forcing-logic.formula-atblp-rules))))

 (defthmd logic.formula-atblp-when-por-expensive
   (implies (equal (logic.fmtype x) 'por*)
            (equal (logic.formula-atblp x atbl)
                   (and (logic.formula-atblp (logic.vlhs x) atbl)
                        (logic.formula-atblp (logic.vrhs x) atbl)))))

 (defthmd logic.formula-atblp-when-pnot-expensive
   (implies (equal (logic.fmtype x) 'pnot*)
            (equal (logic.formula-atblp x atbl)
                   (logic.formula-atblp (logic.~arg x) atbl))))

 (defthmd logic.formula-atblp-when-pequal-expensive
   (implies (equal (logic.fmtype x) 'pequal*)
            (equal (logic.formula-atblp x atbl)
                   (and (logic.term-atblp (logic.=lhs x) atbl)
                        (logic.term-atblp (logic.=rhs x) atbl)))))

 (defthmd logic.formula-atblp-of-logic.por-expensive
   (equal (logic.formula-atblp (logic.por x y) atbl)
          (and (logic.formula-atblp x atbl)
               (logic.formula-atblp y atbl))))

 (defthmd logic.formula-atblp-of-logic.pequal-expensive
   (equal (logic.formula-atblp (logic.pequal x y) atbl)
          (and (logic.term-atblp x atbl)
               (logic.term-atblp y atbl))))

 (defthmd logic.formula-atblp-of-logic.pnot-expensive
   (equal (logic.formula-atblp (logic.pnot x) atbl)
          (logic.formula-atblp x atbl)))

 )

(deftheory backtracking-logic.formula-atblp-rules
  '(logic.formula-atblp-when-por-expensive
    logic.formula-atblp-when-pnot-expensive
    logic.formula-atblp-when-pequal-expensive
    logic.formula-atblp-of-logic.por-expensive
    logic.formula-atblp-of-logic.pnot-expensive
    logic.formula-atblp-of-logic.pequal-expensive
    ))
