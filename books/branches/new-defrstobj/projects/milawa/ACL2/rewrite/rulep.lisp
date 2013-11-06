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
(include-book "evaluator") ;; why?
(include-book "../clauses/basic")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Each hypothesis has a force-mode.  Here is what these modes mean:
;;
;;   - nil     never force it
;;   - weak    force it unless it rewrites to nil (like ACL2)
;;   - strong  force it no matter what it rewrites to

(defund rw.force-modep (x)
  (memberp x '(nil weak strong)))

(defthm booleanp-of-rw.force-modep
  (equal (booleanp (rw.force-modep x))
         t)
  :hints(("Goal" :in-theory (enable rw.force-modep))))



;; A hypothesis is an aggregate of:
;;
;;   - A term which must be proven before the rule can be used,
;;   - A force mode (described above),
;;   - A limit flag that indicates if we should only search in a limited way
;;     during the attempt to relieve this hyp, and
;;   - A limit (if the limit flag is set) that indicates how much searching to
;;     tolerate during the relief of this hyp.
;;
;; This may be expanded on in the future to support new features, so you should
;; not assume that these are the only fields.

(defaggregate rw.hyp
  (term fmode limitp limit)
  :require ((logic.termp-of-rw.hyp->term     (logic.termp term))
            (rw.force-modep-of-rw.hyp->fmode (rw.force-modep fmode))
            (booleanp-of-rw.hyp->limitp      (booleanp limitp))
            (natp-of-rw.hyp->limit           (natp limit)))
  :legiblep nil)

(deflist rw.hyp-listp (x)
  (rw.hypp x)
  :elementp-of-nil nil)



(definlined rw.hyp-atblp (x atbl)
  (declare (xargs :guard (and (rw.hypp x)
                              (logic.arity-tablep atbl))))
  (logic.term-atblp (rw.hyp->term x) atbl))

(defthm booleanp-of-rw.hyp-atblp
  (equal (booleanp (rw.hyp-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.hyp-atblp))))

(defthm forcing-logic.term-atblp-of-rw.hyp
  (implies (force (rw.hyp-atblp x atbl))
           (equal (logic.term-atblp (rw.hyp->term x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.hyp-atblp))))

(defthm rw.hyp-atblp-of-rw.hyp
  (implies (force (logic.term-atblp term atbl))
           (equal (rw.hyp-atblp (rw.hyp term fmode limitp limit) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.hyp-atblp))))

(defthm rw.hyp-atblp-of-nil
  (equal (rw.hyp-atblp nil atbl)
         nil)
  :hints(("Goal" :in-theory (enable rw.hyp-atblp))))

(deflist rw.hyp-list-atblp (x atbl)
  (rw.hyp-atblp x atbl)
  :elementp-of-nil nil
  :guard (and (rw.hyp-listp x)
              (logic.arity-tablep atbl)))


(defprojection :list (rw.hyp-list-terms x)
               :element (rw.hyp->term x)
               :guard (rw.hyp-listp x))

(defthm forcing-logic.term-listp-of-rw.hyp-list-terms
  (implies (force (rw.hyp-listp x))
           (equal (logic.term-listp (rw.hyp-list-terms x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.hyp-list-terms
  (implies (force (rw.hyp-list-atblp x atbl))
           (equal (logic.term-list-atblp (rw.hyp-list-terms x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))





;; A rewrite rule is an aggregate of:
;;
;;   - A symbolic name which is used to identify the rule,
;;   - A type that identifies what kind of rule it is.
;;   - A list of hypotheses which govern when the rule can be used,
;;   - A target term, lhs, which describes the terms we want to rewrite,
;;   - A replacement term, rhs, which describes the result of rewriting,
;;   - An equivalence relation that relates the lhs and rhs, i.e., "equal",
;;   - A list of syntactic restrictions on the rule's application, and
;;   - A list of "critical hyps" used in free-variable matching.
;;
;; This may be expanded on in the future to support new features, so you should
;; not assume that these are the only fields.

(defaggregate rw.rule
  (name type hyps equiv lhs rhs syntax crithyps)
  :require ((symbolp-of-rw.rule->name                (symbolp name))
            (symbolp-of-rw.rule->type                (symbolp type))
            (rw.hyp-listp-of-rw.rule->hyps           (rw.hyp-listp hyps))
            (logic.function-namep-of-rw.rule->equiv  (logic.function-namep equiv))
            (logic.termp-of-rw.rule->lhs             (logic.termp lhs))
            (logic.termp-of-rw.rule->rhs             (logic.termp rhs))
            (logic.term-listp-of-rw.rule->syntax     (logic.term-listp syntax))
            ;; BOZO this is not named correctly
            (subsetp-of-rw.rule->crithyps            (logic.term-listp crithyps))
            )
  :legiblep nil)

(deflist rw.rule-listp (x)
  (rw.rulep x)
  :elementp-of-nil nil)

(deflist rw.rule-list-listp (x)
  (rw.rule-listp x)
  :elementp-of-nil t)

(defthm forcing-rw.rule-listp-of-simple-flatten
  (implies (force (rw.rule-list-listp x))
           (equal (rw.rule-listp (simple-flatten x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defund rw.rule-atblp (x atbl)
  (declare (xargs :guard (and (rw.rulep x)
                              (logic.arity-tablep atbl))))
  (and (rw.hyp-list-atblp (rw.rule->hyps x) atbl)
       (equal (cdr (lookup (rw.rule->equiv x) atbl)) 2)
       (logic.term-atblp (rw.rule->lhs x) atbl)
       (logic.term-atblp (rw.rule->rhs x) atbl)
       (logic.term-list-atblp (rw.rule->crithyps x) atbl)
       ;; We don't check syntax restrictions; they're only used to decide if
       ;; the rule should be applied.
       ))

(defthm rw.rule-atblp-of-nil
  (equal (rw.rule-atblp nil atbl)
         nil)
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm booleanp-of-rw.rule-atblp
  (equal (booleanp (rw.rule-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm forcing-rw.hyp-list-atblp-of-rw.rule->hyps
  (implies (force (rw.rule-atblp x atbl))
           (equal (rw.hyp-list-atblp (rw.rule->hyps x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm forcing-logic.term-atblp-of-rw.rule->lhs
  (implies (force (rw.rule-atblp x atbl))
           (equal (logic.term-atblp (rw.rule->lhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm forcing-logic.term-atblp-of-rw.rule->rhs
  (implies (force (rw.rule-atblp x atbl))
           (equal (logic.term-atblp (rw.rule->rhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm forcing-logic.term-list-atblp-of-rw.rule->crithyps
  (implies (force (rw.rule-atblp x atbl))
           (equal (logic.term-list-atblp (rw.rule->crithyps x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm forcing-lookup-of-rw.rule-equiv
  (implies (force (rw.rule-atblp x atbl))
           (equal (lookup (rw.rule->equiv x) atbl)
                  (cons (rw.rule->equiv x) 2)))
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(defthm forcing-rw.rule-atblp-of-rw.rule
  (implies (and (force (rw.hyp-list-atblp hyps atbl))
                (force (equal (cdr (lookup equiv atbl)) 2))
                (force (logic.term-atblp lhs atbl))
                (force (logic.term-atblp rhs atbl))
                (force (logic.term-list-atblp crithyps atbl)))
           (equal (rw.rule-atblp (rw.rule name type hyps equiv lhs rhs syntax crithyps) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-atblp))))

(deflist rw.rule-list-atblp (x atbl)
  (rw.rule-atblp x atbl)
  :guard (and (rw.rule-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil nil)

(deflist rw.rule-list-list-atblp (x atbl)
  (rw.rule-list-atblp x atbl)
  :guard (and (rw.rule-list-listp x)
              (logic.arity-tablep atbl))
  :elementp-of-nil t)





;; Interpreting rules as clauses/formulas.
;;
;; A rule loosely means "hyps imply (equiv lhs rhs)."  I have flip-flopped a
;; bit on how to represent this as a formula, but now I prefer to represent it
;; as a clause.  This makes it "compatible" with the tactic harness directly,
;; rather than having to involve the formula compiler or anything like that.
;; The clause for a rule is:
;;
;;   If there are no hyps:  (equiv lhs rhs)
;;
;;   If there are hyps:     (not hyp1) v ... v (not hypN) v (equiv lhs rhs)

(defund rw.rule-clause (x)
  (declare (xargs :guard (rw.rulep x)))
  (let* ((hyps  (rw.rule->hyps x))
         (equiv (rw.rule->equiv x))
         (lhs   (rw.rule->lhs x))
         (rhs   (rw.rule->rhs x)))
    (fast-app (logic.negate-term-list (rw.hyp-list-terms hyps))
              (list (logic.function equiv (list lhs rhs))))))

(defthm consp-of-rw.rule-clause
  (equal (consp (rw.rule-clause x))
         t)
  :hints(("Goal" :in-theory (enable rw.rule-clause))))

(defthm forcing-logic.term-listp-of-rw.rule-clause
  (implies (force (rw.rulep x))
           (equal (logic.term-listp (rw.rule-clause x))
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-clause))))

(defthm forcing-logic.term-list-atbp-of-rw.rule-clause
  (implies (force (and (rw.rule-atblp x atbl)
                       (rw.rulep x)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-atblp (rw.rule-clause x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-clause))))

(defthm forcing-rw.rule-clause-when-no-hyps
  (implies (not (rw.rule->hyps x))
           (equal (rw.rule-clause x)
                  (list (logic.function (rw.rule->equiv x)
                                        (list (rw.rule->lhs x)
                                              (rw.rule->rhs x))))))
  :hints(("Goal" :in-theory (enable rw.rule-clause))))



(defprojection :list (rw.rule-list-clauses x)
               :element (rw.rule-clause x)
               :guard (rw.rule-listp x))

(defthm cons-listp-of-rw.rule-list-clauses
  (equal (cons-listp (rw.rule-list-clauses x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-rw.rule-list-clauses
  (implies (force (rw.rule-listp x))
           (equal (logic.term-list-listp (rw.rule-list-clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atbp-of-rw.rule-list-clauses
  (implies (force (and (rw.rule-list-atblp x atbl)
                       (rw.rule-listp x)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-list-atblp (rw.rule-list-clauses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection
  :list (rw.rule-list-lhses x)
  :element (rw.rule->lhs x)
  :guard (rw.rule-listp x))

(defthm forcing-logic.term-listp-of-rw.rule-list-lhses
  (implies (force (rw.rule-listp x))
           (equal (logic.term-listp (rw.rule-list-lhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.rule-list-lhses
  (implies (force (rw.rule-list-atblp x atbl))
           (equal (logic.term-list-atblp (rw.rule-list-lhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(defprojection
  :list (rw.rule-list-names x)
  :element (rw.rule->name x)
  :guard (rw.rule-listp x))

(defthm forcing-symbol-listp-of-rw.rule-list-names
  (implies (force (rw.rule-listp x))
           (equal (symbol-listp (rw.rule-list-names x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(definlined rw.rule-env-okp (x thms)
  (declare (xargs :guard (and (rw.rulep x)
                              (logic.formula-listp thms))))
  (memberp (clause.clause-formula (rw.rule-clause x)) thms))

(defthm booleanp-of-rw.rule-env-okp
  (equal (booleanp (rw.rule-env-okp x thms))
         t)
  :hints(("Goal" :in-theory (enable rw.rule-env-okp))))


(deflist rw.rule-list-env-okp (x thms)
  (rw.rule-env-okp x thms)
  :guard (and (rw.rule-listp x)
              (logic.formula-listp thms)))

(deflist rw.rule-list-list-env-okp (x thms)
  (rw.rule-list-env-okp x thms)
  :guard (and (rw.rule-list-listp x)
              (logic.formula-listp thms))
  :elementp-of-nil t)







(defund rw.rule-list-lookup (rulename rules)
  (declare (xargs :guard (rw.rule-listp rules)))
  (if (consp rules)
      (if (equal (rw.rule->name (car rules)) rulename)
          (car rules)
        (rw.rule-list-lookup rulename (cdr rules)))
    nil))

(defthm rw.rule-list-lookup-when-not-consp
  (implies (not (consp rules))
           (equal (rw.rule-list-lookup rulename rules)
                  nil))
  :hints(("Goal" :in-theory (enable rw.rule-list-lookup))))

(defthm rw.rule-list-lookup-of-cons
  (equal (rw.rule-list-lookup rulename (cons rule rules))
         (if (equal (rw.rule->name rule) rulename)
             rule
           (rw.rule-list-lookup rulename rules)))
  :hints(("Goal" :in-theory (enable rw.rule-list-lookup))))

(defthm rw.rulep-of-rw.rule-list-lookup
  (implies (force (rw.rule-listp rules))
           (equal (rw.rulep (rw.rule-list-lookup name rules))
                  (if (rw.rule-list-lookup name rules)
                      t
                    nil)))
  :hints(("Goal" :induct (cdr-induction rules))))

(defthm rw.rule-atblp-of-rw.rule-list-lookup
  (implies (force (rw.rule-list-atblp rules atbl))
           (equal (rw.rule-atblp (rw.rule-list-lookup name rules) atbl)
                  (if (rw.rule-list-lookup name rules)
                      t
                    nil)))
  :hints(("Goal" :induct (cdr-induction rules))))

(defthm rw.rule-env-okp-of-rw.rule-list-lookup
  (implies (force (and (rw.rule-list-env-okp rules thms)
                       (rw.rule-list-lookup name rules)))
           (equal (rw.rule-env-okp (rw.rule-list-lookup name rules) thms)
                  t))
  :hints(("Goal" :induct (cdr-induction rules))))



(defthm rw.rule-list-atblp-of-cdr-of-lookup
  (implies (force (rw.rule-list-list-atblp (range map) atbl))
           (rw.rule-list-atblp (cdr (lookup name map)) atbl))
  :hints(("Goal" :induct (cdr-induction map))))

(defthm rw.rule-list-env-okp-of-cdr-of-lookup
  (implies (force (rw.rule-list-list-env-okp (range map) thms))
           (rw.rule-list-env-okp (cdr (lookup name map)) thms))
  :hints(("Goal" :induct (cdr-induction map))))
