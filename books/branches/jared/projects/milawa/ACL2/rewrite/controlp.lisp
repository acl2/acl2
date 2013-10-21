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
(include-book "theoryp")
(include-book "syntax-evaluator")
(include-book "assms/assmctrl")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; A rewriter control is an aggregate of the invariant arguments used by our
;; rewriters:
;;
;;   - A list of function definitions to use during execution,
;;   - A list of the function names we should not try to execute,
;;   - A stack depth to use when executing functions,
;;   - A flag to control whether to use forcing,
;;   - A flag to control whether or not we should beta-reduce lambdas,
;;   - A theory for the rewrite rules,
;;   - Settings for the assumptions system.
;;
;; This may be expanded on in the future to support new features, so you should
;; not assume that these are the only fields.

(defaggregate rw.control
  (noexec forcingp betamode theory defs depth assmctrl)
  :require ((logic.function-symbol-listp-of-rw.control->noexec  (logic.function-symbol-listp noexec))
            (booleanp-of-rw.control->forcingp                   (booleanp forcingp))
            (symbolp-of-rw.control->betamode                    (symbolp betamode))
            (rw.theoryp-of-rw.control->theory                   (rw.theoryp theory))
            (definition-listp-of-rw.control->defs               (definition-listp defs))
            (natp-of-rw.control->depth                          (natp depth))
            (rw.assmctrlp-of-rw.control->assmctrl               (rw.assmctrlp assmctrl)))
  :legiblep nil)


(definlined rw.control-atblp (x atbl)
  (declare (xargs :guard (and (rw.controlp x)
                              (logic.arity-tablep atbl))))
  (and (rw.theory-atblp (rw.control->theory x) atbl)
       (logic.formula-list-atblp (rw.control->defs x) atbl)))

(defthm booleanp-of-rw.control-atblp
  (equal (booleanp (rw.control-atblp x atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.control-atblp))))

(defthm forcing-rw.control-atblp-of-rw.control
  (implies (force (and (rw.theory-atblp theory atbl)
                       (logic.formula-list-atblp defs atbl)))
           (equal (rw.control-atblp (rw.control noexec forcingp betamode theory defs depth assmctrl) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.control-atblp))))

(defthm forcing-rw.theory-atblp-of-rw.control->theory
  (implies (force (rw.control-atblp x atbl))
           (equal (rw.theory-atblp (rw.control->theory x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.control-atblp))))

(defthm forcing-logic.formula-list-atblp-of-rw.control->defs
  (implies (force (rw.control-atblp x atbl))
           (equal (logic.formula-list-atblp (rw.control->defs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.control-atblp))))



(definlined rw.control-env-okp (x axioms thms)
  (declare (xargs :guard (and (rw.controlp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms))))
  (and (subsetp (rw.control->defs x) axioms)
       (rw.theory-env-okp (rw.control->theory x) thms)))

(defthm booleanp-of-rw.control-env-okp
  (equal (booleanp (rw.control-env-okp x axioms thms))
         t)
  :hints(("Goal" :in-theory (enable rw.control-env-okp))))

(defthm forcing-rw.control-env-okp-of-rw.control
  (implies (force (and (subsetp defs axioms)
                       (rw.theory-env-okp theory thms)))
           (equal (rw.control-env-okp (rw.control noexec forcingp betamode theory defs depth assmctrl) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable rw.control-env-okp))))

(defthm forcing-rw.theory-env-okp-of-rw.control->theory
  (implies (force (rw.control-env-okp x axioms thms))
           (equal (rw.theory-env-okp (rw.control->theory x) thms)
                  t))
  :hints(("Goal" :in-theory (enable rw.control-env-okp))))

(defthm forcing-subsetp-of-rw.control-defs-and-axioms
  ;; Well, this is hyper-aggressive.
  (implies (force (rw.control-env-okp x axioms thms))
           (equal (subsetp (rw.control->defs x) axioms)
                  t))
  :hints(("Goal" :in-theory (enable rw.control-env-okp))))




;; Checking Syntactic Restrictions
;;
;; We can add syntactic restrictions to prevent rules from being instantiated
;; with some sigmas.  Suppose we are trying to use [x1 <- s1, ..., xn <- sn] to
;; instantiate some rule, and the rule has a syntactic restriction, R.  Such
;; restrictions are just terms, so say the variables of R are [v1, ..., vm].
;;
;; Let [u1, ..., uk] be the vi which do not occur among the xi.  These vars do
;; not occur in our sigma's domain, so as far as instantiation is concerned, we
;; can think of sigma as [u1 <- u1, ..., uk <- uk, x1 <- s1, ..., xn <- sn].
;;
;; We begin by creating a Grounding Sigma by quoting the range of this new and
;; extended sigma.  That is, we create:
;;
;;   Grounding Sigma = [u1 <- (quote u1), ..., uk <- (quote uk),
;;                      x1 <- (quote s1), ..., xn <- (quote sn)]
;;
;; We now apply this sigma to R.  Observe that this produces a ground term,
;; since all the variables of R are in the domain of the grounding sigma, and
;; the range of the grounding sigma is entirely ground terms.  We then evaluate
;; the resulting term, and we say the restriction is satisfied if the result is
;; non-nil.

(defund rw.grounding-sigma-fragment (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (cons (car x) (list 'quote (car x)))
            (rw.grounding-sigma-fragment (cdr x)))
    nil))

(defthm rw.grounding-sigma-fragment-when-not-consp
  (implies (not (consp x))
           (equal (rw.grounding-sigma-fragment x)
                  nil))
  :hints(("Goal" :in-theory (enable rw.grounding-sigma-fragment))))

(defthm rw.grounding-sigma-fragment-of-cons
  (equal (rw.grounding-sigma-fragment (cons a x))
         (cons (cons a (list 'quote a))
               (rw.grounding-sigma-fragment x)))
  :hints(("Goal" :in-theory (enable rw.grounding-sigma-fragment))))

(defthm forcing-logic.sigmap-of-rw.grounding-sigma-fragment
  (implies (force (logic.variable-listp x))
           (equal (logic.sigmap (rw.grounding-sigma-fragment x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.sigma-atblp-of-rw.grounding-sigma-fragment
  (implies (force (logic.variable-listp x))
           (equal (logic.sigma-atblp (rw.grounding-sigma-fragment x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.ground-listp-of-range-of-rw.grounding-sigma-fragment
  (equal (logic.ground-listp (range (rw.grounding-sigma-fragment x)))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-rw.grounding-sigma-fragment
  (equal (domain (rw.grounding-sigma-fragment x))
         (list-fix x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.grounding-sigma-fragment-of-list-fix
  (equal (rw.grounding-sigma-fragment (list-fix x))
         (rw.grounding-sigma-fragment x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-rw.grounding-sigma-fragment
  (equal (true-listp (rw.grounding-sigma-fragment x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.grounding-sigma-fragment-of-app
  (equal (rw.grounding-sigma-fragment (app x y))
         (app (rw.grounding-sigma-fragment x)
              (rw.grounding-sigma-fragment y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd rw.grounding-sigma-fragment-of-rev
  (equal (rw.grounding-sigma-fragment (rev x))
         (rev (rw.grounding-sigma-fragment x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-rw.grounding-sigma-fragment
  (equal (rev (rw.grounding-sigma-fragment x))
         (rw.grounding-sigma-fragment (rev x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defund rw.aux-extend-grounding-sigma (vars acc)
  (declare (xargs :guard (and (logic.variable-listp vars)
                              (logic.sigmap acc))))
  (if (consp vars)
      (rw.aux-extend-grounding-sigma (cdr vars)
                                     (cons (cons (car vars) (list 'quote (car vars))) acc))
    acc))

(defthm forcing-rw.aux-extend-grounding-sigma-removal
  (implies (force (true-listp acc))
           (equal (rw.aux-extend-grounding-sigma vars acc)
                  (revappend (rw.grounding-sigma-fragment vars) acc)))
  :hints(("Goal" :in-theory (enable rw.aux-extend-grounding-sigma
                                    rw.grounding-sigma-fragment))))




(defund rw.extend-grounding-sigma (restriction sigma)
  (declare (xargs :guard (and (logic.termp restriction)
                              (logic.sigmap sigma)
                              (logic.ground-listp (range sigma))
                              (true-listp sigma))))
  (let* ((vs (logic.term-vars restriction))
         (xs (fast-domain$ sigma nil))
         (us (fast-difference$ vs xs nil)))
    (rw.aux-extend-grounding-sigma us sigma)))

(defthm forcing-logic.sigmap-of-rw.extend-grounding-sigma
  (implies (force (and (logic.termp restriction)
                       (logic.sigmap sigma)
                       (true-listp sigma)))
           (equal (logic.sigmap (rw.extend-grounding-sigma restriction sigma))
                  t))
  :hints(("Goal" :in-theory (enable rw.extend-grounding-sigma))))

(defthm forcing-logic.sigma-atblp-of-rw.extend-grounding-sigma
  (implies (force (and (logic.termp restriction)
                       (logic.sigmap sigma)
                       (logic.sigma-atblp sigma atbl)
                       (true-listp sigma)))
           (equal (logic.sigma-atblp (rw.extend-grounding-sigma restriction sigma) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.extend-grounding-sigma))))

(defthm forcing-logic.ground-listp-of-range-of-rw.extend-grounding-sigma
  (implies (force (and (logic.termp restriction)
                       (logic.sigmap sigma)
                       (logic.ground-listp (range sigma))
                       (true-listp sigma)))
           (equal (logic.ground-listp (range (rw.extend-grounding-sigma restriction sigma)))
                  t))
  :hints(("Goal" :in-theory (enable rw.extend-grounding-sigma))))

(defthm subsetp-of-logic.term-vars-and-domain-of-rw.extend-grounding-sigma
  (implies (force (true-listp sigma))
           (equal (subsetp (logic.term-vars restriction)
                           (domain (rw.extend-grounding-sigma restriction sigma)))
                  t))
  :hints(("Goal" :in-theory (e/d (rw.extend-grounding-sigma domain-of-rev)
                                 (rev-of-domain)))))



(defund rw.aux-rule-syntax-okp (name restrictions partial-grounding-sigma defs depth)
  (declare (xargs :guard (and (symbolp name)
                              (logic.term-listp restrictions)
                              (logic.sigmap partial-grounding-sigma)
                              (logic.ground-listp (range partial-grounding-sigma))
                              (true-listp partial-grounding-sigma)
                              (definition-listp defs)
                              (natp depth))))
  (if (consp restrictions)
      (let* ((grounding-sigma (rw.extend-grounding-sigma (car restrictions) partial-grounding-sigma))
             (target          (logic.substitute (car restrictions) grounding-sigma))
             (valuation       (rewrite.syntaxp-evaluator target defs depth)))
        (if (not valuation)
            (ACL2::cw "Note: we won't apply ~s0 since we failed to evaluate the syntactic ~
                       restriction ~q1.~%"
                      name target)
          (and (logic.unquote valuation)
               (rw.aux-rule-syntax-okp name (cdr restrictions) partial-grounding-sigma defs depth))))
    t))

(defund rw.rule-syntax-okp (rule sigma control)
  (declare (xargs :guard (and (rw.rulep rule)
                              (logic.sigmap sigma)
                              (subsetp (logic.term-vars (rw.rule->lhs rule)) (domain sigma))
                              (rw.controlp control))))
  (let ((restrictions (rw.rule->syntax rule)))
    (if (consp restrictions)
        (rw.aux-rule-syntax-okp (rw.rule->name rule)
                                restrictions
                                (logic.quote-range sigma)
                                (rw.control->defs control)
                                (rw.control->depth control))
      t)))

(defthm booleanp-of-rw.aux-rule-syntax-okp
  (equal (booleanp (rw.aux-rule-syntax-okp name terms partial-grounding-sigma defs depth))
         t)
  :hints(("Goal" :in-theory (e/d (rw.aux-rule-syntax-okp)
                                 ((:executable-counterpart ACL2::force))))))

(defthm booleanp-of-rw.rule-syntax-okp
  (equal (booleanp (rw.rule-syntax-okp rule sigma control))
         t)
  :hints(("Goal" :in-theory (enable rw.rule-syntax-okp))))


