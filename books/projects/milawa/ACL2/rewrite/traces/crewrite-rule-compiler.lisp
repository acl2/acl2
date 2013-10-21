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
(include-book "trace-okp")
(include-book "../../build/iff")
(include-book "../../build/not")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; BOZO find these a home.

(local (in-theory (enable rw.trace-conclusion-formula rw.trace-formula)))

(defthm logic.strip-function-names-of-rw.trace-list-conclusion-formulas-when-all-iffp
  (implies (and (all-equalp t (rw.trace-list-iffps x))
                (force (rw.trace-listp x)))
           (equal (logic.strip-function-names (logic.=lhses (rw.trace-list-conclusion-formulas x)))
                  (repeat 'iff (len x))))
  :hints(("Goal" :in-theory (enable rw.trace-list-conclusion-formulas))))

(defthm logic.strip-lens-of-logic.strip-function-args-of-rw.trace-list-conclusion-formulas
  (equal (strip-lens (logic.strip-function-args (logic.=lhses (rw.trace-list-conclusion-formulas x))))
         (repeat 2 (len x)))
  :hints(("Goal" :in-theory (enable rw.trace-list-conclusion-formulas))))


(deftheorem rw.crewrite-rule-lemma
  :derive  (v (!= (iff x t) t)
              (= (not x) nil))
  :proof   (@derive
            ((v (!= x nil) (= (iff x t) nil))      (build.theorem (theorem-iff-t-when-nil)))
            ((v (!= x nil) (!= (iff x t) t))       (build.disjoined-not-t-from-nil @-))
            ((v (= x nil) (= (not x) nil))         (build.theorem (theorem-not-when-not-nil)))
            ((v (= (not x) nil) (!= (iff x t) t))  (build.cut @- @--))
            ((v (!= (iff x t) t) (= (not x) nil))  (build.commute-or @-)))
  :minatbl ((iff . 2)
            (not  . 1)))

(defderiv rw.crewrite-rule-lemma-bldr
  :derive (= (not (? a)) nil)
  :from   ((proof x (= (iff (? a) t) t)))
  :proof  (@derive
           ((v (!= (iff x t) t) (= (not x) nil))           (build.theorem (rw.crewrite-rule-lemma)))
           ((v (!= (iff (? a) t) t) (= (not (? a)) nil))   (build.instantiation @- (@sigma (x . (? a)))))
           ((= (iff (? a) t) t)                            (@given x))
           ((= (not (? a)) nil)                            (build.modus-ponens @- @--)))
  :minatbl ((iff . 2)
            (not . 1)))

(defderiv rw.disjoined-crewrite-rule-lemma-bldr
  :derive (v P (= (not (? a)) nil))
  :from   ((proof x (v P (= (iff (? a) t) t))))
  :proof  (@derive
           ((v (!= (iff x t) t) (= (not x) nil))                (build.theorem (rw.crewrite-rule-lemma)))
           ((v (!= (iff (? a) t) t) (= (not (? a)) nil))        (build.instantiation @- (@sigma (x . (? a)))))
           ((v P (v (!= (iff (? a) t) t) (= (not (? a)) nil)))  (build.expansion (@formula P) @-))
           ((v P (= (iff (? a) t) t))                           (@given x))
           ((v P (= (not (? a)) nil))                           (build.disjoined-modus-ponens @- @--)))
  :minatbl ((iff . 2)
            (not . 1)))

(defund rw.crewrite-rule-lemma-list-bldr (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-atomicp (logic.strip-conclusions x))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                              (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions x))))))
  (if (consp x)
      (cons (rw.crewrite-rule-lemma-bldr (car x))
            (rw.crewrite-rule-lemma-list-bldr (cdr x)))
    nil))

(defobligations rw.crewrite-rule-lemma-list-bldr
  (rw.crewrite-rule-lemma-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-rule-lemma-list-bldr)))

 (defthm len-of-rw.crewrite-rule-lemma-list-bldr
   (equal (len (rw.crewrite-rule-lemma-list-bldr x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-rw.crewrite-rule-lemma-list-bldr
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))))
            (equal (logic.appeal-listp (rw.crewrite-rule-lemma-list-bldr x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-rw.crewrite-rule-lemma-list-bldr
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))))
            (equal (logic.strip-conclusions (rw.crewrite-rule-lemma-list-bldr x))
                   (logic.pequal-list (logic.negate-term-list (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                                      (repeat ''nil (len x)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable logic.negate-term))))

 (defthm@ forcing-logic.proof-listp-of-rw.crewrite-rule-lemma-list-bldr
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.crewrite-rule-lemma-list-bldr)
                        ))
            (equal (logic.proof-listp (rw.crewrite-rule-lemma-list-bldr x) axioms thms atbl)
                   t))))



(defund rw.disjoined-crewrite-rule-lemma-list-bldr (p x)
  (declare (xargs :guard (and (logic.formulap p)
                              (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x))
                              (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                              (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                              (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                              (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x)))))))
  (if (consp x)
      (cons (rw.disjoined-crewrite-rule-lemma-bldr (car x))
            (rw.disjoined-crewrite-rule-lemma-list-bldr p (cdr x)))
    nil))

(defobligations rw.disjoined-crewrite-rule-lemma-list-bldr
  (rw.disjoined-crewrite-rule-lemma-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.disjoined-crewrite-rule-lemma-list-bldr)))

 (defthm len-of-rw.disjoined-crewrite-rule-lemma-list-bldr
   (equal (len (rw.disjoined-crewrite-rule-lemma-list-bldr p x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-rw.disjoined-crewrite-rule-lemma-list-bldr
   (implies (force (and (logic.formulap p)
                        (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))))
            (equal (logic.appeal-listp (rw.disjoined-crewrite-rule-lemma-list-bldr p x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-rw.disjoined-crewrite-rule-lemma-list-bldr
   (implies (force (and (logic.formulap p)
                        (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))))
            (equal (logic.strip-conclusions (rw.disjoined-crewrite-rule-lemma-list-bldr p x))
                   (logic.por-list (repeat p (len x))
                                   (logic.pequal-list (logic.negate-term-list (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                                                      (repeat ''nil (len x))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable logic.negate-term))))

 (defthm@ forcing-logic.proof-listp-of-rw.disjoined-crewrite-rule-lemma-list-bldr
   (implies (force (and (logic.formulap p)
                        (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.disjoined-crewrite-rule-lemma-list-bldr)
                        ))
            (equal (logic.proof-listp (rw.disjoined-crewrite-rule-lemma-list-bldr p x) axioms thms atbl)
                   t))))




(defund rw.compile-crewrite-rule-trace-lemma1 (rule sigma proofs)
  (declare (xargs :guard (and (rw.rulep rule)
                              (logic.sigmap sigma)
                              (logic.appeal-listp proofs)
                              (logic.all-atomicp (logic.strip-conclusions proofs))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                              (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))
                                     (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                              (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs))))
                  :verify-guards nil))
  ;; 1. (not hyp1) != nil v ... v (not hypN) != nil v (equiv lhs rhs) != nil                          Given (Rule's theorem)
  ;; 2. (not hyp1/sigma) != nil v ... v (not hypN/sigma) != nil v (equiv lhs/sigma rhs/sigma) != nil  Instantiation
  ;; 3. [[ (iff hyp1/sigma t) = t, ..., (iff hypN/sigma t) = t ]]                                     Givens (Proofs)
  ;; 4. [[ (not hyp1/sigma) = nil, ..., (not hypN/sigma) = nil ]]                                     CRewrite Rule Lemma List Bldr
  ;; 5. (equiv lhs/sigma rhs/sigma) != nil                                                            Modus Ponens List
  (let* ((lhs    (rw.rule->lhs rule))
         (rhs    (rw.rule->rhs rule))
         (equiv  (rw.rule->equiv rule))
         (line-1 (build.theorem (clause.clause-formula (rw.rule-clause rule))))
         (line-2 (build.instantiation line-1 sigma))
         (line-4 (rw.crewrite-rule-lemma-list-bldr proofs))
         (line-5 (build.modus-ponens-list (logic.pnot (logic.pequal (logic.function equiv (list (logic.substitute lhs sigma)
                                                                                                (logic.substitute rhs sigma)))
                                                                    ''nil))
                                          line-4 line-2)))
    line-5))

(defobligations rw.compile-crewrite-rule-trace-lemma1
  (build.instantiation
   rw.crewrite-rule-lemma-list-bldr
   build.modus-ponens-list))

(encapsulate
 ()
 (local (in-theory (enable rw.compile-crewrite-rule-trace-lemma1
                           rw.rule-clause
                           redefinition-of-logic.term-list-formulas)))

 (local (defthm crock
          (implies (and (logic.all-negationsp a)
                        (logic.all-negationsp c)
                        (force (equal (len a) (len c))) ;; not always true, we force anyway
                        (force (equal (len b) (len d))) ;; not always true, we force anyway
                        (force (logic.formula-listp a))
                        (force (logic.formula-listp b))
                        (force (logic.formula-listp c))
                        (force (logic.formula-listp d)))
                   (equal (equal (logic.disjoin-formulas (app a b))
                                 (logic.disjoin-formulas (app c d)))
                          (and (equal (list-fix a) (list-fix c))
                               (equal (list-fix b) (list-fix d)))))))

 (local (defthm crock2
          (implies (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                          (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                   (equal (len proofs)
                          (len (rw.rule->hyps rule))))
          :hints(("Goal"
                  :in-theory (disable len-of-strip-firsts len-of-logic.substitute-list)
                  :use ((:instance len-of-strip-firsts
                                   (x (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (:instance len-of-logic.substitute-list
                                   (x (rw.hyp-list-terms (rw.rule->hyps rule)))))))))



 (defthm logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1
   (implies (force (and (rw.rulep rule)
                        (logic.sigmap sigma)
                        (logic.appeal-listp proofs)
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))
                               (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))))
            (equal (logic.appealp (rw.compile-crewrite-rule-trace-lemma1 rule sigma proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-crewrite-rule-trace-lemma1
   (implies (force (and (rw.rulep rule)
                        (logic.sigmap sigma)
                        (logic.appeal-listp proofs)
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))
                               (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))))
            (equal (logic.conclusion (rw.compile-crewrite-rule-trace-lemma1 rule sigma proofs))
                   (logic.pnot
                    (logic.pequal (logic.function (rw.rule->equiv rule)
                                                  (list (logic.substitute (rw.rule->lhs rule) sigma)
                                                        (logic.substitute (rw.rule->rhs rule) sigma)))
                                  ''nil))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (local (in-theory (enable rw.rule-env-okp)))

 (defthm@ logic.proofp-of-rw.compile-crewrite-rule-trace-lemma1
   (implies (force (and (rw.rulep rule)
                        (logic.sigmap sigma)
                        (logic.appeal-listp proofs)
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))
                               (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))
                        ;; ---
                        (rw.rule-atblp rule atbl)
                        (rw.rule-env-okp rule thms)
                        (logic.sigma-atblp sigma atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.compile-crewrite-rule-trace-lemma1)))
            (equal (logic.proofp (rw.compile-crewrite-rule-trace-lemma1 rule sigma proofs) axioms thms atbl)
                   t)))

 (verify-guards rw.compile-crewrite-rule-trace-lemma1))



(defund rw.compile-crewrite-rule-trace-lemma1-okp (x thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'rw.compile-crewrite-rule-trace-lemma1)
         (tuplep 2 extras)
         (let ((rule (first extras))
               (sigma (second extras)))
           (and (rw.rulep rule)
                (rw.rule-atblp rule atbl)
                (rw.rule-env-okp rule thms)
                (logic.sigmap sigma)
                (logic.sigma-atblp sigma atbl)
                (let ((conclusions (logic.strip-conclusions subproofs)))
                  (and (logic.all-atomicp conclusions)
                       (let ((lhses (logic.=lhses conclusions)))
                         (and (logic.all-functionsp lhses)
                              (let ((names (logic.strip-function-names lhses))
                                    (args  (logic.strip-function-args lhses)))
                                (and (all-equalp 'iff names)
                                     (all-equalp 2 (strip-lens args))
                                     (equal (strip-firsts args)
                                            (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                                     (all-equalp ''t (strip-seconds args))
                                     (all-equalp ''t (logic.=rhses conclusions))
                                     (equal conclusion
                                            (logic.pnot
                                             (logic.pequal (logic.function (rw.rule->equiv rule)
                                                                           (list (logic.substitute (rw.rule->lhs rule) sigma)
                                                                                 (logic.substitute (rw.rule->rhs rule) sigma)))
                                                           ''nil))))))))))))))

(defund rw.compile-crewrite-rule-trace-lemma1-high (rule sigma proofs)
  (declare (xargs :guard (and (rw.rulep rule)
                              (logic.sigmap sigma)
                              (logic.appeal-listp proofs)
                              (logic.all-atomicp (logic.strip-conclusions proofs))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                              (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))
                                     (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                              (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs))))))
  (logic.appeal 'rw.compile-crewrite-rule-trace-lemma1
                (logic.pnot (logic.pequal (logic.function (rw.rule->equiv rule)
                                                          (list (logic.substitute (rw.rule->lhs rule) sigma)
                                                                (logic.substitute (rw.rule->rhs rule) sigma)))
                                          ''nil))
                (list-fix proofs)
                (list rule sigma)))

(encapsulate
 ()
 (local (in-theory (enable rw.compile-crewrite-rule-trace-lemma1-okp)))

 (defthm booleanp-of-rw.compile-crewrite-rule-trace-lemma1-okp
   (equal (booleanp (rw.compile-crewrite-rule-trace-lemma1-okp x thms atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.compile-crewrite-rule-trace-lemma1-okp-of-logic.appeal-identity
   (equal (rw.compile-crewrite-rule-trace-lemma1-okp (logic.appeal-identity x) thms atbl)
          (rw.compile-crewrite-rule-trace-lemma1-okp x thms atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthmd lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
   (implies (and (rw.compile-crewrite-rule-trace-lemma1-okp x thms atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (rw.compile-crewrite-rule-trace-lemma1 (first (logic.extras x))
                                                           (second (logic.extras x))
                                                           (logic.provable-list-witness
                                                            (logic.strip-conclusions (logic.subproofs x))
                                                            axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
   (implies (and (rw.compile-crewrite-rule-trace-lemma1-okp x thms atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations rw.compile-crewrite-rule-trace-lemma1)
                 (equal (cdr (lookup 'not atbl)) 1))
            (equal (logic.proofp
                    (rw.compile-crewrite-rule-trace-lemma1 (first (logic.extras x))
                                                           (second (logic.extras x))
                                                           (logic.provable-list-witness
                                                            (logic.strip-conclusions (logic.subproofs x))
                                                            axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
   (implies (and (rw.compile-crewrite-rule-trace-lemma1-okp x thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations rw.compile-crewrite-rule-trace-lemma1)
                             (equal (cdr (lookup 'not atbl)) 1))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
                               lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (rw.compile-crewrite-rule-trace-lemma1 (first (logic.extras x))
                                                                       (second (logic.extras x))
                                                                       (logic.provable-list-witness
                                                                        (logic.strip-conclusions (logic.subproofs x))
                                                                        axioms thms atbl)))))))))





(defund rw.compile-crewrite-rule-trace-lemma2 (p rule sigma proofs)
  (declare (xargs :guard (and (logic.formulap p)
                              (rw.rulep rule)
                              (logic.sigmap sigma)
                              (logic.appeal-listp proofs)
                              (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                              (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                              (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                              (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                                     (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                              (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                              (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs)))))
                  :verify-guards nil))
  ;; 1. (not hyp1) != nil v ... v (not hypN) != nil v (equiv lhs rhs) != nil                              Given (Rule's theorem)
  ;; 2. (not hyp1/sigma) != nil v ... v (not hypN/sigma) != nil v (equiv lhs/sigma rhs/sigma) != nil      Instantiation
  ;; 3. P v (not hyp1/sigma) != nil v ... v (not hypN/sigma) != nil v (equiv lhs/sigma rhs/sigma) != nil  Expansion
  ;; 4. [[ P v (iff hyp1/sigma t) = t, ..., P v (iff hypN/sigma t) = t ]]                                 Givens (Proofs)
  ;; 5. [[ P v (not hyp1/sigma) = nil, ..., P v (not hypN/sigma) = nil ]]                                 DJ CRewrite Rule Lemma List Bldr
  ;; 6. P v (equiv lhs/sigma rhs/sigma) != nil                                                            DJ Modus Ponens List
  (let* ((lhs    (rw.rule->lhs rule))
         (rhs    (rw.rule->rhs rule))
         (equiv  (rw.rule->equiv rule))
         (line-1 (build.theorem (clause.clause-formula (rw.rule-clause rule))))
         (line-2 (build.instantiation line-1 sigma))
         (line-3 (build.expansion P line-2))
         (line-5 (rw.disjoined-crewrite-rule-lemma-list-bldr p proofs))
         (line-6 (build.disjoined-modus-ponens-list
                  (logic.pnot (logic.pequal (logic.function equiv (list (logic.substitute lhs sigma)
                                                                        (logic.substitute rhs sigma)))
                                            ''nil))
                  line-5 line-3)))
    line-6))

(defobligations rw.compile-crewrite-rule-trace-lemma2
  (build.expansion
   rw.disjoined-crewrite-rule-lemma-list-bldr
   build.disjoined-modus-ponens-list))

(encapsulate
 ()
 (local (in-theory (enable rw.compile-crewrite-rule-trace-lemma2
                           rw.rule-clause
                           redefinition-of-logic.term-list-formulas)))

 (local (defthm crock
          (implies (and (logic.all-negationsp a)
                        (logic.all-negationsp c)
                        (force (equal (len a) (len c))) ;; not always true, we force anyway
                        (force (equal (len b) (len d))) ;; not always true, we force anyway
                        (force (logic.formula-listp a))
                        (force (logic.formula-listp b))
                        (force (logic.formula-listp c))
                        (force (logic.formula-listp d)))
                   (equal (equal (logic.disjoin-formulas (app a b))
                                 (logic.disjoin-formulas (app c d)))
                          (and (equal (list-fix a) (list-fix c))
                               (equal (list-fix b) (list-fix d)))))))

 (local (defthm crock2
          (implies (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                          (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                   (equal (len proofs)
                          (len (rw.rule->hyps rule))))
          :hints(("Goal"
                  :in-theory (disable len-of-strip-firsts len-of-logic.substitute-list)
                  :use ((:instance len-of-strip-firsts
                                   (x (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (:instance len-of-logic.substitute-list
                                   (x (rw.hyp-list-terms (rw.rule->hyps rule)))))))))

 (defthm forcing-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma2
   (implies (force (and (logic.formulap p)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (logic.appeal-listp proofs)
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                               (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))
                        ))
            (equal (logic.appealp (rw.compile-crewrite-rule-trace-lemma2 p rule sigma proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-crewrite-rule-trace-lemma2
   (implies (force (and (logic.formulap p)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (logic.appeal-listp proofs)
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                               (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))
                        ))
            (equal (logic.conclusion (rw.compile-crewrite-rule-trace-lemma2 p rule sigma proofs))
                   (logic.por p
                              (logic.pnot
                               (logic.pequal (logic.function (rw.rule->equiv rule)
                                                             (list (logic.substitute (rw.rule->lhs rule) sigma)
                                                                   (logic.substitute (rw.rule->rhs rule) sigma)))
                                             ''nil)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.compile-crewrite-rule-trace-lemma2
   (implies (force (and (logic.formulap p)
                        (rw.rulep rule)
                        (logic.sigmap sigma)
                        (logic.appeal-listp proofs)
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                               (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                        (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))
                        ;; ---
                        (logic.formula-atblp p atbl)
                        (rw.rule-atblp rule atbl)
                        (rw.rule-env-okp rule thms)
                        (logic.sigma-atblp sigma atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.compile-crewrite-rule-trace-lemma2)
                        ))
            (equal (logic.proofp (rw.compile-crewrite-rule-trace-lemma2 p rule sigma proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.rule-env-okp))))

 (verify-guards rw.compile-crewrite-rule-trace-lemma2))



(defund rw.compile-crewrite-rule-trace-lemma2-okp (x thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'rw.compile-crewrite-rule-trace-lemma2)
         (tuplep 3 extras)
         (let ((p     (first extras))
               (rule  (second extras))
               (sigma (third extras)))
           (and (logic.formulap p)
                (logic.formula-atblp p atbl)
                (rw.rulep rule)
                (rw.rule-atblp rule atbl)
                (rw.rule-env-okp rule thms)
                (logic.sigmap sigma)
                (logic.sigma-atblp sigma atbl)
                (let ((conclusions (logic.strip-conclusions subproofs)))
                  (and (logic.all-disjunctionsp conclusions)
                       (let ((rhses (logic.vrhses conclusions)))
                         (and (all-equalp p (logic.vlhses conclusions))
                              (logic.all-atomicp rhses)
                              (let ((lhses-of-rhses (logic.=lhses rhses)))
                                (and (logic.all-functionsp lhses-of-rhses)
                                     (all-equalp 'iff (logic.strip-function-names lhses-of-rhses))
                                     (let ((args (logic.strip-function-args lhses-of-rhses)))
                                       (and (all-equalp 2 (strip-lens args))
                                            (equal (strip-firsts args)
                                                   (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                                            (all-equalp ''t (strip-seconds args))
                                            (all-equalp ''t (logic.=rhses rhses))
                                            (equal conclusion
                                                   (logic.por p
                                                              (logic.pnot
                                                               (logic.pequal (logic.function (rw.rule->equiv rule)
                                                                                             (list (logic.substitute (rw.rule->lhs rule) sigma)
                                                                                                   (logic.substitute (rw.rule->rhs rule) sigma)))
                                                                             ''nil)))))))))))))))))


(defund rw.compile-crewrite-rule-trace-lemma2-high (p rule sigma proofs)
  (declare (xargs :guard (and (logic.formulap p)
                              (rw.rulep rule)
                              (logic.sigmap sigma)
                              (logic.appeal-listp proofs)
                              (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                              (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                              (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                              (equal (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                                     (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma))
                              (all-equalp ''t (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                              (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs)))))))
  (logic.appeal 'rw.compile-crewrite-rule-trace-lemma2
                (logic.por p (logic.pnot (logic.pequal (logic.function (rw.rule->equiv rule)
                                                                       (list (logic.substitute (rw.rule->lhs rule) sigma)
                                                                             (logic.substitute (rw.rule->rhs rule) sigma)))
                                                       ''nil)))
                (list-fix proofs)
                (list p rule sigma)))

(encapsulate
 ()
 (local (in-theory (enable rw.compile-crewrite-rule-trace-lemma2-okp)))

 (defthm booleanp-of-rw.compile-crewrite-rule-trace-lemma2-okp
   (equal (booleanp (rw.compile-crewrite-rule-trace-lemma2-okp x thms atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.compile-crewrite-rule-trace-lemma2-okp-of-logic.appeal-identity
   (equal (rw.compile-crewrite-rule-trace-lemma2-okp (logic.appeal-identity x) thms atbl)
          (rw.compile-crewrite-rule-trace-lemma2-okp x thms atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
   (implies (and (rw.compile-crewrite-rule-trace-lemma2-okp x thms atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (rw.compile-crewrite-rule-trace-lemma2 (first (logic.extras x))
                                                           (second (logic.extras x))
                                                           (third (logic.extras x))
                                                           (logic.provable-list-witness
                                                            (logic.strip-conclusions (logic.subproofs x))
                                                            axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
   (implies (and (rw.compile-crewrite-rule-trace-lemma2-okp x thms atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations rw.compile-crewrite-rule-trace-lemma2)
                 (equal (cdr (lookup 'not atbl)) 1))
            (equal (logic.proofp
                    (rw.compile-crewrite-rule-trace-lemma2 (first (logic.extras x))
                                                           (second (logic.extras x))
                                                           (third (logic.extras x))
                                                           (logic.provable-list-witness
                                                            (logic.strip-conclusions (logic.subproofs x))
                                                            axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
   (implies (and (rw.compile-crewrite-rule-trace-lemma2-okp x thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations rw.compile-crewrite-rule-trace-lemma2)
                             (equal (cdr (lookup 'not atbl)) 1))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
                               lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (rw.compile-crewrite-rule-trace-lemma2 (first (logic.extras x))
                                                                       (second (logic.extras x))
                                                                       (third (logic.extras x))
                                                                       (logic.provable-list-witness
                                                                        (logic.strip-conclusions (logic.subproofs x))
                                                                        axioms thms atbl)))))))))








(defund@ rw.compile-crewrite-rule-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.crewrite-rule-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  ;; Let the rule be [| rhyp1, ..., rhypN |] ==> (REQUIV rlhs rrhs) = t.
  ;; Goal: assms v (TEQUIV rlhs/sigma rrhs/sigma) = t
  ;; Proofs are: assms v (iff rhypi/sigma t) = t
  (let* ((hypbox  (rw.trace->hypbox x))
         (iffp    (rw.trace->iffp x))
         (extras  (rw.trace->extras x))
         (rule    (first extras))
         (sigma   (second extras)))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (let (;; (REQUIV lhs/sigma rhs/sigma) != nil
              (main-proof (rw.compile-crewrite-rule-trace-lemma1 rule sigma proofs)))
          (if iffp
              (if (equal (rw.rule->equiv rule) 'equal)
                  ;; to cause problems, try (equal (rw.rule->equiv x) 'equal) instead
                  (build.iff-from-equal (build.equal-t-from-not-nil main-proof))
                (build.iff-t-from-not-nil main-proof))
            (build.equal-t-from-not-nil main-proof)))
      (let* ((f-nhyps    (rw.hypbox-formula hypbox))
             ;; nhyps v (REQUIV lhs/sigma rhs/sigma) != nil
             (main-proof (rw.compile-crewrite-rule-trace-lemma2 f-nhyps rule sigma proofs)))
          (if iffp
              (if (equal (rw.rule->equiv rule) 'equal)
                  ;; to cause problems, try (equal (rw.rule->equiv x) 'equal) instead
                  (build.disjoined-iff-from-equal (build.disjoined-equal-t-from-not-nil main-proof))
                (build.disjoined-iff-t-from-not-nil main-proof))
            (build.disjoined-equal-t-from-not-nil main-proof))))))

(defobligations rw.compile-crewrite-rule-trace
  (rw.compile-crewrite-rule-trace-lemma1
   rw.compile-crewrite-rule-trace-lemma2
   build.disjoined-equal-t-from-not-nil
   build.disjoined-iff-t-from-not-nil
   build.disjoined-iff-from-equal
   build.equal-t-from-not-nil
   build.iff-t-from-not-nil
   build.iff-from-equal))

(encapsulate
 ()
 (local (in-theory (enable rw.compile-crewrite-rule-trace rw.crewrite-rule-tracep)))

 (defthmd lemma-1-for-rw.compile-crewrite-rule-trace
   (implies (and (equal (rw.trace-list-conclusion-formulas subtraces)
                        (logic.vrhses (logic.strip-conclusions proofs)))
                 (all-equalp t (rw.trace-list-iffps subtraces))
                 (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                 (rw.hypbox->right hypbox)
                 (force (rw.trace-listp subtraces)))
            (equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                   (repeat 'iff (len subtraces)))))

 (defthmd lemma-2-for-rw.compile-crewrite-rule-trace
   (implies (and (equal (rw.trace-list-conclusion-formulas subtraces)
                        (logic.vrhses (logic.strip-conclusions proofs)))
                 (all-equalp t (rw.trace-list-iffps subtraces))
                 (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                 (rw.hypbox->left hypbox)
                 (force (rw.trace-listp subtraces)))
            (equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                   (repeat 'iff (len subtraces)))))

 (defthmd lemma-3-for-rw.compile-crewrite-rule-trace
   (implies (and (equal (rw.trace-list-conclusion-formulas subtraces)
                        (logic.vrhses (logic.strip-conclusions proofs)))
                 (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                 (rw.hypbox->right hypbox)
                 (force (rw.trace-listp subtraces)))
            (equal (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                   (repeat '2 (len subtraces)))))

 (defthmd lemma-4-for-rw.compile-crewrite-rule-trace
   (implies (and (equal (rw.trace-list-conclusion-formulas subtraces)
                        (logic.vrhses (logic.strip-conclusions proofs)))
                 (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                 (rw.hypbox->left hypbox)
                 (force (rw.trace-listp subtraces)))
            (equal (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                   (repeat '2 (len subtraces)))))

 (defthmd lemma-5-for-rw.compile-crewrite-rule-trace
   (IMPLIES (AND (EQUAL (RW.TRACE-LIST-CONCLUSION-FORMULAS subtraces)
                        (LOGIC.STRIP-CONCLUSIONS PROOFS))
                 (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                 (all-equalp t (rw.trace-list-iffps subtraces))
                 (not (rw.hypbox->left hypbox))
                 (not (rw.hypbox->right hypbox))
                 (force (rw.trace-listp subtraces)))
            (equal (LOGIC.STRIP-FUNCTION-NAMES (LOGIC.=LHSES (LOGIC.STRIP-CONCLUSIONS PROOFS)))
                   (repeat 'iff (len subtraces))))
   :hints(("Goal"
           :in-theory (disable LOGIC.STRIP-FUNCTION-NAMES-OF-RW.TRACE-LIST-CONCLUSION-FORMULAS-WHEN-ALL-IFFP)
           :use ((:instance LOGIC.STRIP-FUNCTION-NAMES-OF-RW.TRACE-LIST-CONCLUSION-FORMULAS-WHEN-ALL-IFFP
                            (x subtraces))))))

 (defthmd lemma-6-for-rw.compile-crewrite-rule-trace
   (IMPLIES (AND (EQUAL (RW.TRACE-LIST-CONCLUSION-FORMULAS subtraces)
                        (LOGIC.STRIP-CONCLUSIONS PROOFS))
                 (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                 (not (rw.hypbox->left hypbox))
                 (not (rw.hypbox->right hypbox))
                 (force (rw.trace-listp subtraces)))
            (equal (STRIP-LENS (LOGIC.STRIP-FUNCTION-ARGS (LOGIC.=LHSES (LOGIC.STRIP-CONCLUSIONS PROOFS))))
                   (repeat 2 (len subtraces))))
   :hints(("Goal"
           :in-theory (disable LOGIC.STRIP-LENS-OF-LOGIC.STRIP-FUNCTION-ARGS-OF-RW.TRACE-LIST-CONCLUSION-FORMULAS)
           :use ((:instance LOGIC.STRIP-LENS-OF-LOGIC.STRIP-FUNCTION-ARGS-OF-RW.TRACE-LIST-CONCLUSION-FORMULAS
                            (x subtraces))))))

 (local (in-theory (enable lemma-1-for-rw.compile-crewrite-rule-trace
                           lemma-2-for-rw.compile-crewrite-rule-trace
                           lemma-3-for-rw.compile-crewrite-rule-trace
                           lemma-4-for-rw.compile-crewrite-rule-trace
                           lemma-5-for-rw.compile-crewrite-rule-trace
                           lemma-6-for-rw.compile-crewrite-rule-trace)))

 (defthm rw.compile-crewrite-rule-trace-under-iff
   (iff (rw.compile-crewrite-rule-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-logic.appealp-of-rw.compile-crewrite-rule-trace
   (implies (force (and (rw.tracep x)
                        (rw.crewrite-rule-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-crewrite-rule-trace x proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-crewrite-rule-trace
   (implies (force (and (rw.tracep x)
                        (rw.crewrite-rule-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-crewrite-rule-trace x proofs))
                   (rw.trace-formula x))))

 (defthm@ forcing-logic.proofp-of-rw.compile-crewrite-rule-trace
   (implies (force (and (rw.tracep x)
                        (rw.crewrite-rule-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (rw.crewrite-rule-trace-env-okp x thms atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.compile-crewrite-rule-trace)
                        ))
            (equal (logic.proofp (rw.compile-crewrite-rule-trace x proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.crewrite-rule-trace-env-okp))))

 (verify-guards rw.compile-crewrite-rule-trace))


