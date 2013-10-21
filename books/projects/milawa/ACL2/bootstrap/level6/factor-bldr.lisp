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
(include-book "factor")
(%interactive)


(%autoadmit binding-formula)
(%enable default binding-formula)

(defsection assignment-formulas
 (local (%disable default binding-formula))
 (%defprojection :list (assignment-formulas x)
                 :element (binding-formula x)))

(%autoprove forcing-logic.formulap-listp-of-assignment-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.formula-atblp-listp-of-assignment-formulas
            (%cdr-induction x))


;; We already introduced these earlier.
;; (%defderiv clause.factor-bldr-lemma-1 :omit-okp t)
;; (%defderiv clause.factor-bldr-lemma-2 :omit-okp t)


(%autoadmit clause.flag-factor-bldr)
(%autoadmit clause.factor-bldr)
(%autoadmit clause.factor-list-bldr)

(%autoprove definition-of-clause.factor-bldr
            (%restrict default clause.flag-factor-bldr (equal x 'x))
            (%enable default clause.factor-bldr clause.factor-list-bldr)
            (%auto :strategy (cleanup urewrite split)))

(%autoprove definition-of-clause.factor-list-bldr
            (%restrict default clause.flag-factor-bldr (equal x 'x))
            (%enable default clause.factor-bldr clause.factor-list-bldr)
            (%auto :strategy (cleanup urewrite split)))

(%autoprove forcing-clause.flag-factor-bldr-of-term-removal
            (%enable default clause.factor-bldr))

(%autoprove clause.flag-factor-bldr-of-list-removal
            ;; BOZO rename should be called forcing-blah
            (%enable default clause.factor-list-bldr))

(%autoprove clause.factor-list-bldr-when-not-consp
            (%restrict default definition-of-clause.factor-list-bldr (equal x 'x)))

(%autoprove clause.factor-list-bldr-of-cons
            (%restrict default definition-of-clause.factor-list-bldr (equal x '(cons a x))))

(encapsulate
 ()
 (%autoprove lemma-for-nil-preservingp-of-clause.factor-list-bldr
             (%restrict default definition-of-clause.factor-bldr (equal x ''nil)))
 (local (%enable default lemma-for-nil-preservingp-of-clause.factor-list-bldr))
 (%defprojection
  :list (clause.factor-list-bldr x assignment hyps hyps-formula)
  :element (clause.factor-bldr x assignment hyps hyps-formula)
  :nil-preservingp t))


;; This is super-aggressive forcing, but we should only be looking for the
;; right terms during these proofs.
(%autoprove lemma-forcing-memberp-of-pequal-a-nil-in-assignment-formulas
            (%cdr-induction x))

;; This is super-aggressive forcing, but we should only be looking for the
;; right terms during these proofs.
(%autoprove lemma-forcing-memberp-of-logic.pnot-pequal-a-nil-in-assignment-formulas
            (%cdr-induction x))





(%autoprove lemma-1-for-forcing-logic.appealp-of-clause.factor-bldr)
(%autoprove lemma-2-for-forcing-logic.appealp-of-clause.factor-bldr)
(%autoprove lemma-3-for-forcing-logic.appealp-of-clause.factor-bldr)

(%autoprove lemma-1-for-forcing-logic.conclusion-of-clause.factor-bldr
            (%forcingp nil))
(%autoprove lemma-2-for-forcing-logic.conclusion-of-clause.factor-bldr
            (%forcingp nil))
(%autoprove lemma-3-for-forcing-logic.conclusion-of-clause.factor-bldr
            (%forcingp nil))



(defthm clause.factor-bldr-when-logic.constantp
  (implies (logic.constantp x)
           (equal (clause.factor-bldr x assignment)
                  (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                         (hyps-formula  (logic.disjoin-formulas hyps)))
                    (build.expansion hyps-formula (build.reflexivity x)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))

(defthm clause.factor-bldr-when-logic.variablep
  (implies (logic.variablep x)
           (equal (clause.factor-bldr x assignment)
                  (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                         (hyps-formula  (logic.disjoin-formulas hyps)))
                    (build.expansion hyps-formula (build.reflexivity x)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))

(defthm clause.factor-bldr-when-non-if-logic.functionp
  (implies (and (logic.functionp x)
                (not (equal (logic.function-name x) 'if)))
           (equal (clause.factor-bldr x assignment)
                  (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                         (hyps-formula  (logic.disjoin-formulas hyps)))
                    (build.disjoined-pequal-by-args (logic.function-name x)
                                                    hyps-formula
                                                    (clause.factor-list-bldr (logic.function-args x) assignment)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))

(defthm clause.factor-bldr-when-bad-args-logic.functionp
  (implies (and (logic.functionp x)
                (not (equal (len (logic.function-args x)) 3)))
           (equal (clause.factor-bldr x assignment)
                  (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                         (hyps-formula  (logic.disjoin-formulas hyps)))
                    (build.disjoined-pequal-by-args (logic.function-name x)
                                                    hyps-formula
                                                    (clause.factor-list-bldr (logic.function-args x) assignment)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))

(defthm clause.factor-bldr-when-if
  (implies (and (logic.functionp x)
                (equal (logic.function-name x) 'if)
                (equal (len (logic.function-args x)) 3))
           (equal (clause.factor-bldr x assignment)
                  (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                         (hyps-formula  (logic.disjoin-formulas hyps))
                         (args          (logic.function-args x))
                         (a-proof       (clause.factor-bldr (first args) assignment))
                         (a-prime       (logic.=rhs (logic.vrhs (logic.conclusion a-proof))))
                         (binding       (lookup a-prime assignment)))
                    (if binding
                        (if (cdr binding)
                            (clause.factor-bldr-lemma-1 (build.multi-assoc-expansion (build.commute-or (build.propositional-schema (logic.pequal a-prime ''nil))) hyps)
                                                        a-proof
                                                        (clause.factor-bldr (second args) assignment)
                                                        (third args))
                          (clause.factor-bldr-lemma-2 (build.multi-assoc-expansion (build.propositional-schema (logic.pequal a-prime ''nil)) hyps)
                                                      a-proof
                                                      (clause.factor-bldr (third args) assignment)
                                                      (second args)))
                      (build.disjoined-pequal-by-args 'if
                                                      hyps-formula
                                                      (list a-proof
                                                            (clause.factor-bldr (second args) assignment)
                                                            (clause.factor-bldr (third args) assignment)))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal"
          :in-theory (e/d (definition-of-clause.factor-bldr)
                          ((:executable-counterpart ACL2::force)))
          :expand (clause.factor-bldr x assignment))))

(defthm clause.factor-bldr-when-logic.lambdap
  (implies (logic.lambdap x)
           (equal (clause.factor-bldr x assignment)
                  (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                         (hyps-formula  (logic.disjoin-formulas hyps)))
                    (build.disjoined-lambda-pequal-by-args (logic.lambda-formals x)
                                                           (logic.lambda-body x)
                                                           hyps-formula
                                                           (clause.factor-list-bldr (logic.lambda-actuals x) assignment)))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))

(defthm clause.factor-bldr-when-degenerate
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (clause.factor-bldr x assignment)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))


(%autoprove clause.factor-bldr-when-logic.constantp
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))

(%autoprove clause.factor-bldr-when-logic.variablep
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))

(%autoprove clause.factor-bldr-when-non-if-logic.functionp
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))

(%autoprove clause.factor-bldr-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))

(%autoprove clause.factor-bldr-when-if
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))

(%autoprove clause.factor-bldr-when-logic.lambdap
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))

(%autoprove clause.factor-bldr-when-degenerate
            (%restrict default definition-of-clause.factor-bldr (equal x 'x)))



(%create-theory clause.factor-bldr-openers)
(%enable clause.factor-bldr-openers
         clause.factor-bldr-when-logic.constantp
         clause.factor-bldr-when-logic.variablep
         clause.factor-bldr-when-non-if-logic.functionp
         clause.factor-bldr-when-bad-args-logic.functionp
         clause.factor-bldr-when-if
         clause.factor-bldr-when-logic.lambdap
         clause.factor-bldr-when-degenerate)

(%create-theory clause.factor-openers)
(%enable clause.factor-openers
         clause.factor-when-logic.constantp
         clause.factor-when-logic.variablep
         clause.factor-when-non-if-logic.functionp
         clause.factor-when-bad-args-logic.functionp
         clause.factor-when-if-expression
         clause.factor-when-logic.lambdap
         clause.factor-when-degenerate)


(%autoprove lemma-for-forcing-logic.appealp-of-clause.factor-bldr
            (%clause.simple-term-induction flag x)
            (%enable default
                     lemma-1-for-forcing-logic.appealp-of-clause.factor-bldr
                     lemma-2-for-forcing-logic.appealp-of-clause.factor-bldr
                     lemma-3-for-forcing-logic.appealp-of-clause.factor-bldr
                     lemma-1-for-forcing-logic.conclusion-of-clause.factor-bldr
                     lemma-2-for-forcing-logic.conclusion-of-clause.factor-bldr
                     lemma-3-for-forcing-logic.conclusion-of-clause.factor-bldr
                     lemma-forcing-memberp-of-pequal-a-nil-in-assignment-formulas
                     lemma-forcing-memberp-of-logic.pnot-pequal-a-nil-in-assignment-formulas)
            (%disable default
                      clause.factor-openers
                      clause.factor-bldr-openers
                      forcing-equal-of-logic.por-rewrite-two
                      forcing-equal-of-logic.por-rewrite
                      forcing-equal-of-logic.pequal-rewrite-two
                      forcing-equal-of-logic.pequal-rewrite
                      forcing-equal-of-logic.pnot-rewrite-two
                      forcing-equal-of-logic.pnot-rewrite
                      forcing-equal-of-logic.por-list-rewrite-alt
                      forcing-equal-of-logic.por-list-rewrite
                      forcing-equal-of-logic.pequal-list-rewrite
                      forcing-equal-of-logic.pequal-list-rewrite-alt
                      equal-of-cons-rewrite
                      equal-of-booleans-rewrite
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      not-equal-when-less
                      not-equal-when-less-two
                      equal-of-non-cons-and-cons-cheap
                      equal-of-symbol-and-non-symbol-cheap
                      equal-of-non-symbol-and-symbol-cheap
                      equal-of-cons-and-non-cons-cheap
                      equal-of-nat-and-non-nat-cheap
                      equal-of-non-nat-and-nat-cheap)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%enable default
                     forcing-equal-of-logic.por-rewrite-two
                     forcing-equal-of-logic.por-rewrite
                     forcing-equal-of-logic.pequal-rewrite-two
                     forcing-equal-of-logic.pequal-rewrite
                     forcing-equal-of-logic.por-list-rewrite-alt
                     forcing-equal-of-logic.por-list-rewrite
                     forcing-equal-of-logic.pequal-list-rewrite
                     forcing-equal-of-logic.pequal-list-rewrite-alt)
            (%crewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%enable default
                     aggressive-equal-of-logic.pequals
                     aggressive-equal-of-logic.pors
                     aggressive-equal-of-logic.pnots
                     equal-of-cons-rewrite
                     equal-of-booleans-rewrite)
            (%crewrite default)
            (%auto :strategy (cleanup split urewrite))
            (%enable default
                     clause.factor-openers
                     clause.factor-bldr-openers)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free)
            (%crewrite default))

(%autoprove forcing-logic.appealp-of-clause.factor-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.factor-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-clause.factor-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.factor-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.appeal-listp-of-clause.factor-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.factor-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-clause.factor-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.factor-bldr)
                             (flag 'list))))



(%autoprove lemma-1-for-forcing-logic.proofp-of-clause.factor-bldr)

(%autoprove lemma-2-for-forcing-logic.proofp-of-clause.factor-bldr)

(%autoprove lemma-3-for-forcing-logic.proofp-of-clause.factor-bldr)

(%autoprove lemma-for-forcing-logic.proofp-of-clause.factor-bldr
            (%clause.simple-term-induction flag x)
            (%enable default
                     lemma-1-for-forcing-logic.proofp-of-clause.factor-bldr
                     lemma-2-for-forcing-logic.proofp-of-clause.factor-bldr
                     lemma-3-for-forcing-logic.proofp-of-clause.factor-bldr
                     lemma-forcing-memberp-of-pequal-a-nil-in-assignment-formulas
                     lemma-forcing-memberp-of-logic.pnot-pequal-a-nil-in-assignment-formulas)
            (%disable default
                      forcing-equal-of-logic.pequal-list-rewrite
                      forcing-equal-of-logic.por-list-rewrite
                      equal-of-cons-rewrite
                      equal-of-booleans-rewrite
                      aggressive-equal-of-logic.pequals
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      not-equal-when-less
                      not-equal-when-less-two
                      equal-of-non-cons-and-cons-cheap
                      equal-of-symbol-and-non-symbol-cheap
                      equal-of-non-symbol-and-symbol-cheap
                      equal-of-cons-and-non-cons-cheap
                      equal-of-nat-and-non-nat-cheap
                      equal-of-non-nat-and-nat-cheap))

(%autoprove forcing-logic.proofp-of-clause.factor-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-clause.factor-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.proof-listp-of-clause.factor-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-clause.factor-bldr)
                             (flag 'list))))



