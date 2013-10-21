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
(include-book "../defderiv/top")
(include-book "axioms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "basic.tex")

(dd.write "Builders are functions that build proofs from their inputs.  The
simplest builders correspond to the basic axioms and rules of inference, while
more complex builders can generate long sequences of proof steps.  Builders
correspond to derived rules of inference in logic.")

(dd.write "During bootstrapping, we want our builders to produce short proofs.
Next to most derivations, we write down how many steps will be introduced by
using the derivation.  Sometimes we can optimize special cases (e.g., we don't
need to add any steps at all to commute a proof of $a = a$), but here we only
show the steps and costs for the general case.")



(defund build.axiom (a)
  (declare (xargs :guard (logic.formulap a)))
  (logic.appeal 'axiom a nil nil))

(encapsulate
 ()
 (local (in-theory (enable build.axiom)))

 (defthm build.axiom-under-iff
   (iff (build.axiom a)
        t))

 (defthm logic.method-of-build.axiom
   (equal (logic.method (build.axiom a))
          'axiom))

 (defthm logic.conclusion-of-build.axiom
   (equal (logic.conclusion (build.axiom a))
          a))

 (defthm logic.subproofs-of-build.axiom
   (equal (logic.subproofs (build.axiom a))
          nil))

 (defthm logic.extras-of-build.axiom
   (equal (logic.extras (build.axiom a))
          nil))

 (defthm forcing-logic.appealp-of-build.axiom
   (implies (force (logic.formulap a))
            (equal (logic.appealp (build.axiom a))
                   t)))

 (defthm forcing-logic.proofp-of-build.axiom
   (implies (force (and (memberp a axioms)
                        (logic.formula-atblp a atbl)))
            (equal (logic.proofp (build.axiom a) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.axiom-okp)))))



(defund build.theorem (a)
  (declare (xargs :guard (logic.formulap a)))
  (logic.appeal 'theorem a nil nil))

(encapsulate
 ()
 (local (in-theory (enable build.theorem)))

 (defthm build.theorem-under-iff
   (iff (build.theorem a)
        t))

 (defthm logic.method-of-build.theorem
   (equal (logic.method (build.theorem a))
          'theorem))

 (defthm logic.conclusion-of-build.theorem
   (equal (logic.conclusion (build.theorem a))
          a))

 (defthm logic.subproofs-of-build.theorem
   (equal (logic.subproofs (build.theorem a))
          nil))

 (defthm logic.extras-of-build.theorem
   (equal (logic.extras (build.theorem a))
          nil))

 (defthm forcing-logic.appealp-of-build.theorem
   (implies (force (logic.formulap a))
            (equal (logic.appealp (build.theorem a))
                   t)))

 (defthm forcing-logic.proofp-of-build.theorem
   (implies (force (and (logic.formula-atblp a atbl)
                        (memberp a thms)))
            (equal (logic.proofp (build.theorem a) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.theorem-okp)))))



(defund@ build.propositional-schema (a)
  (declare (xargs :guard (logic.formulap a)))
  (logic.appeal 'propositional-schema
                (logic.por (logic.pnot a) a)
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.propositional-schema)))

 (defthm build.propositional-schema-under-iff
   (iff (build.propositional-schema a)
        t))

 (defthm logic.method-of-build.propositional-schema
   (equal (logic.method (build.propositional-schema a))
          'propositional-schema))

 (defthm logic.conclusion-of-build.propositional-schema
   (equal (logic.conclusion (build.propositional-schema a))
          (logic.por (logic.pnot a) a)))

 (defthm logic.subproofs-of-build.propositional-schema
   (equal (logic.subproofs (build.propositional-schema a))
          nil))

 (defthm logic.extras-of-build.propositional-schema
   (equal (logic.extras (build.propositional-schema a))
          nil))

 (defthm forcing-logic.appealp-of-build.propositional-schema
   (implies (force (logic.formulap a))
            (equal (logic.appealp (build.propositional-schema a))
                   t)))

 (defthm forcing-logic.proofp-of-build.propositional-schema
   (implies (force (logic.formula-atblp a atbl))
            (equal (logic.proofp (build.propositional-schema a) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.propositional-schema-okp)))))



(defund@ build.cut (x y)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.appealp y)
                              (@match (proof x (v A B))
                                      (proof y (v (! A) C))))))
  (logic.appeal 'cut
                (@formula (v B C))
                (list x y)
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.cut)))

 (defthm build.cut-under-iff
   (iff (build.cut x y)
        t))

 (defthm logic.method-of-build.cut
   (equal (logic.method (build.cut x y))
          'cut))

 (defthm@ logic.conclusion-of-cut
   (@extend ((proof x (v A B))
             (proof y (v (! A) C)))
            (equal (logic.conclusion (build.cut x y))
                   (@formula (v B C)))))

 (defthm logic.subproofs-of-build.cut
   (equal (logic.subproofs (build.cut x y))
          (list x y)))

 (defthm logic.extras-of-build.cut
   (equal (logic.extras (build.cut x y))
          nil))

 (defthm@ forcing-logic.appealp-of-build.cut
   (implies (force (and (logic.appealp x)
                        (logic.appealp y)
                        (@match (proof x (v A B))
                                (proof y (v (! A) C)))))
            (equal (logic.appealp (build.cut x y))
                   t)))

 (defthm@ forcing-logic.proofp-of-build.cut
   (implies (force (and ;(logic.appealp x)
                        ;(logic.appealp y)
                        (@match (proof x (v A B))
                                (proof y (v (! A) C)))
                        (logic.proofp x axioms thms atbl)
                        (logic.proofp y axioms thms atbl)))
            (equal (logic.proofp (build.cut x y) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (e/d (definition-of-logic.proofp
                                    logic.appeal-step-okp
                                    logic.cut-okp)
                                  (FORCING-TRUE-LISTP-OF-LOGIC.SUBPROOFS)
                                  )))))




(defund@ build.contraction (x)
  (declare (xargs :guard (and (logic.appealp x)
                              (@match (proof x (v A A))))))
  (logic.appeal 'contraction
                (@formula A)
                (list x)
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.contraction)))

 (defthm build.contraction-under-iff
   (iff (build.contraction x)
        t))

 (defthm logic.method-of-build.contraction
   (equal (logic.method (build.contraction x))
          'contraction))

 (defthm@ logic.conclusion-of-build.contraction
   (@extend ((proof x (v A A)))
            (equal (logic.conclusion (build.contraction x))
                   (@formula A))))

 (defthm logic.subproofs-of-build.contraction
   (equal (logic.subproofs (build.contraction x))
          (list x)))

 (defthm logic.extras-of-build.contraction
   (equal (logic.extras (build.contraction x))
          nil))

 (defthm@ forcing-logic.appealp-of-build.contraction
   (implies (force (and (logic.appealp x)
                        (@match (proof x (v A A)))))
            (equal (logic.appealp (build.contraction x))
                   t)))

 (defthm@ forcing-logic.proofp-of-build.contraction
   (implies (force (and ;(logic.appealp x)
                        (@match (proof x (v A A)))
                        (logic.proofp x axioms thms atbl)))
            (equal (logic.proofp (build.contraction x) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (e/d (definition-of-logic.proofp
                                    logic.appeal-step-okp
                                    logic.contraction-okp)
                                  (FORCING-TRUE-LISTP-OF-LOGIC.SUBPROOFS))))))



(defund@ build.expansion (a x)
  (declare (xargs :guard (and (logic.formulap a)
                              (logic.appealp x)
                              (@match (formula a A)
                                      (proof x B)))))
  (logic.appeal 'expansion
                (@formula (v A B))
                (list x)
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.expansion)))

 (defthm build.expansion-under-iff
   (iff (build.expansion a x)
        t))

 (defthm logic.method-of-build.expansion
   (equal (logic.method (build.expansion a x))
          'expansion))

 (defthm@ logic.conclusion-of-build.expansion
   (@extend ((formula a A)
             (proof x B))
            (equal (logic.conclusion (build.expansion a x))
                   (@formula (v A B)))))

 (defthm logic.subproofs-of-build.expansion
   (equal (logic.subproofs (build.expansion a x))
          (list x)))

 (defthm logic.extras-of-build.expansion
   (equal (logic.extras (build.expansion a x))
          nil))

 (defthm forcing-logic.appealp-of-build.expansion
   (implies (force (and (logic.formulap a)
                        (logic.appealp x)))
            (equal (logic.appealp (build.expansion a x))
                   t)))

 (defthm forcing-logic.proofp-of-build.expansion
   (implies (force (and (logic.formula-atblp a atbl)
                        ;(logic.appealp x)
                        (logic.proofp x axioms thms atbl)))
            (equal (logic.proofp (build.expansion a x) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (e/d (logic.appeal-step-okp
                                   logic.expansion-okp
                                   definition-of-logic.proofp)
                                  (forcing-logic.formula-atblp-rules
                                   FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VLHS
                                   FORCING-TRUE-LISTP-OF-LOGIC.SUBPROOFS))))))



(defund@ build.associativity (x)
  (declare (xargs :guard (and (logic.appealp x)
                              (@match (proof x (v A (v B C)))))))
  (logic.appeal 'associativity
                (@formula (v (v A B) C))
                (list x)
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.associativity)))

 (defthm build.associativity-under-iff
   (iff (build.associativity x)
        t))

 (defthm logic.method-of-build.associativity
   (equal (logic.method (build.associativity x))
          'associativity))

 (defthm@ logic.conclusion-of-build.associativity
   (@extend ((proof x (v A (v B C))))
            (equal (logic.conclusion (build.associativity x))
                   (@formula (v (v A B) C)))))

 (defthm logic.subproofs-of-build.associativity
   (equal (logic.subproofs (build.associativity x))
          (list x)))

 (defthm logic.extras-of-build.associativity
   (equal (logic.extras (build.associativity x))
          nil))

 (defthm@ forcing-logic.appealp-of-build.associativity
   (implies (force (and (logic.appealp x)
                        (@match (proof x (v A (v B C))))))
            (equal (logic.appealp (build.associativity x))
                   t)))

 (defthm@ forcing-logic.proofp-of-build.associativity
   (implies (force (and ;(logic.appealp x)
                        (@match (proof x (v A (v B C))))
                        (logic.proofp x axioms thms atbl)))
            (equal (logic.proofp (build.associativity x) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (e/d (definition-of-logic.proofp
                                    logic.appeal-step-okp
                                    logic.associativity-okp)
                                  (forcing-true-listp-of-logic.subproofs))))))



(defund build.instantiation (x sigma)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.sigmap sigma))))
  (let* ((conclusion (logic.conclusion x))
         (instance   (logic.substitute-formula conclusion sigma)))
    (if (equal conclusion instance)
        (logic.appeal-identity x)
      (logic.appeal 'instantiation instance (list x) sigma))))

(encapsulate
 ()
 (local (in-theory (enable build.instantiation)))

 (defthm build.instantiation-under-iff
   (iff (build.instantiation x sigma)
        t))

 (defthm logic.method-of-build.instantiation
   (equal (logic.method (build.instantiation x sigma))
          (if (equal (logic.conclusion x)
                     (logic.substitute-formula (logic.conclusion x) sigma))
              (logic.method x)
            'instantiation)))

 (defthm logic.conclusion-of-build.instantiation
   (equal (logic.conclusion (build.instantiation x sigma))
          (logic.substitute-formula (logic.conclusion x) sigma)))

 (defthm logic.subproofs-of-build.instantiation
   (equal (logic.subproofs (build.instantiation x sigma))
          (if (equal (logic.conclusion x)
                     (logic.substitute-formula (logic.conclusion x) sigma))
              (logic.subproofs x)
            (list x))))

 (defthm logic.extras-of-build.instantiation
   (equal (logic.extras (build.instantiation x sigma))
          (if (equal (logic.conclusion x)
                     (logic.substitute-formula (logic.conclusion x) sigma))
              (logic.extras x)
            sigma)))

 (defthm forcing-logic.appealp-of-build.instantiation
   (implies (force (and (logic.appealp x)
                        (logic.sigmap sigma)))
            (equal (logic.appealp (build.instantiation x sigma))
                   t)))

 (defthm forcing-logic.proofp-of-build.instantiation
   (implies (force (and ;(logic.appealp x)
                        (logic.sigmap sigma)
                        (logic.sigma-atblp sigma atbl)
                        (logic.proofp x axioms thms atbl)))
            (equal (logic.proofp (build.instantiation x sigma) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (e/d (definition-of-logic.proofp
                                    logic.appeal-step-okp
                                    logic.instantiation-okp)
                                  (FORCING-TRUE-LISTP-OF-LOGIC.SUBPROOFS))))))



(defund build.functional-equality (fn ti si)
  (declare (xargs :guard (and (logic.function-namep fn)
                              (logic.term-listp ti)
                              (logic.term-listp si)
                              (equal (len si) (len ti)))))
  (logic.appeal 'functional-equality
                (logic.functional-axiom fn ti si)
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.functional-equality)))

 (defthm build.functional-equality-under-iff
   (iff (build.functional-equality fn ti si)
        t))

 (defthm logic.method-of-build.functional-equality
   (equal (logic.method (build.functional-equality fn ti si))
          'functional-equality))

 (defthm logic.conclusion-of-build.functional-equality
   (equal (logic.conclusion (build.functional-equality fn ti si))
          (logic.functional-axiom fn ti si)))

 (defthm logic.subproofs-of-build.functional-equality
   (equal (logic.subproofs (build.functional-equality fn ti si))
          nil))

 (defthm logic.extras-of-build.functional-equality
   (equal (logic.extras (build.functional-equality fn ti si))
          nil))

 (defthm forcing-logic.appealp-of-build.functional-equality
   (implies (force (and (logic.function-namep fn)
                        (logic.term-listp ti)
                        (logic.term-listp si)
                        (equal (len ti) (len si))))
            (equal (logic.appealp (build.functional-equality fn ti si))
                   t)))

 (defthm forcing-logic.proofp-of-build.functional-equality
   (implies (force (and (logic.function-namep fn)
                        (logic.term-list-atblp ti atbl)
                        (logic.term-list-atblp si atbl)
                        (equal (len ti) (len si))
                        (equal (cdr (lookup fn atbl)) (len ti))))
            (equal (logic.proofp (build.functional-equality fn ti si) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.functional-equality-okp)))))



(defund build.beta-reduction (formals body actuals)
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (equal (len formals) (len actuals))
                              (true-listp actuals)
                              (logic.term-listp actuals))))
  (logic.appeal 'beta-reduction
                (logic.pequal (logic.lambda formals body actuals)
                              (logic.substitute body (pair-lists formals actuals)))
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.beta-reduction)))

 (defthm build.beta-reduction-under-iff
   (iff (build.beta-reduction formals body actuals)
        t))

 (defthm logic.method-of-build.beta-reduction
   (equal (logic.method (build.beta-reduction formals body actuals))
          'beta-reduction))

 (defthm logic.conclusion-of-build.beta-reduction
   (equal (logic.conclusion (build.beta-reduction formals body actuals))
          (logic.pequal (logic.lambda formals body actuals)
                        (logic.substitute body (pair-lists formals actuals)))))

 (defthm logic.subproofs-of-build.beta-reduction
   (equal (logic.subproofs (build.beta-reduction formals body actuals))
          nil))

 (defthm logic.extras-of-build.beta-reduction
   (equal (logic.extras (build.beta-reduction formals body actuals))
          nil))

 (defthm forcing-logic.appealp-of-build.beta-reduction
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (equal (len formals) (len actuals))
                        (true-listp actuals)
                        (logic.term-listp actuals)))
            (equal (logic.appealp (build.beta-reduction formals body actuals))
                   t)))

 (defthm forcing-logic.proofp-of-build.beta-reduction
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (equal (len formals) (len actuals))
                        (true-listp actuals)
                        (logic.term-listp actuals)
                        (logic.term-atblp body atbl)
                        (logic.term-list-atblp actuals atbl)))
            (equal (logic.proofp (build.beta-reduction formals body actuals) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.beta-reduction-okp)))))



(defund build.base-eval (a)
  (declare (xargs :guard (and (logic.termp a)
                              (logic.base-evaluablep a))))
  (logic.appeal 'base-eval
                (logic.pequal a (logic.base-evaluator a))
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable build.base-eval)))

 (defthm build.base-eval-under-iff
   (iff (build.base-eval a)
        t))

 (defthm logic.method-of-build.base-eval
   (equal (logic.method (build.base-eval a))
          'base-eval))

 (defthm logic.conclusion-of-build.base-eval
   (equal (logic.conclusion (build.base-eval a))
          (logic.pequal a (logic.base-evaluator a))))

 (defthm logic.subproofs-of-build.base-eval
   (equal (logic.subproofs (build.base-eval a))
          nil))

 (defthm logic.extras-of-build.base-eval
   (equal (logic.extras (build.base-eval a))
          nil))

 (defthm forcing-logic.appealp-of-build.base-eval
   (implies (force (and (logic.termp a)
                        (logic.base-evaluablep a)))
            (equal (logic.appealp (build.base-eval a))
                   t)))

 (defthm forcing-logic.proofp-of-build.base-eval
   (implies (force (and ;(logic.termp a)
                        (logic.base-evaluablep a)
                        (logic.term-atblp a atbl)))
            (equal (logic.proofp (build.base-eval a) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.base-eval-okp)))))




(defund build.instantiation-list (x sigma)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.sigmap sigma))))
  (if (consp x)
      (cons (build.instantiation (car x) sigma)
            (build.instantiation-list (cdr x) sigma))
    nil))

(defobligations build.instantiation-list
  (build.instantiation))

(encapsulate
 ()
 (defthm build.instantiation-list-when-not-consp
   (implies (not (consp x))
            (equal (build.instantiation-list x sigma)
                   nil))
   :hints(("Goal" :in-theory (enable build.instantiation-list))))

 (defthm build.instantiation-list-of-cons
   (equal (build.instantiation-list (cons a x) sigma)
          (cons (build.instantiation a sigma)
                (build.instantiation-list x sigma)))
   :hints(("Goal" :in-theory (enable build.instantiation-list))))

 (defthm forcing-logic.appeal-listp-of-build.instantiation-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.sigmap sigma)))
            (equal (logic.appeal-listp (build.instantiation-list x sigma))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-logic.strip-conclusions-of-build.instantiation-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.sigmap sigma)))
            (equal (logic.strip-conclusions (build.instantiation-list x sigma))
                   (logic.substitute-formula-list (logic.strip-conclusions x) sigma)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-logic.proofp-of-build.instantiation-list
   (implies (force (and ;(logic.appeal-listp x)
                        (logic.sigmap sigma)
                        ;; ---
                        (logic.sigma-atblp sigma atbl)
                        (logic.proof-listp x axioms thms atbl)))
            (equal (logic.proof-listp (build.instantiation-list x sigma) axioms thms atbl)
                   t))
   :hints(("Goal" :induct (cdr-induction x)))))





(defund build.induction (f m qs all-sigmas proofs)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.termp m)
                              (logic.formula-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas))
                              (logic.appeal-listp proofs)
                              (memberp (logic.make-basis-step f qs) (logic.strip-conclusions proofs))
                              (subsetp (logic.make-induction-steps f qs all-sigmas) (logic.strip-conclusions proofs))
                              (memberp (logic.make-ordinal-step m) (logic.strip-conclusions proofs))
                              (subsetp (logic.make-all-measure-steps m qs all-sigmas) (logic.strip-conclusions proofs)))))
  (logic.appeal 'induction
                f
                (list-fix proofs)
                (list m qs all-sigmas)))

(encapsulate
 ()
 (local (in-theory (enable build.induction)))

 (defthm build.induction-under-iff
   (iff (build.induction f m qs sigmas proofs)
        t))

 (defthm logic.method-of-build.induction
   (equal (logic.method (build.induction f m qs sigmas proofs))
          'induction))

 (defthm logic.conclusion-of-build.induction
   (equal (logic.conclusion (build.induction f m qs sigmas proofs))
          f))

 (defthm logic.subproofs-of-build.induction
   (equal (logic.subproofs (build.induction f m qs sigmas proofs))
          (list-fix proofs)))

 (defthm logic.extras-of-build.induction
   (equal (logic.extras (build.induction f m qs sigmas proofs))
          (list m qs sigmas)))

 (defthm forcing-logic.appealp-of-build.induction
   (implies (force (and (logic.formulap f)
                        (logic.appeal-listp proofs)))
            (equal (logic.appealp (build.induction f m qs sigmas proofs))
                   t)))

 (defthm forcing-logic.proofp-of-build.induction
   (implies (force (and (logic.formulap f)
                        (logic.termp m)
                        (logic.formula-listp qs)
                        (logic.sigma-list-listp all-sigmas)
                        (equal (len qs) (len all-sigmas))
                        (logic.appeal-listp proofs)
                        (memberp (logic.make-basis-step f qs) (logic.strip-conclusions proofs))
                        (subsetp (logic.make-induction-steps f qs all-sigmas) (logic.strip-conclusions proofs))
                        (memberp (logic.make-ordinal-step m) (logic.strip-conclusions proofs))
                        (subsetp (logic.make-all-measure-steps m qs all-sigmas) (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.formula-atblp f atbl)
                        (logic.proof-listp proofs axioms thms atbl)))
            (equal (logic.proofp (build.induction f m qs all-sigmas proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp
                                     logic.appeal-step-okp
                                     logic.induction-okp)))))




(dd.close)
