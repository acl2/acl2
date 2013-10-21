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
(include-book "../logic/proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; The deduction rule is unique (so far) in that it manipulates proofs which
;; already exist, rather than building atop of other proofs.  This is not
;; something that our usual theory is well set up to handle, so here we add
;; many rules to assist with reasoning about already existing proofs.
;;
;; These rules are not something we normally want around, so we exile them to
;; this file instead of integrating them into our system.  This file is then
;; locally included whenever we want these sorts of rules available.

(defthm logic.appeal-step-okp-when-axiom
  (implies (equal (logic.method x) 'axiom)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.axiom-okp x axioms atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-propositional-schema
  (implies (equal (logic.method x) 'propositional-schema)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.propositional-schema-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-functional-equality
  (implies (equal (logic.method x) 'functional-equality)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.functional-equality-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-expansion
  (implies (equal (logic.method x) 'expansion)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.expansion-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-contraction
  (implies (equal (logic.method x) 'contraction)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.contraction-okp x)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-associativity
  (implies (equal (logic.method x) 'associativity)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.associativity-okp x)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-cut
  (implies (equal (logic.method x) 'cut)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.cut-okp x)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-instantiation
  (implies (equal (logic.method x) 'instantiation)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.instantiation-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-induction
  (implies (equal (logic.method x) 'induction)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.induction-okp x)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-base-eval
  (implies (equal (logic.method x) 'base-eval)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  (logic.base-eval-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-logic.proofp
  (implies (logic.proofp x axioms thms atbl)
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.proofp))))



(defthm cons-structure-of-logic.subproofs-when-logic.cut-okp
  (implies (logic.cut-okp x)
           (and (logic.subproofs x)
                (consp (logic.subproofs x))
                (cdr (logic.subproofs x))
                (consp (cdr (logic.subproofs x)))))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm cons-structure-of-logic.subproofs-when-logic.instantiation-okp
  (implies (logic.instantiation-okp x atbl)
           (and (logic.subproofs x)
                (consp (logic.subproofs x))))
  :hints(("Goal" :in-theory (e/d (logic.instantiation-okp)
                                 (forcing-logic.appeal-listp-of-logic.subproofs)))))

(defthm cons-structure-of-logic.subproofs-when-logic.expansion-okp
  (implies (logic.expansion-okp x atbl)
           (and (logic.subproofs x)
                (consp (logic.subproofs x))))
  :hints(("Goal" :in-theory (e/d (logic.expansion-okp)
                                 (forcing-logic.appeal-listp-of-logic.subproofs)))))

(defthm cons-structure-of-logic.subproofs-when-logic.contraction-okp
  (implies (logic.contraction-okp x)
           (and (logic.subproofs x)
                (consp (logic.subproofs x))))
  :hints(("Goal" :in-theory (enable logic.contraction-okp))))

(defthm cons-structure-of-logic.subproofs-when-associativity
  (implies (logic.associativity-okp x)
           (and (logic.subproofs x)
                (consp (logic.subproofs x))))
  :hints(("Goal" :in-theory (enable logic.associativity-okp))))



(defthm conclusion-when-logic.instantiation-okp
  (implies (logic.instantiation-okp x atbl)
           (equal (logic.conclusion x)
                  (logic.substitute-formula (logic.conclusion (car (logic.subproofs x)))
                                            (logic.extras x))))
  :hints(("Goal" :in-theory (e/d (logic.instantiation-okp)
                                 (forcing-true-listp-of-logic.subproofs
                                  forcing-logic.appeal-listp-of-logic.subproofs)))))

(defthm logic.sigmap-of-logic.extras-when-logic.instantiation-okp
  (implies (logic.instantiation-okp x atbl)
           (logic.sigmap (logic.extras x)))
  :hints(("Goal" :in-theory (enable logic.instantiation-okp))))

(defthm conclusion-when-logic.cut-okp
  (implies (and (logic.cut-okp x)
                (force (logic.appealp x)))
           (equal (logic.conclusion x)
                  (logic.por (logic.vrhs (logic.conclusion (first (logic.subproofs x))))
                             (logic.vrhs (logic.conclusion (second (logic.subproofs x)))))))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm logic.fmtype-of-logic.conclusion-of-first-subgoal-when-logic.cut-okp
  (implies (and (logic.cut-okp x)
                (force (logic.appealp x)))
           (equal (logic.fmtype (logic.conclusion (first (logic.subproofs x))))
                  'por*))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm logic.fmtype-of-logic.conclusion-of-second-subgoal-when-logic.cut-okp
  (implies (and (logic.cut-okp x)
                (force (logic.appealp x)))
           (equal (logic.fmtype (logic.conclusion (second (logic.subproofs x))))
                  'por*))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm logic.vlhs-of-logic.conclusion-of-second-subgoal-when-logic.cut-okp
  (implies (and (logic.cut-okp x)
                (force (logic.appealp x)))
           (equal (logic.vlhs (logic.conclusion (second (logic.subproofs x))))
                  (logic.pnot (logic.vlhs (logic.conclusion (first (logic.subproofs x)))))))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm conclusion-when-logic.associativity-okp
  (implies (and (logic.associativity-okp x)
                (force (logic.appealp x)))
           (equal (logic.conclusion x)
                  (logic.por (logic.por (logic.vlhs (logic.conclusion (first (logic.subproofs x))))
                                        (logic.vlhs (logic.vrhs (logic.conclusion (first (logic.subproofs x))))))
                             (logic.vrhs (logic.vrhs (logic.conclusion (first (logic.subproofs x))))))))
  :hints(("Goal" :in-theory (enable logic.associativity-okp))))

(defthm logic.fmtype-of-logic.conclusion-of-subgoal-when-logic.associativity-okp
  (implies (and (logic.associativity-okp x)
                (force (logic.appealp x)))
           (equal (logic.fmtype (logic.conclusion (first (logic.subproofs x))))
                  'por*))
  :hints(("Goal" :in-theory (enable logic.associativity-okp))))

(defthm logic.fmtype-of-logic.vrhs-of-logic.conclusion-of-subgoal-when-logic.associativity-okp
  (implies (and (logic.associativity-okp x)
                (force (logic.appealp x)))
           (equal (logic.fmtype (logic.vrhs (logic.conclusion (first (logic.subproofs x)))))
                  'por*))
  :hints(("Goal" :in-theory (enable logic.associativity-okp))))


(defthm conclusion-when-logic.contraction-okp
  (implies (and (logic.contraction-okp x)
                (force (logic.appealp x)))
           (equal (logic.conclusion x)
                  (logic.vlhs (logic.conclusion (first (logic.subproofs x))))))
  :hints(("Goal" :in-theory (enable logic.contraction-okp))))

(defthm logic.vrhs-of-logic.conclusion-of-first-subgoal-when-logic.contraction-okp
  (implies (and (logic.contraction-okp x)
                (force (logic.appealp x)))
           (equal (logic.vrhs (logic.conclusion (first (logic.subproofs x))))
                  (logic.vlhs (logic.conclusion (first (logic.subproofs x))))))
  :hints(("Goal" :in-theory (enable logic.contraction-okp))))

(defthm logic.fmtype-of-logic.conclusion-of-first-subgoal-when-logic.contraction-okp
  (implies (and (logic.contraction-okp x)
                (force (logic.appealp x)))
           (equal (logic.fmtype (logic.conclusion (first (logic.subproofs x))))
                  'por*))
  :hints(("Goal" :in-theory (enable logic.contraction-okp))))


(defthm logic.fmtype-of-logic.conclusion-when-logic.expansion-okp
  (implies (and (logic.expansion-okp x atbl)
                (force (logic.appealp x)))
           (equal (logic.fmtype (logic.conclusion x))
                  'por*))
  :hints(("Goal" :in-theory (enable logic.expansion-okp))))

(defthm logic.vrhs-of-logic.conclusion-when-logic.expansion-okp
  (implies (and (logic.expansion-okp x atbl)
                (force (logic.appealp x)))
           (equal (logic.vrhs (logic.conclusion x))
                  (logic.conclusion (first (logic.subproofs x)))))
  :hints(("Goal" :in-theory (enable logic.expansion-okp))))
