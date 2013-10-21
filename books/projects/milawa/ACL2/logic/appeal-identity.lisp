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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund logic.appeal-identity (x)
  (declare (xargs :guard (logic.appealp x)))
  (if (consp x)
      x
    (cons nil nil)))

(defthm logic.appeal-identity-under-iff
  (iff (logic.appeal-identity x)
       t)
  :hints(("Goal" :in-theory (enable logic.appeal-identity))))

(defthm logic.method-of-logic.appeal-identity
  (equal (logic.method (logic.appeal-identity x))
         (logic.method x))
  :hints(("Goal" :in-theory (enable logic.method logic.appeal-identity))))

(defthm logic.conclusion-of-logic.appeal-identity
  (equal (logic.conclusion (logic.appeal-identity x))
         (logic.conclusion x))
  :hints(("Goal" :in-theory (enable logic.conclusion logic.appeal-identity))))

(defthm logic.subproofs-of-logic.appeal-identity
  (equal (logic.subproofs (logic.appeal-identity x))
         (logic.subproofs x))
  :hints(("Goal" :in-theory (enable logic.subproofs logic.appeal-identity))))

(defthm logic.extras-of-logic.appeal-identity
  (equal (logic.extras (logic.appeal-identity x))
         (logic.extras x))
  :hints(("Goal" :in-theory (enable logic.extras logic.appeal-identity))))

(local (in-theory (disable forcing-true-listp-of-logic.subproofs)))

(defthm logic.skip-okp-of-logic.appeal-identity
  (equal (logic.skip-okp (logic.appeal-identity x) atbl)
         (logic.skip-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.skip-okp))))

(defthm logic.axiom-okp-of-logic.appeal-identity
  (equal (logic.axiom-okp (logic.appeal-identity x) axioms atbl)
         (logic.axiom-okp x axioms atbl))
  :hints(("Goal" :in-theory (enable logic.axiom-okp))))

(defthm logic.theorem-okp-of-logic.appeal-identity
  (equal (logic.theorem-okp (logic.appeal-identity x) theorems atbl)
         (logic.theorem-okp x theorems atbl))
  :hints(("Goal" :in-theory (enable logic.theorem-okp))))

(defthm logic.propositional-schema-okp-of-logic.appeal-identity
  (equal (logic.propositional-schema-okp (logic.appeal-identity x) atbl)
         (logic.propositional-schema-okp x atbl))
  :hints(("Goal" :in-theory (e/d (logic.propositional-schema-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm logic.functional-equality-okp-of-logic.appeal-identity
  (equal (logic.functional-equality-okp (logic.appeal-identity x) atbl)
         (logic.functional-equality-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.functional-equality-okp))))

(defthm logic.expansion-okp-of-logic.appeal-identity
  (equal (logic.expansion-okp (logic.appeal-identity x) atbl)
         (logic.expansion-okp x atbl))
  :hints(("Goal" :in-theory (e/d (logic.expansion-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm logic.contraction-okp-of-logic.appeal-identity
  (equal (logic.contraction-okp (logic.appeal-identity x))
         (logic.contraction-okp x))
  :hints(("Goal" :in-theory (enable logic.contraction-okp))))

(defthm logic.associativity-okp-of-logic.appeal-identity
  (equal (logic.associativity-okp (logic.appeal-identity x))
         (logic.associativity-okp x))
  :hints(("Goal" :in-theory (enable logic.associativity-okp))))

(defthm logic.cut-okp-of-logic.appeal-identity
  (equal (logic.cut-okp (logic.appeal-identity x))
         (logic.cut-okp x))
  :hints(("Goal" :in-theory (enable logic.cut-okp))))

(defthm logic.instantiation-okp-of-logic.appeal-identity
  (equal (logic.instantiation-okp (logic.appeal-identity x) atbl)
         (logic.instantiation-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.instantiation-okp))))

(defthm logic.beta-reduction-okp-of-logic.appeal-identity
  (equal (logic.beta-reduction-okp (logic.appeal-identity x) atbl)
         (logic.beta-reduction-okp x atbl))
  :hints(("Goal" :in-theory (enable logic.beta-reduction-okp))))

(defthm logic.induction-okp-of-logic.appeal-identity
  (equal (logic.induction-okp (logic.appeal-identity x))
         (logic.induction-okp x))
  :hints(("Goal" :in-theory (enable logic.induction-okp))))

(defthm logic.base-eval-okp-of-logic.appeal-identity
  (equal (logic.base-eval-okp (logic.appeal-identity x) atbl)
         (logic.base-eval-okp x atbl))
  :hints(("Goal" :in-theory (e/d (logic.base-eval-okp)
                                 ((:executable-counterpart acl2::force))))))

(defthm logic.appeal-step-okp-of-logic.appeal-identity
  (equal (logic.appeal-step-okp (logic.appeal-identity x) axioms thms atbl)
         (logic.appeal-step-okp x axioms thms atbl))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appealp-of-logic.appeal-identity
  (equal (logic.appealp (logic.appeal-identity x))
         (logic.appealp x))
  :hints(("Goal" :in-theory (enable logic.appeal-identity
                                    definition-of-logic.appealp))))

(defthm logic.proofp-of-logic.appeal-identity
  (equal (logic.proofp (logic.appeal-identity x) axioms thms atbl)
         (logic.proofp x axioms thms atbl))
  :hints(("Goal" :use ((:instance definition-of-logic.proofp (x (logic.appeal-identity x)))
                       (:instance definition-of-logic.proofp)))))

