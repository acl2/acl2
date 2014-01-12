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
(%interactive)

(defsection build.axiom
  (%autoadmit build.axiom)
  (local (%enable default build.axiom))
  (%autoprove build.axiom-under-iff)
  (%autoprove logic.method-of-build.axiom)
  (%autoprove logic.conclusion-of-build.axiom)
  (%autoprove logic.subproofs-of-build.axiom)
  (%autoprove logic.extras-of-build.axiom)
  (%autoprove forcing-logic.appealp-of-build.axiom)
  (local (%disable default build.axiom))
  (%autoprove forcing-logic.proofp-of-build.axiom
              (%enable default logic.axiom-okp logic.appeal-step-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.axiom a)))))

(defsection build.theorem
  (%autoadmit build.theorem)
  (local (%enable default build.theorem))
  (%autoprove build.theorem-under-iff)
  (%autoprove logic.method-of-build.theorem)
  (%autoprove logic.conclusion-of-build.theorem)
  (%autoprove logic.subproofs-of-build.theorem)
  (%autoprove logic.extras-of-build.theorem)
  (%autoprove forcing-logic.appealp-of-build.theorem)
  (local (%disable default build.theorem))
  (%autoprove forcing-logic.proofp-of-build.theorem
              (%enable default logic.theorem-okp logic.appeal-step-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.theorem a)))))

(defsection build.propositional-schema
  (%autoadmit build.propositional-schema)
  (local (%enable default build.propositional-schema))
  (%autoprove build.propositional-schema-under-iff)
  (%autoprove logic.method-of-build.propositional-schema)
  (%autoprove logic.conclusion-of-build.propositional-schema)
  (%autoprove logic.subproofs-of-build.propositional-schema)
  (%autoprove logic.extras-of-build.propositional-schema)
  (%autoprove forcing-logic.appealp-of-build.propositional-schema)
  (local (%disable default build.propositional-schema))
  (%autoprove forcing-logic.proofp-of-build.propositional-schema
              (%enable default logic.appeal-step-okp logic.propositional-schema-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.propositional-schema a)))))

(defsection build.cut
  (%autoadmit build.cut)
  (local (%enable default build.cut))
  (%autoprove build.cut-under-iff)
  (%autoprove logic.method-of-build.cut)
  (%autoprove logic.conclusion-of-cut) ;; BOZO wrong name, should be build.cut
  (%autoprove logic.subproofs-of-build.cut)
  (%autoprove logic.extras-of-build.cut)
  (%autoprove forcing-logic.appealp-of-build.cut)
  (local (%disable default build.cut))
  (%autoprove forcing-logic.proofp-of-build.cut
              (%enable default logic.appeal-step-okp logic.cut-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.cut x y)))))

(defsection build.contraction
  (%autoadmit build.contraction)
  (local (%enable default build.contraction))
  (%autoprove build.contraction-under-iff)
  (%autoprove logic.method-of-build.contraction)
  (%autoprove logic.conclusion-of-build.contraction)
  (%autoprove logic.subproofs-of-build.contraction)
  (%autoprove logic.extras-of-build.contraction)
  (%autoprove forcing-logic.appealp-of-build.contraction)
  (local (%disable default build.contraction))
  (%autoprove forcing-logic.proofp-of-build.contraction
              (%enable default logic.appeal-step-okp logic.contraction-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.contraction x)))))

(defsection build.expansion
  (%autoadmit build.expansion)
  (local (%enable default build.expansion))
  (%autoprove build.expansion-under-iff)
  (%autoprove logic.method-of-build.expansion)
  (%autoprove logic.conclusion-of-build.expansion)
  (%autoprove logic.subproofs-of-build.expansion)
  (%autoprove logic.extras-of-build.expansion)
  (%autoprove forcing-logic.appealp-of-build.expansion)
  (local (%disable default build.expansion))
  (%autoprove forcing-logic.proofp-of-build.expansion
              (%enable default logic.appeal-step-okp logic.expansion-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.expansion a x)))))

(defsection build.associativity
  (%autoadmit build.associativity)
  (local (%enable default build.associativity))
  (%autoprove build.associativity-under-iff)
  (%autoprove logic.method-of-build.associativity)
  (%autoprove logic.conclusion-of-build.associativity)
  (%autoprove logic.subproofs-of-build.associativity)
  (%autoprove logic.extras-of-build.associativity)
  (%autoprove forcing-logic.appealp-of-build.associativity)
  (local (%disable default build.associativity))
  (%autoprove forcing-logic.proofp-of-build.associativity
              (%enable default logic.appeal-step-okp logic.associativity-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.associativity x)))))

(defsection build.instantiation
  (%autoadmit build.instantiation)
  (local (%enable default build.instantiation))
  (%autoprove build.instantiation-under-iff)
  (%autoprove logic.method-of-build.instantiation)
  (%autoprove logic.conclusion-of-build.instantiation)
  (%autoprove logic.subproofs-of-build.instantiation)
  (%autoprove logic.extras-of-build.instantiation)
  (%autoprove forcing-logic.appealp-of-build.instantiation)
  (%autoprove forcing-logic.proofp-of-build.instantiation
              (%enable default logic.appeal-step-okp logic.instantiation-okp)
              (%restrict default definition-of-logic.proofp (equal x '(logic.appeal 'instantiation (logic.substitute-formula (logic.conclusion x) sigma) (cons x 'nil) sigma)))))

(defsection build.functional-equality
  (%autoadmit build.functional-equality)
  (local (%enable default build.functional-equality))
  (%autoprove build.functional-equality-under-iff)
  (%autoprove logic.method-of-build.functional-equality)
  (%autoprove logic.conclusion-of-build.functional-equality)
  (%autoprove logic.subproofs-of-build.functional-equality)
  (%autoprove logic.extras-of-build.functional-equality)
  (%autoprove forcing-logic.appealp-of-build.functional-equality)
  (local (%disable default build.functional-equality))
  (%autoprove forcing-logic.proofp-of-build.functional-equality
              (%enable default logic.appeal-step-okp logic.functional-equality-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.functional-equality fn ti si)))))

(defsection build.beta-reduction
  (%autoadmit build.beta-reduction)
  (local (%enable default build.beta-reduction))
  (%autoprove build.beta-reduction-under-iff)
  (%autoprove logic.method-of-build.beta-reduction)
  (%autoprove logic.conclusion-of-build.beta-reduction)
  (%autoprove logic.subproofs-of-build.beta-reduction)
  (%autoprove logic.extras-of-build.beta-reduction)
  (%autoprove forcing-logic.appealp-of-build.beta-reduction)
  (local (%disable default build.beta-reduction))
  (%autoprove forcing-logic.proofp-of-build.beta-reduction
              (%enable default logic.appeal-step-okp logic.beta-reduction-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.beta-reduction formals body actuals)))))

(defsection build.base-eval
  (%autoadmit build.base-eval)
  (local (%enable default build.base-eval))
  (%autoprove build.base-eval-under-iff)
  (%autoprove logic.method-of-build.base-eval)
  (%autoprove logic.conclusion-of-build.base-eval)
  (%autoprove logic.subproofs-of-build.base-eval)
  (%autoprove logic.extras-of-build.base-eval)
  (%autoprove forcing-logic.appealp-of-build.base-eval)
  (local (%disable default build.base-eval))
  (%autoprove forcing-logic.proofp-of-build.base-eval
              (%enable default logic.appeal-step-okp logic.base-eval-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.base-eval a)))))

(defsection build.instantiation-list
  (%autoadmit build.instantiation-list)
  (%autoprove build.instantiation-list-when-not-consp (%restrict default build.instantiation-list (equal x 'x)))
  (%autoprove build.instantiation-list-of-cons (%restrict default build.instantiation-list (equal x '(cons a x))))
  (%autoprove forcing-logic.appeal-listp-of-build.instantiation-list (%cdr-induction x))
  (%autoprove forcing-logic.strip-conclusions-of-build.instantiation-list (%cdr-induction x))
  ;; BOZO next theorem is misnamed, should be proof-listp
  (%autoprove forcing-logic.proofp-of-build.instantiation-list (%cdr-induction x)))

(defsection build.induction
  (%autoadmit build.induction)
  (local (%enable default build.induction))
  (%autoprove build.induction-under-iff)
  (%autoprove logic.method-of-build.induction)
  (%autoprove logic.conclusion-of-build.induction)
  (%autoprove logic.subproofs-of-build.induction)
  (%autoprove logic.extras-of-build.induction)
  (%autoprove forcing-logic.appealp-of-build.induction)
  (local (%disable default build.induction))
  (%autoprove forcing-logic.proofp-of-build.induction
              (%enable default logic.appeal-step-okp logic.induction-okp)
              (%restrict default definition-of-logic.proofp (equal x '(build.induction f m qs all-sigmas proofs)))))
