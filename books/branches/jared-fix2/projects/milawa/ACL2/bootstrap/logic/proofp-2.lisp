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
(include-book "proofp-2-strip-conclusions")
(include-book "proofp-2-induction")
(%interactive)



(%autoadmit logic.axiom-okp)

(%autoprove booleanp-of-logic.axiom-okp
            (%enable default logic.axiom-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.axiom-okp
            (%enable default logic.axiom-okp))


(%autoadmit logic.theorem-okp)

(%autoprove booleanp-of-logic.theorem-okp
            (%enable default logic.theorem-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.theorem-okp
            (%enable default logic.theorem-okp))


(%autoadmit logic.propositional-schema-okp)

(%autoprove booleanp-of-logic.propositional-schema-okp
            (%enable default logic.propositional-schema-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.propositional-schema-okp
            (%enable default
                     logic.propositional-schema-okp
                     backtracking-logic.formula-atblp-rules)
            (%disable default
                      forcing-logic.formula-atblp-rules))




(%autoadmit logic.check-functional-axiom)

(%autoprove booleanp-of-logic.check-functional-axiom
            (%induct (rank x)
                     ((equal (logic.fmtype x) 'pequal*)
                      nil)
                     ((equal (logic.fmtype x) 'por*)
                      (((x  (logic.vrhs x))
                        (ti (cons (logic.=lhs (logic.~arg (logic.vlhs x))) ti))
                        (si (cons (logic.=rhs (logic.~arg (logic.vlhs x))) si)))))
                     ((and (not (equal (logic.fmtype x) 'pequal*))
                           (not (equal (logic.fmtype x) 'por*)))
                      nil))
            (%restrict default logic.check-functional-axiom (equal x 'x)))

(%autoadmit logic.functional-equality-okp)

(%autoprove booleanp-of-logic.functional-equality-okp
            (%enable default logic.functional-equality-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.functional-equality-okp
            (%enable default logic.functional-equality-okp))



(%autoadmit logic.expansion-okp)

(%autoprove booleanp-of-logic.expansion-okp
            (%enable default logic.expansion-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.expansion-okp
            (%enable default
                     logic.expansion-okp
                     backtracking-logic.formula-atblp-rules
                     logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
            (%disable default
                      forcing-logic.formula-atblp-rules
                      forcing-true-listp-of-logic.subproofs))



(%autoadmit logic.contraction-okp)

(%autoprove booleanp-of-logic.contraction-okp
            (%enable default logic.contraction-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.contraction-okp
            (%enable default
                     logic.contraction-okp
                     backtracking-logic.formula-atblp-rules
                     logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
            (%disable default
                      forcing-logic.formula-atblp-rules
                      forcing-true-listp-of-logic.subproofs))


(%autoadmit logic.associativity-okp)

(%autoprove booleanp-of-logic.associativity-okp
            (%enable default logic.associativity-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.associativity-okp
            (%enable default
                     logic.associativity-okp
                     backtracking-logic.formula-atblp-rules
                     logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
            (%disable default
                      forcing-logic.formula-atblp-rules
                      forcing-true-listp-of-logic.subproofs))



(%autoadmit logic.cut-okp)

(%autoprove booleanp-of-logic.cut-okp
            (%enable default logic.cut-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.cut-okp
            (%enable default
                     logic.cut-okp
                     backtracking-logic.formula-atblp-rules
                     logic.formula-list-atblp-of-logic.strip-conclusions-when-len-2)
            (%disable default
                      forcing-logic.formula-atblp-rules
                      forcing-true-listp-of-logic.subproofs))



(%autoadmit logic.instantiation-okp)

(%autoprove booleanp-of-logic.instantiation-okp
            (%enable default logic.instantiation-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.instantiation-okp
            (%enable default
                     logic.instantiation-okp
                     backtracking-logic.formula-atblp-rules
                     logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
            (%disable default
                      forcing-logic.formula-atblp-rules
                      forcing-true-listp-of-logic.subproofs))


(%autoadmit logic.beta-reduction-okp)

(%autoprove booleanp-of-logic.beta-reduction-okp
            (%enable default logic.beta-reduction-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.beta-reduction-okp
            (%enable default logic.beta-reduction-okp))



(%autoadmit logic.base-eval-okp)

(%autoprove booleanp-of-logic.base-eval-okp
            (%enable default logic.base-eval-okp))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.base-eval-okp
            (%enable default
                     logic.base-eval-okp
                     backtracking-logic.formula-atblp-rules)
            (%disable default
                      forcing-logic.formula-atblp-rules
                      forcing-true-listp-of-logic.subproofs))





(%autoadmit logic.induction-okp)

(%autoprove booleanp-of-logic.induction-okp
            (%enable default logic.induction-okp))

(%autoprove lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.induction-okp
            (%enable default logic.make-basis-step))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.induction-okp
            (%enable default
                     logic.induction-okp
                     lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.induction-okp)
            (%disable default
                      logic.formula-atblp-when-memberp-of-logic.formula-list-atblp
                      logic.formula-atblp-when-memberp-of-logic.formula-list-atblp-alt)
            (%auto)
            (%use (%instance (%thm logic.formula-atblp-when-memberp-of-logic.formula-list-atblp)
                             (a (logic.make-basis-step (logic.conclusion x) (second (logic.extras x))))
                             (x (logic.strip-conclusions (logic.subproofs x))))))


(%autoadmit logic.appeal-step-okp)

;; (defsection logic.appeal-step-okp
;;   ;; Bleh skip okp thing.  We need autoadmit to respect :export.
;;   (%defun logic.appeal-step-okp (x axioms thms atbl)
;;           (LET ((HOW (LOGIC.METHOD X)))
;;                (COND ((EQUAL HOW 'AXIOM)
;;                       (LOGIC.AXIOM-OKP X AXIOMS ATBL))
;;                      ((EQUAL HOW 'THEOREM)
;;                       (LOGIC.THEOREM-OKP X THMS ATBL))
;;                      ((EQUAL HOW 'PROPOSITIONAL-SCHEMA)
;;                       (LOGIC.PROPOSITIONAL-SCHEMA-OKP X ATBL))
;;                      ((EQUAL HOW 'FUNCTIONAL-EQUALITY)
;;                       (LOGIC.FUNCTIONAL-EQUALITY-OKP X ATBL))
;;                      ((EQUAL HOW 'BETA-REDUCTION)
;;                       (LOGIC.BETA-REDUCTION-OKP X ATBL))
;;                      ((EQUAL HOW 'EXPANSION)
;;                       (LOGIC.EXPANSION-OKP X ATBL))
;;                      ((EQUAL HOW 'CONTRACTION)
;;                       (LOGIC.CONTRACTION-OKP X))
;;                      ((EQUAL HOW 'ASSOCIATIVITY)
;;                       (LOGIC.ASSOCIATIVITY-OKP X))
;;                      ((EQUAL HOW 'CUT) (LOGIC.CUT-OKP X))
;;                      ((EQUAL HOW 'INSTANTIATION)
;;                       (LOGIC.INSTANTIATION-OKP X ATBL))
;;                      ((EQUAL HOW 'INDUCTION)
;;                       (LOGIC.INDUCTION-OKP X))
;;                      ((EQUAL HOW 'BASE-EVAL)
;;                       (LOGIC.BASE-EVAL-OKP X ATBL))
;;                      ;((EQUAL HOW 'SKIP)
;;                      ; (LOGIC.SKIP-OKP X ATBL))
;;                      (T NIL))))
;;   (%admit))

(%autoprove booleanp-of-logic.appeal-step-okp
            (%enable default logic.appeal-step-okp))

(%autoprove logic.appeal-step-okp-when-not-consp
            (%enable default logic.appeal-step-okp logic.method))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.appeal-step-okp
            (%enable default logic.appeal-step-okp))


(encapsulate
 ()
 ;; BOZO add hints facility to %autoadmit
 (local (%disable default forcing-true-listp-of-logic.subproofs))
 (%autoadmit logic.flag-proofp))

(%autoadmit logic.proofp)
(%autoadmit logic.proof-listp)

(%autoprove definition-of-logic.proofp
            (%enable default logic.proofp logic.proof-listp)
            (%restrict default logic.flag-proofp (equal x 'x)))

(%autoprove definition-of-logic.proof-listp
            (%enable default logic.proofp logic.proof-listp)
            (%restrict default logic.flag-proofp (equal x 'x)))

(%autoprove logic.proofp-when-not-consp
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove logic.proof-listp-when-not-consp
            (%restrict default definition-of-logic.proof-listp (equal x 'x)))

(%autoprove logic.proof-listp-of-cons
            (%restrict default definition-of-logic.proof-listp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-logic.proofp
            (%logic.appeal-induction flag x)
            (%disable default forcing-true-listp-of-logic.subproofs)
            (%restrict default definition-of-logic.proofp (equal x 'x)))

(%autoprove booleanp-of-logic.proofp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.proofp) (flag 'proof))))

(%autoprove booleanp-of-logic.proof-listp
            (%use (%instance (%thm lemma-for-booleanp-of-logic.proofp) (flag 'list))))



(%deflist logic.proof-listp (x axioms thms atbl)
          (logic.proofp x axioms thms atbl))

(%autoprove logic.proofp-of-nth-when-logic.proof-listp
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

(%autoprove forcing-logic.proof-listp-of-firstn)

(%autoprove forcing-logic.proof-listp-of-restn)



(%autoprove lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.proofp
            (%logic.appeal-induction flag x)
            (%restrict default definition-of-logic.proofp (equal x 'x))
            (%disable default forcing-true-listp-of-logic.subproofs))

(%autoprove logic.formula-atblp-of-logic.conclusion-when-logic.proofp
            (%use (%instance (%thm lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.proofp)
                             (flag 'proof))))

(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-when-logic.proof-listp
            (%use (%instance (%thm lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.proofp)
                             (flag 'list))))

(%autoprove logic.proof-listp-of-logic.subproofs-when-logic.proofp
            (%restrict default definition-of-logic.proofp (equal x 'x)))


