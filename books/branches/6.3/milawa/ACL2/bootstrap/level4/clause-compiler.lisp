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
(include-book "formula-compiler")
(include-book "clause-basics")
(%interactive)


(%autoadmit clause.make-clause-from-arbitrary-formula)

(%autoprove consp-of-clause.make-clause-from-arbitrary-formula
            (%enable default clause.make-clause-from-arbitrary-formula))

(%autoprove forcing-logic.term-listp-of-clause.make-clause-from-arbitrary-formula
            (%enable default clause.make-clause-from-arbitrary-formula))

(%autoprove forcing-logic.term-list-atblp-of-clause.make-clause-from-arbitrary-formula
            (%enable default clause.make-clause-from-arbitrary-formula))

(%autoadmit clause.prove-arbitrary-formula-from-its-clause)

(encapsulate
 ()
 (local (%enable default
                clause.prove-arbitrary-formula-from-its-clause
                clause.make-clause-from-arbitrary-formula
                logic.term-formula))
 (%autoprove forcing-logic.appealp-of-clause.prove-arbitrary-formula-from-its-clause)
 (%autoprove forcing-logic.conclusion-of-clause.prove-arbitrary-formula-from-its-clause)
 (%autoprove forcing-logic.proofp-of-clause.prove-arbitrary-formula-from-its-clause))



(%defprojection :list (clause.make-clauses-from-arbitrary-formulas x)
                :element (clause.make-clause-from-arbitrary-formula x)
                :nil-preservingp nil)

(%autoprove consp-listp-of-clause.make-clauses-from-arbitrary-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-clause.make-clauses-from-arbitrary-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.make-clauses-from-arbitrary-formulas
            (%cdr-induction x))


(%autoadmit clause.prove-arbitrary-formulas-from-their-clauses)

(%autoprove forcing-logic.appeal-listp-of-clause.prove-arbitrary-formulas-from-their-clauses
            (%autoinduct clause.prove-arbitrary-formulas-from-their-clauses)
            (%restrict default clause.prove-arbitrary-formulas-from-their-clauses
                       (equal fs 'fs)))

(%autoprove forcing-logic.strip-conclusions-of-clause.prove-arbitrary-formulas-from-their-clauses
            (%autoinduct clause.prove-arbitrary-formulas-from-their-clauses)
            (%restrict default clause.prove-arbitrary-formulas-from-their-clauses
                       (equal fs 'fs)))

(%autoprove forcing-logic.proofp-of-clause.prove-arbitrary-formulas-from-their-clauses
            (%autoinduct clause.prove-arbitrary-formulas-from-their-clauses)
            (%restrict default clause.prove-arbitrary-formulas-from-their-clauses
                       (equal fs 'fs)))




(%autoadmit clause.prove-arbitrary-formula-from-its-clause-okp)

(%autoadmit clause.prove-arbitrary-formula-from-its-clause-high)
(%autoprove clause.prove-arbitrary-formula-from-its-clause-okp-of-clause.prove-arbitrary-formula-from-its-clause-high
            (%enable default clause.prove-arbitrary-formula-from-its-clause-okp
                     clause.prove-arbitrary-formula-from-its-clause-high))


(%autoprove hack-for-compile-formula-okp-1
            (%autoinduct logic.compile-formula f)
            (%restrict default logic.compile-formula (equal x 'f))

            (%disable default
                      FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VRHS
                      FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VLHS
                      FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.~ARG
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.=RHS
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.=LHS
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.FUNCTION
                      FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.COMPILE-FORMULA)

            (%restrict default logic.formula-atblp (equal x 'f))

            (%restrict default definition-of-logic.term-atblp
                       (or (equal x '(LOGIC.FUNCTION 'IF
                                                     (CONS (LOGIC.COMPILE-FORMULA (LOGIC.~ARG F))
                                                           '('NIL 'T))))
                           (equal x '(LOGIC.FUNCTION 'EQUAL
                                                     (CONS (LOGIC.=LHS F)
                                                           (CONS (LOGIC.=RHS F) 'nil))))
                           (equal x '(LOGIC.FUNCTION 'IF
                                                     (CONS (LOGIC.COMPILE-FORMULA (LOGIC.VLHS F))
                                                           (CONS ''T
                                                                 (CONS (LOGIC.COMPILE-FORMULA (LOGIC.VRHS F))
                                                                       'NIL)))))))

            (%forcingp nil))

(%autoprove hack-for-compile-formula-okp-2
            (%enable default
                     clause.make-clause-from-arbitrary-formula
                     clause.prove-arbitrary-formula-from-its-clause-okp
                     logic.term-formula)
            (%disable default
                      logic.formula-atblp-when-logic.provablep
                      logic.formula-list-atblp-of-when-logic.provable-listp)
            (%forcingp nil)
            (%use (%instance (%thm logic.formula-atblp-when-logic.provablep)
                             (x (logic.conclusion (car (logic.subproofs x))))))
            (%use (%instance (%thm hack-for-compile-formula-okp-1)
                             (f (logic.conclusion x))))
            (%auto)
            (%fertilize (logic.compile-formula (logic.conclusion x))
                        (logic.=lhs
                         (logic.~arg (logic.conclusion (car (logic.subproofs x)))))))

(encapsulate
 ()
 (local (%enable default clause.prove-arbitrary-formula-from-its-clause-okp))

 (%autoprove booleanp-of-clause.prove-arbitrary-formula-from-its-clause-okp)
 (%autoprove clause.prove-arbitrary-formula-from-its-clause-okp-of-logic.appeal-identity)

 (%autoprove lemma-1-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp)

 (%autoprove lemma-2-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
             (%enable default hack-for-compile-formula-okp-2))

 (%autoprove forcing-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
             (%enable default
                      lemma-1-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
                      lemma-2-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp)
             (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                              (x (clause.prove-arbitrary-formula-from-its-clause
                                  (logic.conclusion x)
                                  (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                          axioms thms atbl)))))))


(%ensure-exactly-these-rules-are-missing "../../clauses/compiler")