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
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(%autoadmit logic.arities-okp)

(%autoprove logic.arities-okp-when-not-consp
            (%restrict default logic.arities-okp (equal arities 'arities)))

(%autoprove logic.arities-okp-of-cons
            (%restrict default logic.arities-okp (equal arities '(cons a x))))

(%autoprove booleanp-of-logic.arities-okp
            (%cdr-induction arities))

(%autoprove logic.arities-okp-of-list-fix
            (%cdr-induction x))

(%autoprove logic.arities-okp-of-app
            (%cdr-induction x))

(%autoprove logic.arities-okp-of-rev
            (%cdr-induction x))

(%autoprove logic.arities-okp-of-cdr)

(%autoprove lemma-1-for-logic.arities-okp-when-subsetp
            (%cdr-induction x))

(%autoprove lemma-2-for-logic.arities-okp-when-subsetp
            (%cdr-induction x))

(%autoprove logic.arities-okp-when-subsetp-1
            (%cdr-induction x)
            (%enable default lemma-1-for-logic.arities-okp-when-subsetp
                             lemma-2-for-logic.arities-okp-when-subsetp))

(%autoprove logic.arities-okp-when-subsetp-2)




(%autoadmit logic.fast-arities-okp)


(%autoprove logic.arities-okp-of-halve-list
            (%disable default
                      halve-list-correct
                      [outside]halve-list-correct
                      logic.arities-okp-of-list-fix
                      [outside]logic.arities-okp-of-list-fix
                      logic.arities-okp-when-subsetp-1
                      logic.arities-okp-when-subsetp-2)

            (%use (%instance (%thm halve-list-correct)))
            (%use (%instance (%thm logic.arities-okp-of-list-fix)))
            (%auto)
            ;; Dammit Jared, this is gross.
            (%fertilize (list-fix x)
                        (APP (REV (CAR (HALVE-LIST X)))
                             (CDR (HALVE-LIST X))))
            (%auto)
            (%fertilize (list-fix x)
                        (APP (REV (CAR (HALVE-LIST X)))
                             (CDR (HALVE-LIST X))))
            (%auto)
            (%fertilize (list-fix x)
                        (APP (REV (CAR (HALVE-LIST X)))
                             (CDR (HALVE-LIST X))))
            (%auto))

(%autoprove logic.arities-okp-of-merge-lists
            (%autoinduct merge-lists)
            (%restrict default merge-lists (and (equal x 'x) (equal y 'y))))

(%autoprove logic.arities-okp-of-mergesort
            (%autoinduct mergesort))

(%autoprove logic.arities-okp-of-mergesort-map
            (%cdr-induction x))

(%autoprove mapp-of-cdr-when-mapp)

(%autoprove memberp-of-nil-when-mapp
            (%cdr-induction x))

(%autoprove lemma-1-for-logic.arities-okp-when-subsetp-of-unique-atbl
            (%cdr-induction x))

(%autoprove lemma-2-for-logic.arities-okp-when-subsetp-of-unique-atbl
            (%cdr-induction x))

(%autoprove lemma-3-for-logic.arities-okp-when-subsetp-of-unique-atbl
            (%cdr-induction x))

(%autoprove lemma-4-for-logic.arities-okp-when-subsetp-of-unique-atbl
            (%cdr-induction x))

(%autoprove logic.arities-okp-when-subsetp-of-unique-atbl
            (%cdr-induction x)
            (%enable default lemma-1-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             lemma-2-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             lemma-3-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             lemma-4-for-logic.arities-okp-when-subsetp-of-unique-atbl
                             ))

(%autoprove logic.fast-arities-okp-removal
            (%enable default logic.fast-arities-okp)
            (%use (%instance (%thm logic.arities-okp-when-subsetp-of-unique-atbl)
                             (atbl (mergesort-map atbl))
                             (x x))))


(%autoadmit logic.flag-slow-term-arities)
(%autoadmit logic.slow-term-arities)
(%autoadmit logic.slow-term-list-arities)

(%autoprove definition-of-logic.slow-term-arities
            (%enable default logic.slow-term-arities logic.slow-term-list-arities)
            (%restrict default logic.flag-slow-term-arities (equal x 'x)))

(%autoprove definition-of-logic.slow-term-list-arities
            (%enable default logic.slow-term-arities logic.slow-term-list-arities)
            (%restrict default logic.flag-slow-term-arities (equal x 'x)))

(%autoprove logic.flag-slow-term-arities-of-term
            (%enable default logic.slow-term-arities))

(%autoprove logic.flag-slow-term-arities-of-list
            (%enable default logic.slow-term-list-arities))

(%autoprove logic.slow-term-list-arities-when-not-consp
            (%restrict default definition-of-logic.slow-term-list-arities (equal x 'x)))

(%autoprove logic.slow-term-list-arities-of-cons
            (%restrict default definition-of-logic.slow-term-list-arities (equal x '(cons a x))))

(%autoadmit logic.flag-term-arities)
(%autoadmit logic.term-arities)
(%autoadmit logic.term-list-arities)

(%autoprove definition-of-logic.term-arities
            (%enable default logic.term-arities logic.term-list-arities)
            (%restrict default logic.flag-term-arities (equal x 'x)))

(%autoprove definition-of-logic.term-list-arities
            (%enable default logic.term-arities logic.term-list-arities)
            (%restrict default logic.flag-term-arities (equal x 'x)))

(%autoprove logic.flag-term-arities-of-term
            (%enable default logic.term-arities))

(%autoprove logic.flag-term-arities-of-list
            (%enable default logic.term-list-arities))

(%autoprove logic.term-list-arities-when-not-consp
            (%restrict default definition-of-logic.term-list-arities (equal x 'x)))

(%autoprove logic.term-list-arities-of-cons
            (%restrict default definition-of-logic.term-list-arities (equal x '(cons a x))))

(%autoprove lemma-for-true-listp-of-logic.slow-term-arities
            (%logic.term-induction flag x)
            (%restrict default definition-of-logic.slow-term-arities (equal x 'x)))

(%autoprove true-listp-of-logic.slow-term-arities
            (%use (%instance (%thm lemma-for-true-listp-of-logic.slow-term-arities)
                             (flag 'term))))

(%autoprove true-listp-of-logic.slow-term-list-arities
            (%use (%instance (%thm lemma-for-true-listp-of-logic.slow-term-arities)
                             (flag 'list))))

(%autoprove lemma-for-true-listp-of-logic.term-arities
            (%autoinduct logic.flag-term-arities flag x acc)
            (%forcingp nil)
            (%restrict default definition-of-logic.term-arities (equal x 'x)))

(%autoprove true-listp-of-logic.term-arities
            (%use (%instance (%thm lemma-for-true-listp-of-logic.term-arities)
                             (flag 'term))))

(%autoprove true-listp-of-logic.term-list-arities
            (%use (%instance (%thm lemma-for-true-listp-of-logic.term-arities)
                             (flag 'list))))

(%autoprove lemma-for-logic.term-arities-removal
            (%autoinduct logic.flag-term-arities flag x acc)
            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two)
            (%forcingp nil)
            (%waterfall default 40)
            (%restrict default definition-of-logic.term-arities (equal x 'x))
            (%restrict default definition-of-logic.slow-term-arities (equal x 'x))
            (%auto)
            (%fertilize (LOGIC.TERM-LIST-ARITIES (LOGIC.LAMBDA-ACTUALS X) ACC)
                        (APP (LOGIC.SLOW-TERM-LIST-ARITIES (LOGIC.LAMBDA-ACTUALS X)) ACC))
            (%auto)
            (%fertilize (LOGIC.TERM-LIST-ARITIES X2 ACC)
                        (APP (LOGIC.SLOW-TERM-LIST-ARITIES X2) ACC))
            (%auto))

(%autoprove logic.term-arities-removal
            (%use (%instance (%thm lemma-for-logic.term-arities-removal)
                             (flag 'term))))

(%autoprove logic.term-list-arities-removal
            (%use (%instance (%thm lemma-for-logic.term-arities-removal)
                             (flag 'list))))


(%autoprove lemma-2-for-logic.term-atblp-when-logic.arities-okp-of-logic.slow-term-arities)

(%autoprove lemma-for-logic.slow-term-arities-correct
            (%logic.term-induction flag x)
            (%enable default
                     lemma-2-for-logic.term-atblp-when-logic.arities-okp-of-logic.slow-term-arities)
            (%forcingp nil)
            (%waterfall default 40)
            (%restrict default definition-of-logic.slow-term-arities (equal x 'x))
            (%restrict default definition-of-logic.term-atblp (equal x 'x))
            (%waterfall default 40))

(%autoprove logic.slow-term-arities-correct
            (%use (%instance (%thm lemma-for-logic.slow-term-arities-correct)
                             (flag 'term))))

(%autoprove logic.slow-term-list-arities-correct
            (%use (%instance (%thm lemma-for-logic.slow-term-arities-correct)
                             (flag 'list))))


(%autoadmit logic.slow-formula-arities)
(%autoadmit logic.formula-arities)

(%autoprove true-listp-of-logic.formula-arities
            (%autoinduct logic.formula-arities)
            (%restrict default logic.formula-arities (equal x 'x)))

(%autoprove logic.formula-arities-removal
            (%autoinduct logic.formula-arities)
            (%restrict default logic.formula-arities (equal x 'x))
            (%restrict default logic.slow-formula-arities (equal x 'x)))

(%autoprove logic.slow-formula-arities-correct
            (%autoinduct logic.slow-formula-arities)
            (%forcingp nil)
            (%restrict default logic.slow-formula-arities (equal x 'x))
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoadmit logic.slow-formula-list-arities)
(%autoadmit logic.formula-list-arities)

(%autoprove true-listp-of-logic.formula-list-arities
            (%autoinduct logic.formula-list-arities)
            (%restrict default logic.formula-list-arities (equal x 'x)))

(%autoprove logic.formula-list-arities-removal
            (%autoinduct logic.formula-list-arities)
            (%restrict default logic.formula-list-arities (equal x 'x))
            (%restrict default logic.slow-formula-list-arities (equal x 'x)))

(%autoprove logic.slow-formula-list-arities-correct
            (%cdr-induction x)
            (%forcingp nil)
            (%restrict default logic.formula-list-atblp (equal x 'x))
            (%restrict default logic.slow-formula-list-arities (equal x 'x)))

(%ensure-exactly-these-rules-are-missing "../../logic/arities-okp")