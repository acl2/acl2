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
(include-book "simple-termp")
(%interactive)


(%autoadmit clause.flag-factor)
(%disable default clause.flag-factor)


(%autoadmit clause.factor)
(%autoadmit clause.factor-list)

(%autoprove definition-of-clause.factor
            (%enable default clause.factor clause.factor-list)
            (%restrict default clause.flag-factor (equal x 'x)))

(%autoprove definition-of-clause.factor-list
            (%enable default clause.factor clause.factor-list)
            (%restrict default clause.flag-factor (equal x 'x)))

(%autoprove clause.flag-factor-of-term-removal
            (%enable default clause.factor))

(%autoprove clause.flag-factor-of-list-removal
            (%enable default clause.factor-list))

(%autoprove clause.factor-list-when-not-consp
            (%restrict default definition-of-clause.factor-list (equal x 'x)))

(%autoprove clause.factor-list-of-cons
            (%restrict default definition-of-clause.factor-list (equal x '(cons a x))))

(%defprojection :list (clause.factor-list x assignment)
                :element (clause.factor x assignment))

(%autoprove clause.factor-list-when-len-three)

(%autoprove clause.factor-when-logic.constantp
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-logic.variablep
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-non-if-logic.functionp
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-bad-args-logic.functionp
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-if-expression
            (%forcingp nil)
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-logic.lambdap
            (%restrict default definition-of-clause.factor (equal x 'x)))

(%autoprove clause.factor-when-degenerate
            (%restrict default definition-of-clause.factor (equal x 'x)))


(%autoprove lemma-for-forcing-logic.termp-of-clause.factor
            (%clause.simple-term-induction flag x)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      forcing-logic.functionp-when-logic.base-evaluablep
                      not-equal-when-less
                      trichotomy-of-<
                      logic.formulap-when-not-consp))

(%autoprove forcing-logic.termp-of-clause.factor
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-clause.factor)
                             (flag 'term))))

(%autoprove forcing-logic.term-listp-of-clause.factor-list
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-clause.factor)
                             (flag 'list))))


(%autoprove lemma-for-forcing-logic.term-atblp-of-clause.factor
            (%clause.simple-term-induction flag x)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      forcing-logic.functionp-when-logic.base-evaluablep
                      not-equal-when-less
                      trichotomy-of-<
                      logic.formulap-when-not-consp))

(%autoprove forcing-logic.term-atblp-of-clause.factor
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-clause.factor)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-clause.factor-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-clause.factor)
                             (flag 'list))))


(%autoprove lemma-for-clause.factor-when-not-consp-of-assignment
            (%clause.simple-term-induction flag x)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      forcing-logic.functionp-when-logic.base-evaluablep
                      not-equal-when-less
                      trichotomy-of-<
                      logic.formulap-when-not-consp))

(%autoprove clause.factor-when-not-consp-of-assignment
            (%use (%instance (%thm lemma-for-clause.factor-when-not-consp-of-assignment)
                             (flag 'term))))

(%autoprove clause.factor-list-when-not-consp-of-assignment
            (%use (%instance (%thm lemma-for-clause.factor-when-not-consp-of-assignment)
                             (flag 'list))))


(%defprojection :list (clause.multifactor term x)
                :element (clause.factor term x))

(%autoprove forcing-logic.term-listp-of-clause.multifactor
            (%cdr-induction assignments))


(%ensure-exactly-these-rules-are-missing "../../clauses/if-lifting/factor")