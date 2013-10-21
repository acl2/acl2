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


(%autoadmit rewrite.syntaxp-arity-table)

(%autoprove logic.arity-tablep-of-rewrite.syntaxp-arity-table)
(%noexec rewrite.syntaxp-arity-table)


(%autoadmit rewrite.syntaxp-base-evaluablep)

(%autoprove booleanp-of-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep)
            (%forcingp nil))

(%autoprove forcing-logic.functionp-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep))

(%autoprove logic.constant-listp-of-logic.function-args-when-rewrite.syntaxp-base-evaluablep
            (%enable default
                     rewrite.syntaxp-base-evaluablep
                     logic.function-args))

(%autoprove lookup-logic.function-name-in-rewrite.syntaxp-arity-table-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep))

(%autoprove lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-arity-table))

(%autoprove logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
            (%enable default rewrite.syntaxp-base-evaluablep)
            ;; now looping with new reweriter changes??
            (%disable default len-when-tuplep)
            (%use (%instance (%thm lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep)
                             (fn (logic.function-name term))
                             (args (logic.function-args term)))))

(%autoprove rewrite.syntaxp-base-evaluablep-when-preliminary-fn-applied-to-constants
            (%enable default
                     rewrite.syntaxp-base-evaluablep
                     rewrite.syntaxp-arity-table))

(%autoprove rewrite.syntaxp-base-evaluablep-of-logic.function-equal
            (%enable default
                     rewrite.syntaxp-base-evaluablep
                     rewrite.syntaxp-arity-table))



(%autoadmit rewrite.syntaxp-base-evaluator)

(%autoprove forcing-logic.constantp-of-rewrite.syntaxp-base-evaluator
            (%enable default
                     rewrite.syntaxp-base-evaluator))

(%autoprove forcing-logic.constantp-of-rewrite.syntaxp-base-evaluator-free)

(%autoprove rewrite.syntaxp-base-evaluator-of-logic.function-equal
            (%enable default rewrite.syntaxp-base-evaluator))



(%autoadmit rewrite.flag-syntaxp-evaluator)

(%autoadmit rewrite.syntaxp-evaluator)
(%autoadmit rewrite.syntaxp-evaluator-list)

(%autoprove definition-of-rewrite.syntaxp-evaluator
            (%enable default rewrite.syntaxp-evaluator rewrite.syntaxp-evaluator-list)
            (%restrict default rewrite.flag-syntaxp-evaluator (equal x 'x)))

(%autoprove definition-of-rewrite.syntaxp-evaluator-list
            (%enable default rewrite.syntaxp-evaluator rewrite.syntaxp-evaluator-list)
            (%restrict default rewrite.flag-syntaxp-evaluator (equal x 'x)))

(%autoprove rewrite.flag-syntaxp-evaluator-when-term
            (%enable default rewrite.syntaxp-evaluator))

(%autoprove rewrite.flag-syntaxp-evaluator-when-list
            (%enable default rewrite.syntaxp-evaluator-list))

(%autoprove rewrite.syntaxp-evaluator-list-when-not-consp
            (%restrict default definition-of-rewrite.syntaxp-evaluator-list (equal x 'x)))

(%autoprove rewrite.syntaxp-evaluator-list-of-cons
            (%restrict default definition-of-rewrite.syntaxp-evaluator-list (equal x '(cons a x))))

(%autoprove true-listp-of-rewrite.syntaxp-evaluator-list
            (%cdr-induction x))

(%autoprove forcing-len-of-cdr-of-rewrite.syntaxp-evaluator-list
            (%cdr-induction x))

(%autoprove consp-of-rewrite.syntaxp-evaluator-list
            (%cdr-induction x))

(%autoprove lemma-for-forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator
            (%autoinduct rewrite.flag-syntaxp-evaluator flag x defs n)
            (%disable default
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      expensive-term/formula-inference)
            (%auto)
            (%restrict default definition-of-rewrite.syntaxp-evaluator (equal x 'x))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator
            (%use (%instance (%thm lemma-for-forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator)
                             (flag 'term))))

(%autoprove forcing-logic.constant-listp-of-cdr-of-rewrite.syntaxp-evaluator-list
            (%use (%instance (%thm lemma-for-forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator)
                             (flag 'list))))

