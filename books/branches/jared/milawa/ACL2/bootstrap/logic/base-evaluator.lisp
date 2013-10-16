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
(include-book "terms")
(%interactive)


(%autoadmit logic.initial-arity-table)

(%autoprove logic.arity-tablep-of-logic.initial-arity-table)

(%noexec logic.initial-arity-table)




(%autoadmit logic.base-evaluablep)

(%autoprove booleanp-of-logic.base-evaluablep
            (%enable default logic.base-evaluablep)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-true-listp-of-logic.function-args))

(%autoprove forcing-logic.functionp-when-logic.base-evaluablep
            (%enable default logic.base-evaluablep))

(%autoprove logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
            (%enable default logic.base-evaluablep)
            (%disable default forcing-lookup-of-logic.function-name))

(%autoprove lookup-logic.function-name-in-logic.initial-arity-table-when-logic.base-evaluablep
            (%enable default logic.base-evaluablep)
            (%disable default forcing-lookup-of-logic.function-name))

(%autoprove lemma-for-logic.term-atblp-when-logic.base-evaluablep
            ;; BOZO we shouldn't need this use hint
            (%use (%instance (%thm forcing-logic.term-atblp-of-logic.function)
                             (name fn)
                             (args args)
                             (atbl (logic.initial-arity-table)))))

(%autoprove logic.term-atblp-when-logic.base-evaluablep
            (%autorule logic.term-atblp-when-logic.base-evaluablep)
            (%enable default logic.base-evaluablep)
            ;; BOZO we shouldn't need this use hint, we should just be able to enable the lemma.
            (%use (%instance (%thm lemma-for-logic.term-atblp-when-logic.base-evaluablep)
                             (fn (logic.function-name term))
                             (args (logic.function-args term))))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.base-evaluablep-when-preliminary-fn-applied-to-constants
            (%enable default logic.base-evaluablep)
            (%auto)
            (%use (%instance (%thm logic.function-namep-when-lookup-in-logic.arity-tablep)
                             (x (logic.initial-arity-table))
                             (a fn))))

(%autoprove logic.base-evaluablep-of-logic.function-equal
            (%enable default logic.base-evaluablep logic.initial-arity-table))



(%autoadmit logic.base-evaluator)

(%autoprove forcing-logic.constantp-of-logic.base-evaluator
            (%enable default logic.base-evaluator))

(%autoprove forcing-logic.constantp-of-logic.base-evaluator-free)

(%autoprove logic.base-evaluator-of-logic.function-equal
            (%enable default logic.base-evaluator))

(%ensure-exactly-these-rules-are-missing "../../logic/base-evaluator")

