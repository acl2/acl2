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


(%autoadmit definitionp)

(%autoprove booleanp-of-definitionp
            (%enable default definitionp))

(%autoprove logic.formulap-when-definitionp
            (%enable default definitionp))

(%autoprove logic.fmtype-when-definitionp
            (%enable default definitionp))

(%autoprove logic.functionp-of-logic.=lhs-when-definitionp
            (%enable default definitionp))

(%autoprove logic.variable-listp-of-logic.function-args-of-logic.=lhs-when-definitionp
            (%enable default definitionp))

(%autoprove uniquep-of-logic.function-args-of-logic.=lhs-when-definitionp
            (%enable default definitionp))

(%autoprove subsetp-of-logic.term-vars-of-logic.=rhs-when-definitionp
            (%enable default definitionp))



(%deflist definition-listp (x)
          (definitionp x))

(%autoprove logic.formula-listp-when-definition-listp
            (%cdr-induction x))



(%autoadmit definition-list-lookup)

(%autoprove definition-list-lookup-when-not-consp
            (%restrict default definition-list-lookup (equal x 'x)))

(%autoprove definition-list-lookup-of-cons
            (%restrict default definition-list-lookup (equal x '(cons a x))))

(%autoprove definitionp-of-definition-list-lookup
            (%cdr-induction x))

(%autoprove logic.formula-atblp-of-definition-list-lookup
            (%cdr-induction x))

(%autoprove memberp-of-definition-list-lookup
            (%cdr-induction defs))

(%autoprove forcing-logic.fmtype-of-definition-list-lookup)

(%autoprove forcing-logic.function-name-of-logic.=lhs-of-definition-list-lookup
            (%cdr-induction defs))

(%autoprove forcing-logic.functionp-of-logic.=lhs-of-definition-list-lookup
            (%cdr-induction defs))

(%ensure-exactly-these-rules-are-missing "../../rewrite/definitions")



(%enable expensive-term/formula-inference
         logic.formulap-when-definitionp
         logic.formula-listp-when-definition-listp
         logic.functionp-of-logic.=lhs-when-definitionp
         logic.fmtype-when-definitionp)
