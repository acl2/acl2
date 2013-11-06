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
(%interactive)


(%autoadmit logic.appeal-identity)

(%autoprove logic.appeal-identity-under-iff
            (%enable default logic.appeal-identity))

(%autoprove logic.method-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.method))

(%autoprove logic.conclusion-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.conclusion))

(%autoprove logic.subproofs-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.subproofs))

(%autoprove logic.extras-of-logic.appeal-identity
            (%enable default logic.appeal-identity logic.extras))

(local (%disable default forcing-true-listp-of-logic.subproofs))

(%autoprove logic.axiom-okp-of-logic.appeal-identity
            (%enable default logic.axiom-okp))

(%autoprove logic.theorem-okp-of-logic.appeal-identity
            (%enable default logic.theorem-okp))

(%autoprove logic.propositional-schema-okp-of-logic.appeal-identity
            (%enable default logic.propositional-schema-okp))

(%autoprove logic.functional-equality-okp-of-logic.appeal-identity
            (%enable default logic.functional-equality-okp))

(%autoprove logic.expansion-okp-of-logic.appeal-identity
            (%enable default logic.expansion-okp))

(%autoprove logic.contraction-okp-of-logic.appeal-identity
            (%enable default logic.contraction-okp))

(%autoprove logic.associativity-okp-of-logic.appeal-identity
            (%enable default logic.associativity-okp))

(%autoprove logic.cut-okp-of-logic.appeal-identity
            (%enable default logic.cut-okp))

(%autoprove logic.instantiation-okp-of-logic.appeal-identity
            (%enable default logic.instantiation-okp))

(%autoprove logic.beta-reduction-okp-of-logic.appeal-identity
            (%enable default logic.beta-reduction-okp))

(%autoprove logic.induction-okp-of-logic.appeal-identity
            (%enable default logic.induction-okp))

(%autoprove logic.base-eval-okp-of-logic.appeal-identity
            (%enable default logic.base-eval-okp))

(%autoprove logic.appeal-step-okp-of-logic.appeal-identity
            (%enable default logic.appeal-step-okp))

(%autoprove logic.appealp-of-logic.appeal-identity
            (%restrict default definition-of-logic.appealp (equal x 'x))
            (%enable default logic.appeal-identity))

(%autoprove logic.proofp-of-logic.appeal-identity
            (%restrict default definition-of-logic.proofp (or (equal x '(logic.appeal-identity x))
                                                              (equal x 'x))))

(%ensure-exactly-these-rules-are-missing "../../logic/appeal-identity"
                                         logic.skip-okp-of-logic.appeal-identity)


