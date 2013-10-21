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
(include-book "evaluator-bldr")
(%interactive)

(local (%enable default lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr))

(encapsulate
 ()
 (local (%max-proof-size 600000000))
 (%autoprove lemma-for-forcing-logic.proofp-of-generic-evaluator-bldr
             (%flag-generic-evaluator-induction flag x defs n)
             (%disable default
                       formula-decomposition
                       expensive-term/formula-inference
                       expensive-arithmetic-rules
                       expensive-arithmetic-rules-two
                       expensive-subsetp-rules
                       type-set-like-rules
                       forcing-logic.function-of-logic.function-name-and-logic.function-args
                       forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                       forcing-lookup-of-logic.function-name
                       same-length-prefixes-equal-cheap
                       definitionp-when-memberp-of-definition-listp
                       definition-list-lookup-when-not-consp)
             (%auto :strategy (split urewrite))
             (%forcingp nil)
             (%crewrite default)
             (%restrict default definition-of-generic-evaluator (equal x 'x))
             (%restrict default definition-of-generic-evaluator-bldr (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list-bldr (equal x 'x))
             (%auto :strategy (split urewrite))
             (%crewrite default)
             (%forcingp t)
             (%enable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules
                      forcing-lookup-of-logic.function-name)
             (%disable default
                       logic.termp-when-logic.formulap
                       logic.termp-when-invalid-maybe-expensive
                       logic.formulap-when-logic.termp
                       logic.formula-listp-when-definition-listp
                       consp-when-logic.lambdap-cheap
                       consp-when-logic.functionp-cheap
                       consp-of-car-when-none-consp
                       consp-of-car-when-cons-listp
                       logic.substitute-when-malformed-cheap
                       logic.lambdap-when-not-anything-else-maybe-expensive)
             (%cheapen default
                       logic.substitute-when-logic.constantp
                       logic.substitute-when-logic.variablep
                       logic.constantp-when-logic.variablep
                       logic.variablep-when-logic.constantp
                       logic.constantp-when-logic.functionp)
             (%auto :strategy (split cleanup urewrite crewrite elim))))

(%autoprove forcing-logic.proofp-of-generic-evaluator-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-generic-evaluator-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.proof-listp-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-generic-evaluator-bldr)
                             (flag 'list))))
