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
(include-book "terms-2")
(include-book "terms-3-functionp")
(include-book "terms-3-lambdap")
(include-book "terms-3-term-vars")
(include-book "terms-3-term-list-listp")
(include-book "terms-3-arity-tablep")
(%interactive)



(%autoprove logic.functionp-when-logic.lambdap-cheap
            (%enable default logic.lambdap logic.functionp))

(%autoprove logic.lambdap-when-logic.functionp-cheap)

(%autoprove logic.functionp-of-logic.lambda)

(%autoprove logic.function-namep-of-car-when-logic.termp-and-not-logic.variablep
            (%enable default logic.functionp logic.constantp)
            (%restrict default definition-of-logic.termp (equal x 'x)))

(%autoprove logic.lambdap-when-not-anything-else-maybe-expensive
            (%enable default logic.lambdap logic.functionp)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil))

(%autoprove logic.termp-when-invalid-maybe-expensive)

(%autoprove logic.functionp-when-not-other-stuff-cheap
            (%enable default logic.lambdap logic.functionp)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil))

(%autoprove logic.lambdap-when-not-other-stuff-cheap)



(%autoprove logic.term-vars-when-function-call
            (%enable default logic.function-args)
            (%restrict default definition-of-logic.term-vars (equal x 'x))
            (%betamode nil))

(%autoprove logic.term-vars-when-logic.lambda
            (%enable default logic.lambdap logic.lambda-actuals)
            (%restrict default definition-of-logic.term-vars (equal x 'x))
            (%betamode nil))


(%autoprove lemma-for-forcing-logic.variable-listp-of-logic.term-vars
            (%logic.term-induction flag x)
            ;; This rule is really expensive, taking 716 frames/try when it's enabled
            (local (%disable default logic.variable-listp-of-subsetp-when-logic.variable-listp))
            ;; These rules cause problems with forcing
            (local (%disable default
                             FORCING-TRUE-LISTP-OF-LOGIC.FUNCTION-ARGS
                             FORCING-LOGIC.TERMP-OF-LOGIC.LAMBDA-BODY
                             FORCING-TRUE-LISTP-OF-LOGIC.LAMBDA-ACTUALS))
            (%auto :strategy (cleanup split crewrite elim)))

(%autoprove forcing-logic.variable-listp-of-logic.term-vars
            (%use (%instance (%thm lemma-for-forcing-logic.variable-listp-of-logic.term-vars) (flag 'term))))

(%autoprove forcing-logic.variable-listp-of-logic.term-list-vars
            (%use (%instance (%thm lemma-for-forcing-logic.variable-listp-of-logic.term-vars) (flag 'list))))



(%autoprove logic.term-listp-when-subset-of-somep
            (%cdr-induction x))

(%autoprove logic.term-listp-when-subset-of-somep-alt)

(%autoprove logic.term-list-listp-when-all-superset-of-somep
            (%cdr-induction x))

(%autoprove logic.term-list-listp-when-all-superset-of-somep-alt)

(%autoprove forcing-logic.term-list-listp-of-remove-supersets1
            (%autoinduct remove-supersets1))

(%autoprove forcing-logic.term-list-listp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove forcing-logic.term-list-listp-of-remove-duplicates-list
            (%cdr-induction x))



(%autoadmit logic.term-list-list-vars)

(%autoprove definition-of-logic.term-list-list-vars
            (%enable default logic.term-list-list-vars)
            (%restrict default logic.fast-term-list-list-vars (equal x 'x)))

(%autoprove logic.term-list-list-vars-when-not-consp
            (%restrict default definition-of-logic.term-list-list-vars (equal x 'x)))

(%autoprove logic.term-list-list-vars-of-cons
            (%restrict default definition-of-logic.term-list-list-vars (equal x '(cons a x))))

(%autoprove true-listp-of-logic.term-list-list-vars
            (%cdr-induction x))

(%autoprove forcing-logic.variable-listp-of-logic.term-list-list-vars
            (%cdr-induction x))
