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
(%interactive)


(%autoadmit logic.lambdap)
(%autoadmit logic.lambda)
(%autoadmit logic.lambda-formals)
(%autoadmit logic.lambda-body)
(%autoadmit logic.lambda-actuals)


(%autoprove booleanp-of-logic.lambdap
            (%enable default logic.lambdap))

(%autoprove consp-when-logic.lambdap-cheap
            (%enable default logic.lambdap))

(%autoprove logic.variablep-when-logic.lambdap-cheap
            (%enable default logic.lambdap logic.variablep))

(%autoprove logic.constantp-when-logic.lambdap-cheap
            (%enable default logic.lambdap logic.constantp))

(%noexec logic.lambda)

(%autoprove consp-of-logic.lambda
            (%enable default logic.lambda))

(%autoprove logic.lambda-under-iff
            (%enable default logic.lambda))

(%autoprove logic.constantp-of-logic.lambda
            (%enable default logic.lambda logic.constantp))

(%autoprove logic.variablep-of-logic.lambda
            (%enable default logic.lambda logic.variablep))

(%autoprove forcing-logic.termp-of-logic.lambda
            (%enable default logic.lambda)
            (%restrict default definition-of-logic.termp (equal x '(cons (cons 'lambda (cons formals (cons body 'nil))) actuals)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambdap-of-logic.lambda
            (%enable default logic.lambdap logic.lambda))

(%autoprove equal-of-logic.lambda-and-logic.lambda
            (%enable default logic.lambda))

(%autoprove forcing-true-listp-of-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.variable-listp-of-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-uniquep-of-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambda-formals-of-logic.lambda
            (%enable default logic.lambda-formals logic.lambda))





(%autoprove forcing-logic.termp-of-logic.lambda-body
            (%enable default logic.lambdap logic.lambda-body)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambda-body-of-logic.lambda
            (%enable default logic.lambda-body logic.lambda))

(%autoprove rank-of-logic.lambda-body
            (%enable default logic.lambda-body))

(%autoprove forcing-subsetp-of-logic.term-vars-of-logic.lambda-body-with-logic.lambda-formals
            (%enable default logic.lambdap logic.lambda-body logic.lambda-formals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-true-listp-of-logic.lambda-actuals
            (%enable default logic.lambdap logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.term-listp-of-logic.lambda-actuals
            (%enable default logic.lambdap logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.lambda-actuals-of-logic.lambda
            (%enable default logic.lambda-actuals logic.lambda))






(%autoprove forcing-equal-lens-of-logic.lambda-formals-and-logic.lambda-actuals
            (%enable default logic.lambdap logic.lambda-formals logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.lambda-of-logic.lambda-formals-body-and-actuals
            (%enable default logic.lambdap logic.lambda logic.lambda-formals logic.lambda-body logic.lambda-actuals)
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%restrict default tuplep (or (equal n ''3) (equal n ''2) (equal n ''1) (equal n ''0)))
            (%betamode nil)
            (%auto :strategy (cleanup split crewrite))
            (%betamode once)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-logic.lambda-of-logic.lambda-formals-body-and-actuals-free)

(%autoprove rank-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove rank-of-first-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove rank-of-second-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove rank-of-third-of-logic.lambda-actuals
            (%enable default logic.lambda-actuals))

(%autoprove logic.lambdap-when-consp-of-car-cheap
            (%enable default logic.lambdap))

