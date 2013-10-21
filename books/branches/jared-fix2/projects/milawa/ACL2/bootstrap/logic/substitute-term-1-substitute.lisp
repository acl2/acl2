;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

(%autoadmit logic.flag-substitute)
(%autoadmit logic.substitute)
(%autoadmit logic.substitute-list)


(%autoprove definition-of-logic.substitute
            (%enable default logic.substitute logic.substitute-list)
            (%restrict default logic.flag-substitute (equal x 'x)))

(%autoprove definition-of-logic.substitute-list
            (%enable default logic.substitute logic.substitute-list)
            (%restrict default logic.flag-substitute (equal x 'x)))

(%autoprove logic.flag-substitute-of-term
            (%enable default logic.substitute))

(%autoprove logic.flag-substitute-of-term-list
            (%enable default logic.substitute-list))

(%autoprove logic.substitute-when-malformed-cheap
            ;; BOZO this rule says it's cheap, but it doesn't have any backchain limits here or
            ;; in the ACL2 model!
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-list-when-not-consp
            (%restrict default definition-of-logic.substitute-list (equal x 'x)))

(%autoprove logic.substitute-list-of-cons
            (%restrict default definition-of-logic.substitute-list (equal x '(cons a x))))

(%defprojection :list (logic.substitute-list x sigma)
                :element (logic.substitute x sigma)
                :nil-preservingp t)



(%autoprove logic.substitute-when-logic.constantp
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-when-logic.variablep
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-when-logic.functionp-cheap
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove logic.substitute-when-logic.lambdap-cheap
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.substitute-of-logic.function)

(%autoprove forcing-logic.function-name-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.function-args-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.substitute-of-logic.lambda
            ;; BOZO this should not be named `forcing` since there are no hyps
            (%disable default forcing-logic.termp-of-logic.lambda)
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.lambda-formals-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.lambda-body-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

(%autoprove forcing-logic.lambda-actuals-of-logic.substitute
            (%restrict default definition-of-logic.substitute (equal x 'x)))

