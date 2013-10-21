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
(include-book "substitute-term")
(%interactive)


(%autoadmit logic.flag-groundp)
(%autoadmit logic.groundp)
(%autoadmit logic.ground-listp)

(%autoprove definition-of-logic.groundp
            (%restrict default logic.flag-groundp (equal x 'x))
            (%enable default logic.groundp)
            (%enable default logic.ground-listp))

(%autoprove definition-of-logic.ground-listp
            (%restrict default logic.flag-groundp (equal x 'x))
            (%enable default logic.groundp)
            (%enable default logic.ground-listp))


(%autoprove logic.ground-listp-when-not-consp
            (%restrict default definition-of-logic.ground-listp (equal x 'x)))

(%autoprove logic.ground-listp-of-cons
            (%restrict default definition-of-logic.ground-listp (equal x '(cons a x))))

(%autoprove booleanp-of-logic.ground-listp
            (%cdr-induction x))

(%autoprove booleanp-of-logic.groundp
            (%restrict default definition-of-logic.groundp (equal x 'x)))

(%autoprove logic.groundp-when-logic.constantp
            (%restrict default definition-of-logic.groundp (equal x 'x)))

(%autoprove forcing-logic.ground-listp-of-logic.function-args-when-logic.groundp
            (%restrict default definition-of-logic.groundp (equal x 'x)))

(%autoprove forcing-logic.ground-listp-of-logic.lambda-actuals-when-logic.groundp
            (%restrict default definition-of-logic.groundp (equal x 'x)))



(%deflist logic.ground-listp (x)
          (logic.groundp x))

(%autoprove logic.ground-listp-when-logic.constant-listp
            (%cdr-induction x))

(%autoprove forcing-logic.groundp-of-logic.function
            (%restrict default definition-of-logic.groundp (equal x '(logic.function name args))))

(%autoprove forcing-logic.groundp-of-logic.lambda
            (%restrict default definition-of-logic.groundp (equal x '(logic.lambda formals body actuals))))



(%autoprove lemma-2-for-forcing-logic.groundp-of-logic.substitute
            (%cdr-induction sigma))

(%autoprove lemma-for-forcing-logic.groundp-of-logic.substitute
            (%logic.term-induction flag x)
            (%enable default lemma-2-for-forcing-logic.groundp-of-logic.substitute))

(%autoprove forcing-logic.groundp-of-logic.substitute
            (%use (%instance (%thm lemma-for-forcing-logic.groundp-of-logic.substitute) (flag 'term))))

(%autoprove forcing-logic.ground-listp-of-logic.substitute-list
            (%use (%instance (%thm lemma-for-forcing-logic.groundp-of-logic.substitute) (flag 'list))))

(%autoprove forcing-logic.groundp-when-logic.constant-listp-of-logic.function-args
            (%use (%instance (%thm forcing-logic.groundp-of-logic.function)
                             (name (logic.function-name term))
                             (args (logic.function-args term)))))


(%autoprove forcing-logic.groundp-when-logic.constant-listp-of-logic.lambda-actuals
            (%use (%instance (%thm forcing-logic.groundp-of-logic.lambda)
                             (formals (logic.lambda-formals term))
                             (body    (logic.lambda-body term))
                             (actuals (logic.lambda-actuals term)))))

(%ensure-exactly-these-rules-are-missing "../../logic/groundp")
