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
(include-book "primary-eqtrace")
(include-book "secondary-eqtrace")
(include-book "transitivity-eqtraces")
(include-book "weakening-eqtrace")
(include-book "direct-iff-eqtrace")
(include-book "negative-iff-eqtrace")
(%interactive)



(%autoadmit rw.eqtrace-step-okp)
(%autoprove booleanp-of-rw.eqtrace-step-okp
            (%enable default rw.eqtrace-step-okp))


(%autoadmit rw.flag-eqtrace-okp)
(%autoadmit rw.eqtrace-okp)
(%autoadmit rw.eqtrace-list-okp)

(%autoprove definition-of-rw.eqtrace-okp
            (%restrict default rw.flag-eqtrace-okp (equal x 'x))
            (%enable default rw.eqtrace-okp rw.eqtrace-list-okp))

(%autoprove definition-of-rw.eqtrace-list-okp
            (%restrict default rw.flag-eqtrace-okp (equal x 'x))
            (%enable default rw.eqtrace-okp rw.eqtrace-list-okp))

(%autoprove rw.flag-eqtrace-okp-of-trace
            (%enable default rw.eqtrace-okp))

(%autoprove rw.flag-eqtrace-okp-of-list
            (%enable default rw.eqtrace-list-okp))



(%autoprove lemma-for-booleanp-of-rw.eqtrace-okp
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-okp (equal x 'x))
            (%restrict default definition-of-rw.eqtrace-list-okp (equal x 'x)))

(%autoprove booleanp-of-rw.eqtrace-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtrace-okp)
                             (flag 'trace))))

(%autoprove booleanp-of-rw.eqtrace-list-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtrace-okp)
                             (flag 'list))))

(%autoprove rw.eqtrace-list-okp-when-not-consp
            (%restrict default definition-of-rw.eqtrace-list-okp (equal x 'x)))

(%autoprove rw.eqtrace-list-okp-of-cons
            (%restrict default definition-of-rw.eqtrace-list-okp (equal x '(cons a x))))

(%autoprove rw.eqtrace-step-okp-of-nil
            (%enable default rw.eqtrace-step-okp))

(%autoprove rw.eqtrace-okp-of-nil
            (%restrict default definition-of-rw.eqtrace-okp (equal x ''nil)))

(%deflist rw.eqtrace-list-okp (x box)
          (rw.eqtrace-okp x box))


(%autoprove forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces
            (%restrict default definition-of-rw.eqtrace-okp (equal x 'x)))

(%autoprove rw.primary-eqtrace-okp-when-empty-box
            (%enable default rw.primary-eqtrace-okp))

(%autoprove rw.secondary-eqtrace-okp-when-empty-box
            (%enable default rw.secondary-eqtrace-okp))


(%autoprove lemma-for-rw.eqtrace-okp-when-empty-box
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-okp (equal x 'x))
            (%auto)
            (%forcingp nil)
            (%enable default
                     rw.eqtrace-step-okp
                     rw.trans1-eqtrace-okp
                     rw.trans2-eqtrace-okp
                     rw.trans3-eqtrace-okp
                     rw.weakening-eqtrace-okp
                     rw.direct-iff-eqtrace-okp
                     rw.negative-iff-eqtrace-okp))

(%autoprove rw.eqtrace-okp-when-empty-box
            (%use (%instance (%thm lemma-for-rw.eqtrace-okp-when-empty-box)
                             (flag 'trace))))

(%autoprove rw.eqtrace-list-okp-when-empty-box
            (%use (%instance (%thm lemma-for-rw.eqtrace-okp-when-empty-box)
                             (flag 'list))))


(encapsulate
 ()
 (local (%enable default rw.eqtrace-step-okp))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.primary-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.primary-eqtrace okp nhyp)
                                     (rw.primary-eqtrace 't nhyp)))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.secondary-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.secondary-eqtrace okp nhyp)
                                     (rw.secondary-eqtrace 't nhyp)))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.trans1-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.trans1-eqtrace iffp x y))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.trans2-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.trans2-eqtrace iffp x y))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.trans3-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.trans3-eqtrace iffp x y))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.weakening-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp (equal x '(rw.weakening-eqtrace x))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.direct-iff-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.direct-iff-eqtrace okp nhyp)
                                     (rw.direct-iff-eqtrace 't nhyp)))))

 (%autoprove forcing-rw.eqtrace-okp-of-rw.negative-iff-eqtrace
             (%restrict default definition-of-rw.eqtrace-okp
                        (memberp x '((rw.negative-iff-eqtrace okp nhyp)
                                     (rw.negative-iff-eqtrace 't nhyp))))))



(%autoadmit rw.eqtrace-formula)


(%autoprove forcing-logic.formulap-of-rw.eqtrace-formula
            (%enable default rw.eqtrace-formula))

(%autoprove forcing-logic.formula-atblp-of-rw.eqtrace-formula
            (%enable default rw.eqtrace-formula))

(%defprojection :list (rw.eqtrace-formula-list x box)
                :element (rw.eqtrace-formula x box))

(%autoprove forcing-logic.formula-listp-of-rw.eqtrace-formula-list
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-rw.eqtrace-formula
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/eqtrace-okp")

