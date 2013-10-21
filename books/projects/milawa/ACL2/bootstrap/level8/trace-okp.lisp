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
(include-book "basic-recognizers")
(include-book "urewrite-recognizers")
(include-book "crewrite-recognizers")
(%interactive)


(%autoadmit rw.trace-step-okp)

(%autoadmit rw.trace-step-env-okp)

(%autoprove booleanp-of-rw.trace-step-okp
            (%enable default rw.trace-step-okp))

(%autoprove booleanp-of-rw.trace-step-env-okp
            (%enable default rw.trace-step-env-okp))



(%autoadmit rw.flag-trace-okp)

(%autoadmit rw.trace-okp)

(%autoadmit rw.trace-list-okp)

(%autoprove definition-of-rw.trace-okp
            (%restrict default rw.flag-trace-okp (equal x 'x))
            (%enable default rw.trace-okp rw.trace-list-okp))

(%autoprove definition-of-rw.trace-list-okp
            (%restrict default rw.flag-trace-okp (equal x 'x))
            (%enable default rw.trace-okp rw.trace-list-okp))


(%autoprove rw.trace-step-okp-of-nil
            (%enable default rw.trace-step-okp))

(%autoprove rw.trace-okp-of-nil
            (%restrict default definition-of-rw.trace-okp (equal x ''nil)))

(%autoprove rw.trace-list-okp-when-not-consp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-list-okp (equal x 'x)))

(%autoprove rw.trace-list-okp-of-cons
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-list-okp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-rw.trace-okp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-okp (equal x 'x)))

(%autoprove booleanp-of-rw.trace-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-okp)
                             (flag 'term))))

(%autoprove booleanp-of-rw.trace-list-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-okp)
                             (flag 'list))))


(%deflist rw.trace-list-okp (x)
          (rw.trace-okp x))

(%autoprove rw.trace-step-okp-when-rw.trace-okp
            (%restrict default definition-of-rw.trace-okp (equal x 'x)))

(%autoprove rw.trace-list-okp-of-rw.trace->subtraces-when-rw.trace-okp
            (%restrict default definition-of-rw.trace-okp (equal x 'x)))





(%autoadmit rw.flag-trace-env-okp)

(%autoadmit rw.trace-env-okp)

(%autoadmit rw.trace-list-env-okp)

(%autoprove definition-of-rw.trace-env-okp
            (%restrict default rw.flag-trace-env-okp (equal x 'x))
            (%enable default rw.trace-env-okp rw.trace-list-env-okp))

(%autoprove definition-of-rw.trace-list-env-okp
            (%restrict default rw.flag-trace-env-okp (equal x 'x))
            (%enable default rw.trace-env-okp rw.trace-list-env-okp))

(%autoprove rw.trace-list-env-okp-when-not-consp
            (%restrict default definition-of-rw.trace-list-env-okp (equal x 'x)))

(%autoprove rw.trace-list-env-okp-of-cons
            (%restrict default definition-of-rw.trace-list-env-okp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-rw.trace-env-okp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-env-okp (equal x 'x)))

(%autoprove booleanp-of-rw.trace-env-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-env-okp)
                             (flag 'term))))

(%autoprove booleanp-of-rw.trace-list-env-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-env-okp)
                             (flag 'list))))

(%autoprove rw.trace-step-env-okp-of-nil
            (%enable default rw.trace-step-env-okp))

(%autoprove rw.trace-env-okp-of-nil
            (%restrict default definition-of-rw.trace-env-okp (equal x ''nil)))

(%deflist rw.trace-list-env-okp (x axioms thms atbl)
          (rw.trace-env-okp x axioms thms atbl))

(%autoprove rw.trace-step-env-okp-when-rw.trace-env-okp
            (%restrict default definition-of-rw.trace-env-okp (equal x 'x)))

(%autoprove rw.trace-list-env-okp-of-rw.trace->subtraces-when-rw.trace-env-okp
            (%restrict default definition-of-rw.trace-env-okp (equal x 'x)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/trace-okp")



