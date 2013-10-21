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
(include-book "urewrite")
(include-book "fast-traces")
(%interactive)

(%autoadmit rw.fast-flag-urewrite)
(%autoadmit rw.fast-urewrite)
(%autoadmit rw.fast-urewrite-list)

(%autoprove definition-of-rw.fast-urewrite
            (%enable default rw.fast-urewrite rw.fast-urewrite-list)
            (%restrict default rw.fast-flag-urewrite (equal x 'x)))

(%autoprove definition-of-rw.fast-urewrite-list
            (%enable default rw.fast-urewrite rw.fast-urewrite-list)
            (%restrict default rw.fast-flag-urewrite (equal x 'x)))

(%autoprove rw.fast-flag-urewrite-of-term
            (%enable default rw.fast-urewrite))

(%autoprove rw.fast-flag-urewrite-of-list
            (%enable default rw.fast-urewrite-list))

(%autoprove rw.fast-urewrite-under-iff
            (%restrict default definition-of-rw.fast-urewrite (equal x 'x)))

(%autoprove len-of-rw.ftraces->rhses-of-rw.fast-urewrite-list
            (%cdr-induction x)
            (%restrict default definition-of-rw.fast-urewrite-list (equal x 'x)))




(%autoprove lemma-for-forcing-rw.ftracep-of-rw.fast-urewrite
            (%autoinduct rw.fast-flag-urewrite)
            (%splitlimit 10)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      expensive-term/formula-inference
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      formula-decomposition)
            (%auto)
            (%restrict default definition-of-rw.fast-urewrite (equal x 'x))
            (%restrict default definition-of-rw.fast-urewrite-list (memberp x '(x (cons x1 x2))))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.ftracep-of-rw.fast-urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.fast-urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.ftrace-listp-of-rw.fast-urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.ftracep-of-rw.fast-urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace-fast-image-of-rw.urewrite
            (%autoinduct rw.fast-flag-urewrite)
            (%splitlimit 10)
            (%enable default rw.trace-fast-image-equivalence-lemmas)
            (%disable default
                      forcing-lookup-of-logic.function-name
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      expensive-term/formula-inference
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      formula-decomposition)
            (%auto)
            (%restrict default definition-of-rw.fast-urewrite (equal x 'x))
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%restrict default definition-of-rw.fast-urewrite-list (memberp x '(x (cons x1 x2))))
            (%restrict default definition-of-rw.urewrite-list (memberp x '(x (cons x1 x2))))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.trace-fast-image-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-fast-image-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-fast-image-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-fast-image-of-rw.urewrite)
                             (flag 'list))))



(%autoprove forcing-rw.ftrace->rhs-of-rw.fast-urewrite
            (%disable default forcing-rw.trace-fast-image-of-rw.urewrite)
            (%use (%thm forcing-rw.trace-fast-image-of-rw.urewrite)))

(%autoprove forcing-rw.ftraces->rhses-of-rw.fast-urewrite-list
            (%disable default forcing-rw.trace-list-fast-image-of-rw.urewrite-list)
            (%use (%thm forcing-rw.trace-list-fast-image-of-rw.urewrite-list)))

(%autoprove forcing-rw.ftrace->fgoals-of-rw.fast-urewrite
            (%disable default forcing-rw.trace-fast-image-of-rw.urewrite)
            (%use (%thm forcing-rw.trace-fast-image-of-rw.urewrite)))

(%autoprove forcing-rw.ftraces->fgoals-of-rw.fast-urewrite-list
            (%disable default forcing-rw.trace-list-fast-image-of-rw.urewrite-list)
            (%use (%thm forcing-rw.trace-list-fast-image-of-rw.urewrite-list)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/fast-urewrite")

