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
(include-book "urewrite-builders")
(%interactive)

(%autoadmit rw.empty-hypbox)

(%autoadmit rw.flag-urewrite)
(%autoadmit rw.urewrite)
(%autoadmit rw.urewrite-list)

(%autoprove definition-of-rw.urewrite
            (%enable default rw.urewrite rw.urewrite-list)
            (%restrict default rw.flag-urewrite (equal x 'x)))

(%autoprove definition-of-rw.urewrite-list
            (%enable default rw.urewrite rw.urewrite-list)
            (%restrict default rw.flag-urewrite (equal x 'x)))

(%autoprove rw.flag-urewrite-of-term
            (%enable default rw.urewrite))

(%autoprove rw.flag-urewrite-of-list
            (%enable default rw.urewrite-list))


(%autoprove rw.urewrite-list-when-not-consp
            (%restrict default definition-of-rw.urewrite-list (equal x 'x)))

(%autoprove rw.urewrite-list-of-cons
            (%restrict default definition-of-rw.urewrite-list (equal x '(cons a x))))

(%defprojection :list (rw.urewrite-list x iffp control n)
                :element (rw.urewrite x iffp control n))

(local (%disable default
                 formula-decomposition
                 type-set-like-rules
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 unusual-memberp-rules
                 unusual-subsetp-rules
                 same-length-prefixes-equal-cheap
                 forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                 minus-when-not-less
                 rw.tracep-when-memberp-of-rw.trace-listp
                 rw.trace-list-rhses-when-not-consp))

(local (%splitlimit 10))

(%autoprove lemma-for-forcing-rw.tracep-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split cleanup urewrite))
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%enable default expensive-term/formula-inference)
            (%auto))

(%autoprove forcing-rw.tracep-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-listp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.tracep-of-rw.urewrite)
                             (flag 'list))))



;; BOZO probably just take this out of our disables from above.
(local (%enable default expensive-arithmetic-rules-two))


(%autoprove lemma-for-forcing-rw.trace->iffp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split cleanup urewrite))
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.trace->iffp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-iffps-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->iffp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace->lhs-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split cleanup urewrite))
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition))

(%autoprove forcing-rw.trace->lhs-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-lhses-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->lhs-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace->nhyps-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%auto :strategy (split urewrite crewrite))
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default
                     expensive-term/formula-inference
                     formula-decomposition))

(%autoprove forcing-rw.trace->nhyps-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace->nhyps-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-nhyps-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace->nhyps-of-rw.urewrite)
                             (flag 'list))))




(%autoprove lemma-for-forcing-rw.trace-atblp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x)))

(%autoprove forcing-rw.trace-atblp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-atblp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-atblp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-atblp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace-env-okp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x)))

(%autoprove forcing-rw.trace-env-okp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-env-okp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-env-okp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.trace-okp-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x))
            (%auto)
            (%enable default expensive-term/formula-inference))

(%autoprove forcing-rw.trace-okp-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.trace-list-okp-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.trace-okp-of-rw.urewrite)
                             (flag 'list))))



(%autoprove lemma-for-forcing-rw.collect-forced-goals-of-rw.urewrite
            (%autoinduct rw.flag-urewrite flag x iffp control n)
            (%disable default expensive-term/formula-inference)
            (%liftlimit 1)
            (%create-theory splitters)
            (%enable splitters (gather from default (not (clause.simple-termp rhs))))
            (%disable default splitters)
            (%auto :strategy (urewrite cleanup split))
            (%forcingp nil)
            (%auto)
            (%enable default splitters)
            (%auto)
            (%restrict default definition-of-rw.urewrite (equal x 'x)))

(%autoprove forcing-rw.collect-forced-goals-of-rw.urewrite
            (%use (%instance (%thm lemma-for-forcing-rw.collect-forced-goals-of-rw.urewrite)
                             (flag 'term))))

(%autoprove forcing-rw.collect-forced-goals-list-of-rw.urewrite-list
            (%use (%instance (%thm lemma-for-forcing-rw.collect-forced-goals-of-rw.urewrite)
                             (flag 'list))))



(%autoprove forcing-rw.trace-list-formulas-of-rw.urewrite-list
            (%use (%instance (%thm rw.trace-list-formulas-when-all-equalp-of-rw.trace-list-hypboxes)
                             (hypbox (rw.empty-hypbox))
                             (x (rw.urewrite-list x iffp control n)))))

(%autoprove forcing-rw.trace-list-conclusion-formulas-of-rw.urewrite-list
            (%cdr-induction x)
            (%restrict default rw.trace-list-conclusion-formulas (equal x 'x))
            (%enable default rw.trace-conclusion-formula))



(%defprojection :list (rw.urewrite-list-list x iffp control n)
                :element (rw.urewrite-list x iffp control n))

(%autoprove cons-listp-of-rw.urewrite-list-list
            (%cdr-induction x))

(%autoprove forcing-rw.trace-list-listp-of-rw.urewrite-list-list
            (%cdr-induction x))

(%autoprove forcing-rw.collect-forced-goals-list-list-of-rw.urewrite-list-list
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../rewrite/urewrite")

