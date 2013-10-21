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
(include-book "skeletonp")
(include-book "split-all") ;; BOZO yuck for cons-listp-of-list-list-fix ??
(%interactive)

(%autoprove true-list-listp-of-remove-supersets1
            (%autoinduct remove-supersets1 x acc)
            (%restrict default remove-supersets1 (equal todo 'x)))

(%autoprove true-list-listp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove true-list-listp-of-remove-duplicates-list
            (%cdr-induction x))

(%autoprove true-list-listp-of-third-of-clause.clean-clauses
            (%enable default clause.clean-clauses))

(%autoprove true-list-listp-of-third-of-clause.fast-clean-clauses
            (%enable default clause.fast-clean-clauses)
            (%disable default
                      clause.fast-clean-clauses-removal
                      clause.fast-clean-part1-removal))

(%autoprove true-list-listp-of-revappend
            (%autoinduct revappend x acc)
            (%restrict default revappend (equal x 'x))
            (%disable default forcing-revappend-removal))

(%autoprove true-list-listp-of-clause.aux-split
            (%autoinduct clause.aux-split)
            (%restrict default clause.aux-split (equal todo 'todo)))

(%autoprove true-list-listp-of-clause.aux-limsplit
            (%autoinduct clause.aux-limsplit todo done splitlimit)
            (%restrict default clause.aux-limsplit (equal todo 'todo)))

(%autoprove true-list-listp-of-clause.simple-limsplit
            (%enable default clause.simple-limsplit))

(%autoprove true-list-listp-of-clause.simple-split
            (%enable default clause.simple-split))

(%autoprove true-list-listp-of-cdr-of-clause.split
            (%forcingp nil)
            (%enable default clause.split))

(%autoprove logic.formula-listp-of-remove-duplicates-free)

(%autoprove logic.formula-list-atblp-of-remove-duplicates-free)

(%autoprove subsetp-of-remove-duplicates-one-indirect)

;; this is now included as part of split-all to avoid overwriting files.
;; (%autoprove cons-listp-of-list-list-fix
;;             (%cdr-induction x))

(%autoprove true-list-listp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.term-list-listp-of-list-list-fix
            (%cdr-induction x))

(%autoprove list-list-fix-when-true-list-listp
            (%cdr-induction x))

(%autoprove logic.term-list-list-atblp-of-list-list-fix
            (%cdr-induction x))


(%autoadmit rw.flag-waterstepp)

(%autoadmit rw.waterstepp)

(%autoadmit rw.waterstep-listp)

(%autoprove definition-of-rw.waterstepp
            (%restrict default rw.flag-waterstepp (equal x 'x))
            (%enable default rw.waterstepp rw.waterstep-listp))

(%autoprove definition-of-rw.waterstep-listp
            (%restrict default rw.flag-waterstepp (equal x 'x))
            (%enable default rw.waterstepp rw.waterstep-listp))

(%autoprove rw.waterstep-listp-when-not-consp
            (%restrict default definition-of-rw.waterstep-listp (equal x 'x)))

(%autoprove rw.waterstep-listp-of-cons
            (%restrict default definition-of-rw.waterstep-listp (equal x '(cons a x))))

(%autoadmit rw.raw-waterstep-induction)

(%autoprove lemma-for-booleanp-of-rw.waterstepp
            (%autoinduct rw.raw-waterstep-induction flag x)
            (%restrict default definition-of-rw.waterstepp (equal x 'x)))

(%autoprove booleanp-of-rw.waterstepp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.waterstepp)
                             (flag 'clause))))

(%autoprove booleanp-of-rw.waterstep-listp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.waterstepp)
                             (flag 'list))))

(%deflist rw.waterstep-listp (x)
          (rw.waterstepp x))


(%autoadmit rw.waterstep)
(%autoadmit rw.waterstep->method)
(%autoadmit rw.waterstep->clause)
(%autoadmit rw.waterstep->extras)
(%autoadmit rw.waterstep->substeps)

(encapsulate
 ()
 (local (%enable default
                 rw.waterstep
                 rw.waterstep->method
                 rw.waterstep->clause
                 rw.waterstep->extras
                 rw.waterstep->substeps))
 (%autoprove rw.waterstep->method-of-rw.waterstep)
 (%autoprove rw.waterstep->clause-of-rw.waterstep)
 (%autoprove rw.waterstep->extras-of-rw.waterstep)
 (%autoprove rw.waterstep->substeps-of-rw.waterstep)
 (%autoprove rank-of-rw.waterstep->substeps)

 (%autoprove rw.waterstepp-of-rw.waterstep
             (%restrict default definition-of-rw.waterstepp
                        (and (logic.functionp x)
                             (equal (logic.function-name x) 'cons))))

 (%autoprove symbolp-of-rw.waterstep->method
             (%restrict default definition-of-rw.waterstepp (equal x 'x)))

 (%autoprove logic.term-listp-of-rw.waterstep->clause
             (%restrict default definition-of-rw.waterstepp (equal x 'x)))

 (%autoprove consp-of-rw.waterstep->clause
             (%restrict default definition-of-rw.waterstepp (equal x 'x)))

 (%autoprove true-listp-of-rw.waterstep->clause
             (%restrict default definition-of-rw.waterstepp (equal x 'x)))

 (%autoprove rw.waterstep-listp-of-rw.waterstep->substeps
             (%restrict default definition-of-rw.waterstepp (equal x 'x))))



(%defprojection :list (rw.waterstep-list->clauses x)
                :element (rw.waterstep->clause x)
                :nil-preservingp t)

(%autoprove cons-listp-of-rw.waterstep-list->clauses
            (%cdr-induction x))

(%autoprove true-list-listp-of-rw.waterstep-list->clauses
            (%cdr-induction x))

(%autoprove logic.term-list-listp-of-rw.waterstep-list->clauses
            (%cdr-induction x))


(%autoadmit rw.waterstep-induction)

(%autoadmit rw.flag-waterstep-atblp)
(%autoadmit rw.waterstep-atblp)
(%autoadmit rw.waterstep-list-atblp)

(%autoprove definition-of-rw.waterstep-atblp
            (%restrict default rw.flag-waterstep-atblp (equal x 'x))
            (%enable default rw.waterstep-atblp rw.waterstep-list-atblp))

(%autoprove definition-of-rw.waterstep-list-atblp
            (%restrict default rw.flag-waterstep-atblp (equal x 'x))
            (%enable default rw.waterstep-atblp rw.waterstep-list-atblp))

(%autoprove rw.flag-waterstep-atblp-of-clause
            (%enable default rw.waterstep-atblp))

(%autoprove rw.flag-waterstep-list-atblp-of-clause
            (%enable default rw.waterstep-list-atblp))

(%autoprove rw.waterstep-list-atblp-when-not-consp
            (%restrict default definition-of-rw.waterstep-list-atblp (equal x 'x)))

(%autoprove rw.waterstep-list-atblp-of-cons
            (%restrict default definition-of-rw.waterstep-list-atblp (equal x '(cons a x))))

(%autoprove rw.waterstep-atblp-of-nil
            (%restrict default definition-of-rw.waterstep-atblp (equal x ''nil)))

(%autoprove lemma-for-booleanp-of-rw.waterstep-atblp
            (%autoinduct rw.waterstep-induction flag x)
            (%restrict default definition-of-rw.waterstep-atblp (equal x 'x)))

(%autoprove booleanp-of-rw.waterstep-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.waterstep-atblp)
                             (flag 'clause))))

(%autoprove booleanp-of-rw.waterstep-list-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.waterstep-atblp)
                             (flag 'list))))


(%deflist rw.waterstep-list-atblp (x atbl)
          (rw.waterstep-atblp x atbl))

(%autoprove logic.term-list-atblp-of-rw.waterstep->clause
            (%restrict default definition-of-rw.waterstep-atblp (equal x 'x)))

(%autoprove rw.waterstep-list-atblp-of-rw.waterstep->substeps
            (%restrict default definition-of-rw.waterstep-atblp (equal x 'x)))

(%autoprove rw.waterstep-atblp-of-rw.waterstep
            (%restrict default definition-of-rw.waterstep-atblp
                       (equal x '(rw.waterstep method clause extras substeps))))


(%autoadmit rw.stop-waterstep-okp)
(%autoprove booleanp-of-rw.stop-waterstep-okp
            (%enable default rw.stop-waterstep-okp))

(%autoadmit rw.urewrite-waterstep-okp)
(%autoprove booleanp-of-rw.urewrite-waterstep-okp
            (%enable default rw.urewrite-waterstep-okp))

(%autoadmit rw.crewrite-waterstep-okp)
(%autoprove booleanp-of-rw.crewrite-waterstep-okp
            (%enable default rw.crewrite-waterstep-okp))

(%autoadmit rw.split-waterstep-okp)
(%autoprove booleanp-of-rw.split-waterstep-okp
            (%enable default rw.split-waterstep-okp))


(%autoadmit rw.flag-waterstep-okp)
(%autoadmit rw.waterstep-okp)
(%autoadmit rw.waterstep-list-okp)
(%autoprove definition-of-rw.waterstep-okp
            (%restrict default rw.flag-waterstep-okp (equal x 'x))
            (%enable default rw.waterstep-okp rw.waterstep-list-okp))
(%autoprove definition-of-rw.waterstep-list-okp
            (%restrict default rw.flag-waterstep-okp (equal x 'x))
            (%enable default rw.waterstep-okp rw.waterstep-list-okp))

(%autoprove rw.waterstep-list-okp-when-not-consp
            (%restrict default definition-of-rw.waterstep-list-okp (equal x 'x)))
(%autoprove rw.waterstep-list-okp-of-cons
            (%restrict default definition-of-rw.waterstep-list-okp (equal x '(cons a x))))

(%autoprove rw.waterstep-okp-of-nil
            (%restrict default definition-of-rw.waterstep-okp (equal x ''nil)))

(%autoprove lemma-for-booleanp-of-rw.waterstep-okp
            (%autoinduct rw.waterstep-induction flag x)
            (%restrict default definition-of-rw.waterstep-okp (equal x 'x)))

(%autoprove booleanp-of-rw.waterstep-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.waterstep-okp)
                             (flag 'clause))))

(%autoprove booleanp-of-rw.waterstep-list-okp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.waterstep-okp)
                             (flag 'list))))

(%deflist rw.waterstep-list-okp (x world)
          (rw.waterstep-okp x world))



(%autoadmit rw.flag-waterfall-subgoals)
(%autoadmit rw.waterfall-subgoals)
(%autoadmit rw.waterfall-list-subgoals)

(%autoprove definition-of-rw.waterfall-subgoals
            (%enable default rw.waterfall-subgoals rw.waterfall-list-subgoals)
            (%restrict default rw.flag-waterfall-subgoals (equal x 'x)))

(%autoprove definition-of-rw.waterfall-list-subgoals
            (%enable default rw.waterfall-subgoals rw.waterfall-list-subgoals)
            (%restrict default rw.flag-waterfall-subgoals (equal x 'x)))

(%autoprove rw.flag-waterfall-subgoals-of-clause
            (%enable default rw.waterfall-subgoals))

(%autoprove rw.flag-waterfall-list-subgoals-of-clause
            (%enable default rw.waterfall-list-subgoals))

(%autoprove rw.waterfall-list-subgoals-when-not-consp
            (%restrict default definition-of-rw.waterfall-list-subgoals (equal x 'x)))

(%autoprove rw.waterfall-list-subgoals-of-cons
            (%restrict default definition-of-rw.waterfall-list-subgoals (equal x '(cons a x))))

(%autoprove lemma-for-logic.term-list-listp-of-rw.waterfall-subgoals
            (%autoinduct rw.flag-waterfall-subgoals flag x)
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))

(%autoprove logic.term-list-listp-of-rw.waterfall-subgoals
            (%use (%instance (%thm lemma-for-logic.term-list-listp-of-rw.waterfall-subgoals)
                             (flag 'clause))))

(%autoprove logic.term-list-listp-of-rw.waterfall-list-subgoals
            (%use (%instance (%thm lemma-for-logic.term-list-listp-of-rw.waterfall-subgoals)
                             (flag 'list))))

(%autoprove lemma-for-cons-listp-of-rw.waterfall-subgoals
            (%autoinduct rw.flag-waterfall-subgoals flag x)
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))

(%autoprove cons-listp-of-rw.waterfall-subgoals
            (%use (%instance (%thm lemma-for-cons-listp-of-rw.waterfall-subgoals)
                             (flag 'clause))))

(%autoprove cons-listp-of-rw.waterfall-list-subgoals
            (%use (%instance (%thm lemma-for-cons-listp-of-rw.waterfall-subgoals)
                             (flag 'list))))

(%autoprove lemma-for-true-list-listp-of-rw.waterfall-subgoals
            (%autoinduct rw.flag-waterfall-subgoals flag x)
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))

(%autoprove true-list-listp-of-rw.waterfall-subgoals
            (%use (%instance (%thm lemma-for-true-list-listp-of-rw.waterfall-subgoals)
                             (flag 'clause))))

(%autoprove true-list-listp-rw.waterfall-list-subgoals
            (%use (%instance (%thm lemma-for-true-list-listp-of-rw.waterfall-subgoals)
                             (flag 'list))))

(%autoprove lemma-for-true-listp-of-rw.waterfall-subgoals
            (%autoinduct rw.flag-waterfall-subgoals flag x)
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))

(%autoprove true-listp-of-rw.waterfall-subgoals
            (%use (%instance (%thm lemma-for-true-listp-of-rw.waterfall-subgoals)
                             (flag 'clause))))

(%autoprove true-listp-rw.waterfall-list-subgoals
            (%use (%instance (%thm lemma-for-true-listp-of-rw.waterfall-subgoals)
                             (flag 'list))))
