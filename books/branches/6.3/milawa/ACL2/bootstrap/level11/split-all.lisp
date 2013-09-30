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
(include-book "partition")
(include-book "skeletonp")
(%interactive)



;; BOZO all this stuff belongs somewhere else.

(%autoprove firstn-of-nfix
            (%autoinduct firstn))

(%autoprove restn-of-nfix
            (%autoinduct restn)
            (%restrict default restn (equal n 'n)))

(%autoprove cons-listp-of-list-list-fix
            ;; BOZO this was also autoproved in waterfall-steps.lisp, which caused a problem
            ;; during proof checking which seemed to have to do with one file overwriting
            ;; the other?  Now I'm just including this file in waterfall-steps.lisp to
            ;; avoid this.
            (%cdr-induction x))

(%autoprove true-list-listp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.term-list-listp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.term-list-list-atblp-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.strip-conclusions-list-of-partition
            (%autoinduct partition))

(%autoprove nat-listp-of-strip-lens-free)

(%autoprove logic.appeal-list-listp-of-partition
            (%autoinduct partition lens proofs))

(%autoprove true-list-listp-of-cdr-of-clause.split-list
            (%autoinduct clause.split-list))

(%autoprove list-list-fix-when-true-list-listp
            (%cdr-induction x))

(%autoprove clause.clause-list-list-formulas-of-partition
            (%autoinduct partition))

(%autoprove logic.proof-list-listp-of-partition
            (%autoinduct partition))



(%autoadmit tactic.split-all-okp)

(%autoprove booleanp-of-tactic.split-all-okp
            (%enable default tactic.split-all-okp))

(%autoprove forcing-cons-listp-of-simple-flatten
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-simple-flatten
            (%cdr-induction x))


(%autoadmit tactic.split-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.split-all-tac
            (%enable default tactic.split-all-tac))

(%autoprove forcing-tactic.split-all-okp-of-tactic.split-all-tac
            (%enable default
                     tactic.split-all-tac
                     tactic.split-all-okp))



(encapsulate
 ()
 (%autoadmit tactic.split-all-compile)

 (local (%enable default tactic.split-all-okp tactic.split-all-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.split-all-compile
             (%disable default
                       partition-of-simple-flatten
                       [outside]partition-of-simple-flatten)
             (%use (%instance
                    (%thm partition-of-simple-flatten)
                    (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                               (second (tactic.skeleton->extras x))
                                               (third (tactic.skeleton->extras x))
                                               (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))

 (%autoprove forcing-logic.strip-conclusions-of-tactic.split-all-compile
             (%disable default
                       partition-of-simple-flatten
                       [outside]partition-of-simple-flatten)
             (%use (%instance
                    (%thm partition-of-simple-flatten)
                    (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                               (second (tactic.skeleton->extras x))
                                               (third (tactic.skeleton->extras x))
                                               (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))

 (%autoprove forcing-logic.proof-listp-of-tactic.split-all-compile
             (%disable default
                       partition-of-simple-flatten
                       [outside]partition-of-simple-flatten)
             (%use (%instance
                    (%thm partition-of-simple-flatten)
                    (x (cdr (clause.split-list (first (tactic.skeleton->extras x))
                                               (second (tactic.skeleton->extras x))
                                               (third (tactic.skeleton->extras x))
                                               (list-list-fix (tactic.skeleton->goals (tactic.skeleton->history x)))))))))
 )

(%ensure-exactly-these-rules-are-missing "../../tactics/split-all")