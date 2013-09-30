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
(%interactive)


(defthmd crock1-for-tactic.split-first-compile
  ;; BOZO unlocalize/rename
  (implies (and (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                       (logic.strip-conclusions proofs))
                (equal (firstn n goals) y))
           (equal (logic.strip-conclusions (firstn n proofs))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas y))))
  :hints(("Goal"
          :in-theory (disable firstn-of-logic.disjoin-each-formula-list)
          :use ((:instance firstn-of-logic.disjoin-each-formula-list
                           (x (logic.term-list-list-formulas goals))
                           (y n))))))

(defthm crock2-for-tactic.split-first-compile
  ;; BOZO unlocalize/rename
  (implies (and (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                       (logic.strip-conclusions proofs))
                (equal (restn n goals) y))
           (equal (logic.strip-conclusions (restn n proofs))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas y))))
  :hints(("Goal"
          :in-theory (disable restn-of-logic.disjoin-each-formula-list)
          :use ((:instance restn-of-logic.disjoin-each-formula-list
                           (x (logic.term-list-list-formulas goals))
                           (y n))))))



(%autoadmit tactic.split-first-okp)

(%autoprove booleanp-of-tactic.split-first-okp
            (%enable default tactic.split-first-okp))


(%autoadmit tactic.split-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.split-first-tac
            (%enable default tactic.split-first-tac))

(%autoprove forcing-tactic.split-first-okp-of-tactic.split-first-tac
            (%enable default tactic.split-first-tac tactic.split-first-okp))


(%autoadmit tactic.split-first-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.split-first-okp
                 tactic.split-first-compile))

 (%autoprove crock1-for-tactic.split-first-compile
             (%disable default
                       firstn-of-logic.disjoin-each-formula-list
                       [outside]firstn-of-logic.disjoin-each-formula-list)
             (%use (%instance (%thm firstn-of-logic.disjoin-each-formula-list)
                              (x (logic.term-list-list-formulas goals))
                              (y n))))

 (%autoprove crock2-for-tactic.split-first-compile
             (%disable default
                       restn-of-logic.disjoin-each-formula-list
                       [outside]restn-of-logic.disjoin-each-formula-list)
             (%use (%instance (%thm restn-of-logic.disjoin-each-formula-list)
                              (x (logic.term-list-list-formulas goals))
                              (y n))))

 (local (%enable default
                 crock1-for-tactic.split-first-compile
                 crock2-for-tactic.split-first-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.split-first-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.split-first-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.split-first-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/split-first")
