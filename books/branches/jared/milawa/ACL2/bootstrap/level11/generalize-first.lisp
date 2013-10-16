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


(%autoadmit tactic.generalize-first-okp)
(%autoadmit tactic.generalize-first-env-okp)

(%autoprove booleanp-of-tactic.generalize-first-okp
            (%enable default tactic.generalize-first-okp))

(%autoprove booleanp-of-tactic.generalize-first-env-okp
            (%enable default tactic.generalize-first-env-okp))


(%autoadmit tactic.generalize-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.generalize-first-tac
            (%enable default tactic.generalize-first-tac))

(%autoprove forcing-tactic.generalize-first-okp-of-tactic.generalize-first-tac
            (%enable default
                     tactic.generalize-first-tac
                     tactic.generalize-first-okp))

(%autoprove forcing-tactic.generalize-first-env-okp-of-tactic.generalize-first-tac
            (%enable default
                     tactic.generalize-first-tac
                     tactic.generalize-first-env-okp))


(%autoadmit tactic.generalize-first-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.generalize-first-okp
                 tactic.generalize-first-env-okp
                 tactic.generalize-first-compile))

 (defthm crock1-for-tactic.generalize-first
   ;; BOZO unlocalize/rename
   (implies (equal x (logic.disjoin-formulas y))
            (equal (logic.substitute-formula x sigma)
                   (logic.disjoin-formulas (logic.substitute-formula-list y sigma)))))

 (defthm crock2-for-tactic.generalize-first
   ;; BOZO unlocalize/rename
   (implies (and (equal terms (logic.replace-subterm-list x old new) )
                 (not (memberp new (logic.term-list-vars x)))
                 (logic.variablep new)
                 (force (logic.term-listp x)))
            (equal (logic.substitute-list terms (list (cons new old)))
                   (list-fix x)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (%autoprove crock1-for-tactic.generalize-first)
 (%autoprove crock2-for-tactic.generalize-first)

 (%autoprove forcing-logic.appeal-listp-of-tactic.generalize-first-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.generalize-first-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.generalize-first-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/generalize-first")