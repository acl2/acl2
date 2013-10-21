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


(%autoadmit tactic.generalize-all-okp)
(%autoadmit tactic.generalize-all-env-okp)

(%autoprove booleanp-of-tactic.generalize-all-okp
            (%enable default tactic.generalize-all-okp))

(%autoprove booleanp-of-tactic.generalize-all-env-okp
            (%enable default tactic.generalize-all-env-okp))


(%autoadmit tactic.generalize-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.generalize-all-tac
            (%enable default tactic.generalize-all-tac))

(%autoprove forcing-tactic.generalize-all-okp-of-tactic.generalize-all-tac
            (%enable default
                     tactic.generalize-all-tac
                     tactic.generalize-all-okp))

(%autoprove forcing-tactic.generalize-all-env-okp-of-tactic.generalize-all-tac
            (%enable default
                     tactic.generalize-all-tac
                     tactic.generalize-all-env-okp))


(%autoadmit tactic.generalize-all-compile)

(encapsulate
 ()
 (local (%enable default
                 tactic.generalize-all-okp
                 tactic.generalize-all-env-okp
                 tactic.generalize-all-compile))

 (%autoprove forcing-logic.substitute-of-logic.replace-subterm-list-list-with-fresh-variable-free)
 (%autoprove forcing-logic.appeal-listp-of-tactic.generalize-all-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.generalize-all-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.generalize-all-compile))

(%ensure-exactly-these-rules-are-missing "../../tactics/generalize-all")
