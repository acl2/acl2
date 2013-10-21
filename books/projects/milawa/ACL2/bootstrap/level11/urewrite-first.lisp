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


(%autoadmit tactic.urewrite-first-okp)

(%autoprove booleanp-of-tactic.urewrite-first-okp
            (%enable default tactic.urewrite-first-okp))

(%autoadmit tactic.urewrite-first-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.urewrite-first-tac
            (%enable default tactic.urewrite-first-tac))

(%autoprove forcing-tactic.urewrite-first-okp-of-tactic.urewrite-first-tac
            (%forcingp nil)
            (%enable default
                     tactic.urewrite-first-tac
                     tactic.urewrite-first-okp))

(%autoadmit tactic.urewrite-first-compile)

(local (%enable default
                tactic.urewrite-first-okp
                tactic.urewrite-first-compile))

(local (%forcingp nil))

(%autoprove forcing-logic.appeal-listp-of-tactic.urewrite-first-compile)
(%autoprove forcing-logic.strip-conclusions-of-tactic.urewrite-first-compile)
(%autoprove forcing-logic.proof-listp-of-tactic.urewrite-first-compile
            (%disable default
                      MEMBERP-WHEN-MEMBERP-OF-CDR
                      MEMBERP-WHEN-NOT-CONSP
                      CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                      CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                      unusual-memberp-rules))

(%ensure-exactly-these-rules-are-missing "../../tactics/urewrite-first")
