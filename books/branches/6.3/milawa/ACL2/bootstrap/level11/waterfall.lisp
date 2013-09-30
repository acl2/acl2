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
(include-book "waterfall-main")
(include-book "waterfall-compiler")
(%interactive)


(%autoadmit tactic.waterfall-okp)

(%autoprove booleanp-of-tactic.waterfall-okp
            (%enable default tactic.waterfall-okp))


(%autoadmit rw.waterfall-list-wrapper)
(%enable default rw.waterfall-list-wrapper)

(%autoadmit tactic.waterfall-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.waterfall-tac
            (%enable default tactic.waterfall-tac))

(%autoprove forcing-tactic.waterfall-okp-of-tactic.waterfall-tac
            (%enable default tactic.waterfall-tac tactic.waterfall-okp)
            (%restrict default nth (logic.constantp n)))


(%autoadmit tactic.waterfall-compile)

(encapsulate
 ()
 (local (%enable default tactic.waterfall-okp tactic.waterfall-compile))

 (%autoprove forcing-logic.appeal-listp-of-tactic.waterfall-compile
             (%auto :strategy (cleanup split urewrite))
             ;; Wow, this is really nice.  I wish I could do this in ACL2.
             (%generalize (NTH '5 (TACTIC.SKELETON->EXTRAS X)) ufastp)
             (%generalize (nth '6 (TACTIC.SKELETON->EXTRAS X)) cfastp)
             (%generalize (car (TACTIC.SKELETON->EXTRAS X)) wsteps)
             (%generalize (car (cdr (TACTIC.SKELETON->EXTRAS X))) theoryname)
             (%generalize (CAR (CDR (CDR (CDR (TACTIC.SKELETON->EXTRAS X))))) maxdepth)
             (%generalize (CAR (CDR (CDR (TACTIC.SKELETON->EXTRAS X)))) strategy))

 (%autoprove forcing-logic.strip-conclusions-of-tactic.waterfall-compile
             (%auto :strategy (cleanup split urewrite))
             ;; Wow, this is really nice.  I wish I could do this in ACL2.
             (%generalize (NTH '5 (TACTIC.SKELETON->EXTRAS X)) ufastp)
             (%generalize (nth '6 (TACTIC.SKELETON->EXTRAS X)) cfastp)
             (%generalize (car (TACTIC.SKELETON->EXTRAS X)) wsteps)
             (%generalize (car (cdr (TACTIC.SKELETON->EXTRAS X))) theoryname)
             (%generalize (CAR (CDR (CDR (CDR (TACTIC.SKELETON->EXTRAS X))))) maxdepth)
             (%generalize (CAR (CDR (CDR (TACTIC.SKELETON->EXTRAS X)))) strategy))

 (%autoprove forcing-logic.proof-listp-of-tactic.waterfall-compile
             (%auto :strategy (cleanup split urewrite))
             ;; Wow, this is really nice.  I wish I could do this in ACL2.
             (%generalize (NTH '5 (TACTIC.SKELETON->EXTRAS X)) ufastp)
             (%generalize (nth '6 (TACTIC.SKELETON->EXTRAS X)) cfastp)
             (%generalize (car (TACTIC.SKELETON->EXTRAS X)) wsteps)
             (%generalize (car (cdr (TACTIC.SKELETON->EXTRAS X))) theoryname)
             (%generalize (CAR (CDR (CDR (CDR (TACTIC.SKELETON->EXTRAS X))))) maxdepth)
             (%generalize (CAR (CDR (CDR (TACTIC.SKELETON->EXTRAS X)))) strategy)))


(%ensure-exactly-these-rules-are-missing "../../tactics/waterfall")