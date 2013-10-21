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
(include-book "assms-top")
(%interactive)


(%autoprove submap-of-eachp-when-submapp
            (%cdr-induction x))

(%autoprove submap-of-eachp-when-submapp-alt)

(%autoadmit rw.collect-critical-hyps)

(%autoprove subsetp-of-rw.collect-critical-hyps
            (%autoinduct rw.collect-critical-hyps)
            (%restrict default rw.collect-critical-hyps (equal hyps 'hyps)))




(%autoadmit rw.critical-hyps)

(%autoprove subsetp-of-rw.critical-hyps
            (%enable default rw.critical-hyps))

(%autoprove logic.term-listp-of-rw.critical-hyps
            (%disable default
                      subsetp-of-rw.critical-hyps
                      [outside]subsetp-of-rw.critical-hyps)
            (%use (%instance (%thm subsetp-of-rw.critical-hyps))))



(%autoadmit rw.limit-hyps-aux)

(%autoadmit rw.limit-hyps)




(%autoadmit rw.find-extensions-for-sigma-aux)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma-aux
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma-aux
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-aux
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-aux-free
            (%autoinduct rw.find-extensions-for-sigma-aux)
            (%restrict default rw.find-extensions-for-sigma-aux (equal trueterms 'trueterms)))



(%autoadmit rw.find-extensions-for-sigma)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma
            (%enable default rw.find-extensions-for-sigma))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma
            (%enable default rw.find-extensions-for-sigma))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma
            (%enable default rw.find-extensions-for-sigma))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-free
            (%enable default rw.find-extensions-for-sigma))





(%autoadmit rw.find-extensions-for-sigma-list)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma-list
            (%autoinduct rw.find-extensions-for-sigma-list)
            (%restrict default rw.find-extensions-for-sigma-list (equal sigmas 'sigmas)))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma-list
            (%autoinduct rw.find-extensions-for-sigma-list)
            (%restrict default rw.find-extensions-for-sigma-list (equal sigmas 'sigmas)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-sigma-list
            (%autoinduct rw.find-extensions-for-sigma-list)
            (%restrict default rw.find-extensions-for-sigma-list (equal sigmas 'sigmas)))




(%autoadmit rw.find-extensions-for-crit-hyps)

(%autoprove forcing-logic.sigma-listp-of-rw.find-extensions-for-crit-hyps
            (%autoinduct rw.find-extensions-for-crit-hyps)
            (%restrict default rw.find-extensions-for-crit-hyps (equal hyps 'hyps)))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-crit-hyps
            (%autoinduct rw.find-extensions-for-crit-hyps)
            (%restrict default rw.find-extensions-for-crit-hyps (equal hyps 'hyps)))

(%autoprove submap-of-eachp-of-rw.find-extensions-for-crit-hyps
            (%autoinduct rw.find-extensions-for-crit-hyps)
            (%restrict default rw.find-extensions-for-crit-hyps (equal hyps 'hyps)))





(%autoadmit rw.create-sigmas-to-try)

(%autoprove forcing-logic.sigma-listp-of-rw.create-sigmas-to-try
            (%enable default rw.create-sigmas-to-try))

(%autoprove forcing-logic.sigma-list-atblp-of-rw.create-sigmas-to-try
            (%enable default rw.create-sigmas-to-try))

(%autoprove submap-of-eachp-of-rw.create-sigmas-to-try
            (%enable default rw.create-sigmas-to-try))



(%ensure-exactly-these-rules-are-missing "../../rewrite/match-free")