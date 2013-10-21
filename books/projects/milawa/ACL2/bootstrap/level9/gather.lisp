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
(include-book "theoryp")
(%interactive)


(%autoadmit rw.rule-components)
(%enable default rw.rule-components)


(%autoadmit rw.consider-rule)

(%autoprove booleanp-of-rw.consider-rule
            (%enable default rw.consider-rule))


(%autoadmit rw.gather-rules-from-list)

(%autoprove true-listp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))

(%autoprove forcing-rw.rule-listp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))

(%autoprove forcing-rw.rule-list-atblp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))

(%autoprove forcing-rw.rule-list-env-okp-of-rw.gather-rules-from-list
            (%autoinduct rw.gather-rules-from-list)
            (%restrict default rw.gather-rules-from-list (equal rules 'rules)))


(%autoadmit rw.gather-rules-from-map)

(%autoprove true-listp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))

(%autoprove rw.rule-listp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))

(%autoprove rw.rule-list-atblp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))

(%autoprove rw.rule-list-env-okp-of-rw.gather-rules-from-map
            (%autoinduct rw.gather-rules-from-map)
            (%restrict default rw.gather-rules-from-map (equal rulemap 'rulemap)))


(%autoadmit rw.gather-rules-from-theory)

(%autoprove true-listp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%autoprove rw.rule-listp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%autoprove rw.rule-list-atblp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%autoprove rw.rule-list-env-okp-of-rw.gather-rules-from-theory
            (%autoinduct rw.gather-rules-from-theory)
            (%restrict default rw.gather-rules-from-theory (equal theory 'theory)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/gather")