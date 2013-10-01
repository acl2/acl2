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
(include-book "hypboxp")
(%interactive)

(%autoadmit rw.slow-hypbox-arities)
(%autoadmit rw.hypbox-arities)

(%autoprove true-listp-of-rw.hypbox-arities
            (%enable default rw.hypbox-arities))

(%autoprove rw.hypbox-arities-removal
            (%enable default rw.hypbox-arities rw.slow-hypbox-arities))

(%autoprove rw.slow-hypbox-arities-correct
            (%forcingp nil)
            (%enable default
                     rw.hypbox-arities
                     rw.slow-hypbox-arities
                     rw.hypbox-atblp))

(%autoadmit rw.fast-hypbox-atblp)

(%autoprove rw.fast-hypbox-atblp-removal
            (%enable default rw.fast-hypbox-atblp))



(%autoadmit rw.slow-hypbox-list-arities)
(%autoadmit rw.hypbox-list-arities)

(%autoprove true-listp-of-rw.hypbox-list-arities
            (%autoinduct rw.hypbox-list-arities)
            (%restrict default rw.hypbox-list-arities (equal x 'x)))

(%autoprove rw.hypbox-list-arities-removal
            (%autoinduct rw.hypbox-list-arities)
            (%restrict default rw.hypbox-list-arities (equal x 'x))
            (%restrict default rw.slow-hypbox-list-arities (equal x 'x)))

(%autoprove rw.slow-hypbox-list-arities-correct
            (%cdr-induction x)
            (%restrict default rw.slow-hypbox-list-arities (equal x 'x)))



(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/hypbox-arities")