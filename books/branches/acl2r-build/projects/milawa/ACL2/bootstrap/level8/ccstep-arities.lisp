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
(include-book "trace-arities")
(include-book "ccsteps")
(%interactive)


(%autoadmit rw.faster-ccstepp)

(%autoprove rw.faster-ccstep-removal
            (%enable default rw.ccstepp rw.faster-ccstepp))

(%autoadmit rw.faster-ccstep-listp)

(%autoprove rw.faster-ccstep-list-removal
            (%cdr-induction x)
            (%restrict default rw.faster-ccstep-listp (equal x 'x)))


(%autoadmit rw.slow-ccstep-arities)

(%autoprove rw.slow-ccsteps-arities-correct
            (%enable default rw.slow-ccstep-arities))

(%autoadmit rw.ccstep-arities)

(%autoprove rw.cstep-arities-removal
            (%enable default rw.ccstep-arities rw.slow-ccstep-arities))


(%autoadmit rw.slow-ccstep-list-arities)

(%autoprove rw.slow-ccstep-list-arities-correct
            (%cdr-induction x)
            (%restrict default rw.slow-ccstep-list-arities (equal x 'x)))


(%autoadmit rw.ccstep-list-arities)

(%autoprove true-listp-of-rw.ccstep-list-arities
            (%autoinduct rw.ccstep-list-arities x acc)
            (%restrict default rw.ccstep-list-arities (equal x 'x)))

(%autoprove rw.ccstep-list-arities-removal
            (%autoinduct rw.ccstep-list-arities x acc)
            (%restrict default rw.ccstep-list-arities (equal x 'x))
            (%restrict default rw.slow-ccstep-list-arities (equal x 'x)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/ccstep-arities")

