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
(include-book "tracep")
(%interactive)


(%autoadmit rw.crewrite-if-specialcase-same-tracep)

(%autoprove booleanp-of-rw.crewrite-if-specialcase-same-tracep
            (%enable default rw.crewrite-if-specialcase-same-tracep))


(%autoadmit rw.crewrite-if-generalcase-tracep)

(%autoprove booleanp-of-rw.crewrite-if-generalcase-tracep
            (%enable default rw.crewrite-if-generalcase-tracep))



(%autoadmit rw.crewrite-rule-tracep)

(%autoprove booleanp-of-rw.crewrite-rule-tracep
            (%enable default rw.crewrite-rule-tracep))



(%autoadmit rw.crewrite-rule-trace-env-okp)

(%autoprove booleanp-of-rw.crewrite-rule-trace-env-okp
            (%enable default rw.crewrite-rule-trace-env-okp))



(%autoadmit rw.assumptions-tracep)

(%autoprove booleanp-of-rw.assumptions-tracep
            (%enable default rw.assumptions-tracep))



(%autoadmit rw.force-tracep)

(%autoprove booleanp-of-rw.force-tracep
            (%enable default rw.force-tracep))



(%autoadmit rw.weakening-tracep)

(%autoprove booleanp-of-rw.weakening-tracep
            (%enable default rw.weakening-tracep))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/crewrite-recognizers")
