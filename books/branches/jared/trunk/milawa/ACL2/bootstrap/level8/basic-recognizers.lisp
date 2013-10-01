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
(include-book "evaluator-bldr-2")
(%interactive)


(%autoadmit rw.fail-tracep)

(%autoprove booleanp-of-rw.fail-tracep
            (%enable default rw.fail-tracep))


(%autoadmit rw.transitivity-tracep)

(%autoprove booleanp-of-rw.transitivity-tracep
            (%enable default rw.transitivity-tracep))


(%autoadmit rw.equiv-by-args-tracep)

(%autoprove booleanp-of-rw.equiv-by-args-tracep
            (%enable default rw.equiv-by-args-tracep))



(%autoadmit rw.lambda-equiv-by-args-tracep)

(%autoprove booleanp-of-rw.lambda-equiv-by-args-tracep
            (%enable default rw.lambda-equiv-by-args-tracep))



(%autoadmit rw.beta-reduction-tracep)

(%autoprove booleanp-of-rw.beta-reduction-tracep
            (%enable default rw.beta-reduction-tracep))



(%autoadmit rw.ground-tracep)

(%autoprove booleanp-of-rw.ground-tracep
            (%enable default rw.ground-tracep))


(%autoadmit rw.if-specialcase-nil-tracep)

(%autoprove booleanp-of-rw.if-specialcase-nil-tracep
            (%enable default rw.if-specialcase-nil-tracep))



(%autoadmit rw.if-specialcase-t-tracep)

(%autoprove booleanp-of-rw.if-specialcase-t-tracep
            (%enable default rw.if-specialcase-t-tracep))



(%autoadmit rw.not-tracep)

(%autoprove booleanp-of-rw.not-tracep
            (%enable default rw.not-tracep))


(%autoadmit rw.negative-if-tracep)

(%autoprove booleanp-of-rw.negative-if-tracep
            (%enable default rw.negative-if-tracep))


(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/basic-recognizers")