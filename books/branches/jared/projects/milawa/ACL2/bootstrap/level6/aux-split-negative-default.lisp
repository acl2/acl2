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
(include-book "aux-split")
(%interactive)

;; speed hint
(local (%disable default
                 AGGRESSIVE-EQUAL-OF-LOGIC.PNOTS
                 AGGRESSIVE-EQUAL-OF-LOGIC.PEQUALS
                 AGGRESSIVE-EQUAL-OF-LOGIC.PORS
                 FORCING-LOGIC.FUNCTION-OF-LOGIC.FUNCTION-NAME-AND-LOGIC.FUNCTION-ARGS-FREE
                 LOGIC.TERM-LISTP-OF-SUBSETP-WHEN-LOGIC.TERM-LISTP
                 LOGIC.TERM-LISTP-WHEN-LOGIC.VARIABLE-LISTP-CHEAP
                 FORCING-LOGIC.DISJOIN-FORMULAS-OF-TWO-ELEMENT-LIST
                 LOGIC.DISJOIN-FORMULAS-WHEN-NOT-CONSP

                 CONSP-WHEN-LOGIC.LAMBDAP-CHEAP
                 LOGIC.FUNCTIONP-WHEN-LOGIC.LAMBDAP-CHEAP
                 LOGIC.TERMP-WHEN-INVALID-MAYBE-EXPENSIVE

                 logic.termp-when-logic.formulap
                 same-length-prefixes-equal-cheap
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 unusual-subsetp-rules
                 car-when-not-consp
                 cdr-when-not-consp
                 type-set-like-rules
                 unusual-memberp-rules
                 ))

(%autoadmit clause.aux-split-negative-default)

(local (%enable default
                clause.aux-split-goal
                clause.aux-split-negative-default
                logic.term-formula))

(%autoprove forcing-logic.appealp-of-clause.aux-split-negative-default)

(%autoprove forcing-logic.conclusion-of-clause.aux-split-negative-default)

(%autoprove forcing-logic.proofp-of-clause.aux-split-negative-default)
