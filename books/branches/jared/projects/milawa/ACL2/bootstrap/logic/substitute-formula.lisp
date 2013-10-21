;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
(include-book "substitute-formula-2-each")
(include-book "substitute-formula-2-list")
(include-book "disjoin-formulas")
(include-book "negate-formulas")
(include-book "pequal-list")
(include-book "por-list")
(%interactive)

(%autoprove logic.substitute-formula-of-logic.disjoin-formulas
            (%cdr-induction x)
            (%restrict default logic.disjoin-formulas (equal x 'x))
            (%disable default
                      ;; These rules cause some problems with forcing
                      forcing-logic.fmtype-of-logic.substitute-formula
                      forcing-logic.fmtype-of-logic.disjoin-formulas
                      forcing-logic.formula-listp-of-logic.substitute-formula-list
                      forcing-logic.vlhs-of-logic.disjoin-formulas
                      forcing-logic.formulap-of-logic.disjoin-formulas
                      forcing-logic.formulap-of-logic.substitute-formula
                      forcing-logic.formulap-of-logic.por
                      forcing-equal-of-logic.por-rewrite-two
                      equal-of-logic.disjoin-formulas-and-logic.disjoin-formulas-when-same-len
                      aggressive-equal-of-logic.pors))

(%autoprove logic.substitute-formula-list-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.pequal-list
            (%cdr-cdr-induction x y)
            (%disable default
                      forcing-equal-of-logic.pequal-list-rewrite
                      forcing-equal-of-logic.pequal-list-rewrite-alt))

(%autoprove logic.substitute-formula-list-of-logic.por-list
            (%cdr-cdr-induction x y)
            (%disable default
                      forcing-equal-of-logic.por-list-rewrite
                      forcing-equal-of-logic.por-list-rewrite-alt))



(%defprojection :list (logic.substitute-formula-list-list x sigma)
                :element (logic.substitute-formula-list x sigma)
                ;; BOZO this is nil-preserving, but the ACL2 model needs to be updated with that fact.
                ;; :nil-preservingp t
                )

(%autoprove forcing-logic.formula-list-listp-of-logic.substitute-formula-list-list
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-list-atblp-of-logic.substitute-formula-list-list
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.disjoin-each-formula-list
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.disjoin-each-formula-list-free)

(%ensure-exactly-these-rules-are-missing "../../logic/substitute-formula")

