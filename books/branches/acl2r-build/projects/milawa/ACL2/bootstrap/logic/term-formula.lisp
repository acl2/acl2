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
(include-book "substitute-formula")
(%interactive)


(%autoadmit logic.term-formula)

(%autoprove forcing-logic.formulap-of-logic.term-formula
            (%enable default logic.term-formula))

(%autoprove forcing-logic.formula-atblp-of-logic.term-formula
            (%enable default logic.term-formula))

(%autoprove logic.substitute-formula-of-logic.term-formula
            (%enable default logic.term-formula))



(%defprojection :list (logic.term-list-formulas x)
                :element (logic.term-formula x))

(%autoprove redefinition-of-logic.term-list-formulas
            (%cdr-induction x)
            (%enable default logic.term-formula))

(%autoprove forcing-logic.formula-listp-of-logic.term-list-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.term-list-formulas
            (%cdr-induction x))

(%autoprove memberp-of-logic.term-formula-and-logic.term-list-formulas
            (%cdr-induction x)
            (%enable default logic.term-formula))

(%autoprove memberp-of-logic.pnot-of-logic.pequal-nil-in-logic.term-list-formulas
            (%cdr-induction x)
            (%enable default logic.term-formula))

(%autoprove subsetp-of-logic.term-list-formulas-and-logic.term-list-formulas
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-of-logic.term-list-formulas
            (%cdr-induction x))




(%defprojection :list (logic.term-list-list-formulas x)
                :element (logic.term-list-formulas x))

(%autoprove forcing-logic.formula-list-listp-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-list-atblp-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove cons-listp-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove supserset-of-somep-of-logic.term-list-formulas-and-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove all-superset-of-somep-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove logic.term-list-list-formulas-of-list-list-fix
            (%cdr-induction x))

(%autoprove logic.substitute-formula-list-list-of-logic.term-list-list-formulas
            (%cdr-induction x))

(%autoprove logic.term-list-list-formulas-of-listify-each
            (%cdr-induction x)
            (%enable default logic.term-formula))


(%ensure-exactly-these-rules-are-missing "../../logic/term-formula")

