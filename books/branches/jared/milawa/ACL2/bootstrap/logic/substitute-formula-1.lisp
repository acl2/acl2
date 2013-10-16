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
(include-book "formulas")
(include-book "substitute-term")
(%interactive)

(%autoadmit logic.substitute-formula)

(%autoprove logic.substitute-formula-of-logic.por
            (%restrict default logic.substitute-formula (equal formula '(logic.por x y))))

(%autoprove logic.substitute-formula-of-logic.pnot
            (%restrict default logic.substitute-formula (equal formula '(logic.pnot x))))

(%autoprove logic.substitute-formula-of-logic.pequal
            (%restrict default logic.substitute-formula (equal formula '(logic.pequal x y))))

(%autoprove logic.substitute-formula-when-malformed-cheap
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove logic.substitute-formula-of-nil)

(%autoprove forcing-logic.formulap-of-logic.substitute-formula
            (%logic.formulap-induction formula)
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove forcing-logic.formula-atblp-of-logic.substitute-formula
            (%logic.formulap-induction formula)
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove forcing-logic.substitute-formula-under-iff
            (%restrict default logic.substitute-formula (equal formula 'formula)))

(%autoprove forcing-logic.fmtype-of-logic.substitute-formula
            (%restrict default logic.substitute-formula (equal formula 'x)))

(%autoprove forcing-logic.=lhs-of-logic.substitute-formula
            (%restrict default logic.substitute-formula (equal formula 'x)))

(%autoprove forcing-logic.=rhs-of-logic.substitute-formula
            (%restrict default logic.substitute-formula (equal formula 'x)))

