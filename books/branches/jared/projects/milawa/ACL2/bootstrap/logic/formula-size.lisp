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
(include-book "formulas")
(%interactive)

;; BOZO shouldn't formula-size be using the proper accessors?  This definition
;; seems strange and not very good.
(%autoadmit logic.formula-size)

(%autoprove natp-of-logic.formula-size
            (%restrict default logic.formula-size (equal x 'x)))

(%autoprove logic.formula-size-nonzero
            (%restrict default logic.formula-size (equal x 'x)))

(%autoprove ordp-of-logic.formula-size)

(%autoprove forcing-logic.formula-size-of-logic.=lhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.=lhs))

(%autoprove forcing-logic.formula-size-of-logic.=rhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.=rhs))

(%autoprove forcing-logic.formula-size-of-logic.~arg
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.~arg))

(%autoprove forcing-logic.formula-size-of-logic.vlhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.vlhs))

(%autoprove forcing-logic.formula-size-of-logic.vrhs
            (%restrict default logic.formula-size (equal x 'x))
            (%enable default logic.fmtype logic.vrhs))

(%autoprove logic.formula-size-of-logic.pnot
            (%restrict default logic.formula-size (equal x '(cons 'pnot* (cons x 'nil))))
            (%enable default logic.pnot))

(%autoprove logic.formula-size-of-logic.por
            (%restrict default logic.formula-size (equal x '(cons 'por* (cons x (cons y 'nil)))))
            (%enable default logic.por))

(%autoprove logic.formula-size-of-pequal
            (%restrict default logic.formula-size (equal x '(cons 'pequal* (cons x (cons y 'nil)))))
            (%enable default logic.pequal))



(%autoadmit logic.formula-list-size)

(%autoprove logic.formula-list-size-when-not-consp
            (%restrict default logic.formula-list-size (equal x 'x)))

(%autoprove logic.formula-list-size-of-cons
            (%restrict default logic.formula-list-size (equal x '(cons a x))))

(%autoprove natp-of-logic.formula-list-size
            (%cdr-induction x))

(%autoprove ordp-of-logic.formula-list-size)

(%ensure-exactly-these-rules-are-missing "../../logic/formula-size")

