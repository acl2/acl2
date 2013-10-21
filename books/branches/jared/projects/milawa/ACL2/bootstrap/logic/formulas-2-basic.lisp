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
(include-book "formulas-1")
(%interactive)



(%autoprove forcing-logic.termp-of-logic.=lhs
            (%enable default logic.fmtype logic.=lhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.termp-of-logic.=rhs
            (%enable default logic.fmtype logic.=rhs)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default forcing-logic.termp-of-logic.=lhs))

(%autoprove forcing-logic.formulap-of-logic.~arg
            (%enable default logic.fmtype logic.~arg)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default forcing-logic.termp-of-logic.=lhs
                      forcing-logic.termp-of-logic.=rhs))

(%autoprove forcing-logic.formulap-of-logic.vlhs
            (%enable default logic.fmtype logic.vlhs)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default
                      forcing-logic.termp-of-logic.=lhs
                      forcing-logic.termp-of-logic.=rhs
                      forcing-logic.formulap-of-logic.~arg))

(%autoprove forcing-logic.formulap-of-logic.vrhs
            (%enable default logic.fmtype logic.vrhs)
            (%restrict default logic.formulap (equal x 'x))
            (%disable default
                      forcing-logic.termp-of-logic.=lhs
                      forcing-logic.termp-of-logic.=rhs
                      forcing-logic.formulap-of-logic.~arg
                      forcing-logic.formulap-of-logic.vlhs))



(%autoprove forcing-logic.formulap-of-logic.pequal
            (%enable default logic.pequal)
            (%restrict default logic.formulap (equal x '(cons 'pequal* (cons a (cons b 'nil))))))

(%autoprove forcing-logic.formulap-of-logic.pnot
            (%enable default logic.pnot)
            (%restrict default logic.formulap (equal x '(cons 'pnot* (cons a 'nil)))))

(%autoprove forcing-logic.formulap-of-logic.por
            (%enable default logic.por)
            (%restrict default logic.formulap (equal x '(cons 'por* (cons a (cons b 'nil))))))

(%autoprove logic.fmtype-of-logic.pequal
            (%enable default logic.fmtype logic.pequal))

(%autoprove logic.fmtype-of-logic.pnot
            (%enable default logic.fmtype logic.pnot))

(%autoprove logic.fmtype-of-logic.por
            (%enable default logic.fmtype logic.por))

(%autoprove logic.=lhs-of-logic.pequal
            (%enable default logic.=lhs logic.pequal))

(%autoprove logic.=rhs-of-logic.pequal
            (%enable default logic.=rhs logic.pequal))

(%autoprove logic.~arg-of-logic.pnot
            (%enable default logic.~arg logic.pnot))

(%autoprove logic.vlhs-of-logic.por
            (%enable default logic.vlhs logic.por))

(%autoprove logic.vrhs-of-logic.por
            (%enable default logic.vrhs logic.por))

(%autoprove logic.=lhs-of-logic.pequal-free)

(%autoprove logic.=rhs-of-logic.pequal-free)

(%autoprove logic.fmtype-of-logic.pequal-free)



(%autoprove forcing-equal-of-logic.pequal-rewrite-two
            (%auto)
            (%enable default logic.fmtype logic.pequal logic.=lhs logic.=rhs)
            (%restrict default logic.formulap (equal x 'x))
            (%restrict default tuplep (or (equal n ''3) (equal n ''2) (equal n ''1)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-equal-of-logic.pequal-rewrite)



(%autoprove forcing-equal-of-logic.pnot-rewrite-two
            (%enable default logic.fmtype logic.pnot logic.~arg)
            (%restrict default logic.formulap (equal x 'x))
            (%restrict default tuplep (or (equal n ''2) (equal n ''1)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-equal-of-logic.pnot-rewrite)

(%autoprove forcing-equal-of-logic.por-rewrite-two
            (%enable default logic.fmtype logic.vlhs logic.vrhs logic.por)
            (%restrict default logic.formulap (equal x 'x))
            (%restrict default tuplep (or (equal n ''3) (equal n ''2) (equal n ''1)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove forcing-equal-of-logic.por-rewrite)




(%autoprove forcing-logic.pnot-of-logic.~arg)

(%autoprove forcing-logic.por-of-logic.vlhs-and-logic.vrhs)

(%autoprove forcing-logic.pequal-of-logic.=lhs-and-logic.=rhs)

(%autoprove equal-logic.pequal-logic.pequal-rewrite
            (%enable default logic.pequal))

(%autoprove equal-logic.pnot-logic.pnot-rewrite
            (%enable default logic.pnot))

(%autoprove equal-logic.por-logic.por-rewrite
            (%enable default logic.por))

