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

(%autoprove logic.pequal-under-iff
            (%enable default logic.pequal))

(%autoprove logic.pnot-under-iff
            (%enable default logic.pnot))

(%autoprove logic.por-under-iff
            (%enable default logic.por))

(%autoprove forcing-logic.=lhs-under-iff
            (%enable default logic.fmtype logic.=lhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.=rhs-under-iff
            (%enable default logic.fmtype logic.=rhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.~arg-under-iff
            (%enable default logic.fmtype logic.~arg)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.vlhs-under-iff
            (%enable default logic.fmtype logic.vlhs)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove forcing-logic.vrhs-under-iff
            (%enable default logic.fmtype logic.vrhs)
            (%restrict default logic.formulap (equal x 'x)))


(%autoprove logic.formulap-of-logic.pequal-of-nil-one
            (%enable default logic.pequal)
            (%restrict default logic.formulap (equal x '(cons 'pequal* (cons 'nil (cons x 'nil))))))

(%autoprove logic.formulap-of-logic.pequal-of-nil-two
            (%enable default logic.pequal)
            (%restrict default logic.formulap (equal x '(cons 'pequal* (cons x '(nil))))))

(%autoprove logic.formulap-of-logic.pnot-of-logic.pequal-of-nil-one
            (%enable default logic.pnot)
            (%restrict default logic.formulap (equal x '(CONS 'PNOT* (CONS (LOGIC.PEQUAL 'NIL X) 'NIL)))))

(%autoprove logic.formulap-of-logic.pnot-of-logic.pequal-of-nil-two
            (%enable default logic.pnot)
            (%restrict default logic.formulap (equal x '(CONS 'PNOT* (CONS (LOGIC.PEQUAL X 'NIL) 'NIL)))))

(%autoprove logic.formulap-of-logic.por-expensive
            (%restrict default logic.formulap (equal x '(cons 'por* (cons x (cons y 'nil)))))
            (%enable default logic.por))
