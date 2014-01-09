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


(%autoprove rank-of-logic.=lhs-strong
            (%enable default logic.=lhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.=rhs-strong
            (%enable default logic.=rhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.~arg-strong
            (%enable default logic.~arg logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.vlhs-strong
            (%enable default logic.vlhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.vrhs-strong
            (%enable default logic.vrhs logic.fmtype)
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove rank-of-logic.pnot
            (%enable default logic.pnot))

(%autoprove rank-of-logic.pequal
            (%enable default logic.pequal))

(%autoprove rank-of-logic.por
            (%enable default logic.por))


(%autoadmit logic.formula-atblp)

(defmacro %logic.formulap-induction (x)
  `(%induct (rank ,x)
            ((equal (logic.fmtype ,x) 'pequal*)
             nil)
            ((equal (logic.fmtype ,x) 'pnot*)
             (((,x (logic.~arg ,x)))))
            ((equal (logic.fmtype ,x) 'por*)
             (((,x (logic.vlhs ,x)))
              ((,x (logic.vrhs ,x)))))
            ((and (not (equal (logic.fmtype ,x) 'pequal*))
                  (not (equal (logic.fmtype ,x) 'pnot*))
                  (not (equal (logic.fmtype ,x) 'por*)))
             nil)))

(%autoprove booleanp-of-logic.formula-atblp
            (%logic.formulap-induction x)
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove logic.formula-atblp-when-not-consp
            (%restrict default logic.formula-atblp (equal x 'x))
            (%enable default logic.fmtype))

(%autoprove forcing-logic.term-atblp-of-logic.=lhs
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-logic.=rhs
            (%restrict default logic.formula-atblp (equal x 'x))
            (%disable default forcing-logic.term-atblp-of-logic.=lhs))

(%autoprove forcing-logic.formula-atblp-of-logic.~arg
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove forcing-logic.formula-atblp-of-logic.vlhs
            (%restrict default logic.formula-atblp (equal x 'x)))

(%autoprove forcing-logic.formula-atblp-of-logic.vrhs
            (%restrict default logic.formula-atblp (equal x 'x))
            (%disable default forcing-logic.formula-atblp-of-logic.vlhs))

(%autoprove logic.formulap-when-malformed-cheap
            ;; BOZO I don't like where this is located; try moving it up in formulas.lisp and
            ;; move it to one of the basic files maybe.
            (%restrict default logic.formulap (equal x 'x))
            (%enable default logic.fmtype))

(%autoprove logic.formula-atblp-when-malformed-cheap
            (%restrict default logic.formula-atblp (equal x 'x)))

