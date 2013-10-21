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
(include-book "formulas-2-atblp")
(include-book "formulas-2-basic")
(include-book "formulas-2-basic2")
(include-book "formulas-2-equal")
(include-book "formulas-2-list")
(%interactive)

(%autoprove forcing-logic.formula-atblp-of-logic.pequal
            (%restrict default logic.formula-atblp (equal x '(logic.pequal a b))))

(%autoprove forcing-logic.formula-atblp-of-logic.pnot
            (%restrict default logic.formula-atblp (equal x '(logic.pnot a)))
            (%disable default forcing-logic.formula-atblp-of-logic.~arg))

(%autoprove forcing-logic.formula-atblp-of-logic.por
            (%restrict default logic.formula-atblp (equal x '(logic.por a b)))
            (%disable default forcing-logic.formula-atblp-of-logic.vlhs forcing-logic.formula-atblp-of-logic.vrhs))


(%create-theory forcing-logic.formula-atblp-rules)
(%enable forcing-logic.formula-atblp-rules
         forcing-logic.term-atblp-of-logic.=lhs
         forcing-logic.term-atblp-of-logic.=rhs
         forcing-logic.formula-atblp-of-logic.~arg
         forcing-logic.formula-atblp-of-logic.vlhs
         forcing-logic.formula-atblp-of-logic.vrhs
         forcing-logic.formula-atblp-of-logic.pequal
         forcing-logic.formula-atblp-of-logic.pnot
         forcing-logic.formula-atblp-of-logic.por)


(encapsulate
 ()
 (local (%enable default forcing-logic.formula-atblp-rules))

 (%autoprove logic.formula-atblp-when-por-expensive
             (%restrict default logic.formula-atblp (equal x 'x)))
 (%autoprove logic.formula-atblp-when-pnot-expensive
             (%restrict default logic.formula-atblp (equal x 'x)))
 (%autoprove logic.formula-atblp-when-pequal-expensive
             (%restrict default logic.formula-atblp (equal x 'x)))
 (%autoprove logic.formula-atblp-of-logic.por-expensive
             (%restrict default logic.formula-atblp (equal x '(logic.por x y))))
 (%autoprove logic.formula-atblp-of-logic.pequal-expensive
             (%restrict default logic.formula-atblp (equal x '(logic.pequal x y))))
 (%autoprove logic.formula-atblp-of-logic.pnot-expensive
             (%restrict default logic.formula-atblp (equal x '(logic.pnot x)))))


(%create-theory backtracking-logic.formula-atblp-rules)
(%enable backtracking-logic.formula-atblp-rules
         logic.formula-atblp-when-por-expensive
         logic.formula-atblp-when-pnot-expensive
         logic.formula-atblp-when-pequal-expensive
         logic.formula-atblp-of-logic.por-expensive
         logic.formula-atblp-of-logic.pnot-expensive
         logic.formula-atblp-of-logic.pequal-expensive)

