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
(include-book "terms")
(%interactive)



(%autoadmit logic.formulap)

(%autoadmit logic.pequal)
(%autoadmit logic.pnot)
(%autoadmit logic.por)

(%noexec logic.pequal)
(%noexec logic.pnot)
(%noexec logic.por)

(%autoadmit logic.fmtype)
(%autoadmit logic.=lhs)
(%autoadmit logic.=rhs)
(%autoadmit logic.~arg)
(%autoadmit logic.vlhs)
(%autoadmit logic.vrhs)


(defmacro %logic.raw-formulap-induction (x)
  `(%induct (rank ,x)
            ((equal (first ,x) 'pequal*)
             nil)
            ((equal (first ,x) 'pnot*)
             (((,x (second ,x)))))
            ((equal (first ,x) 'por*)
             (((,x (second ,x)))
              ((,x (third ,x)))))
            ((and (not (equal (first ,x) 'pequal*))
                  (not (equal (first ,x) 'pnot*))
                  (not (equal (first ,x) 'por*)))
             nil)))

(%autoprove booleanp-of-logic.formulap
            (%logic.raw-formulap-induction x)
            (%restrict default logic.formulap (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove logic.formulap-when-not-consp
            (%restrict default logic.formulap (equal x 'x))
            (%auto :strategy (cleanup split crewrite)))



(%autoprove lemma-1-for-logic.formulap-when-logic.termp
            (%restrict default logic.formulap (equal x 'x)))

(%autoprove lemma-2-for-logic.formulap-when-logic.termp
            (%restrict default definition-of-logic.termp (equal x 'x))
            (%enable default logic.constantp))

(%autoprove logic.formulap-when-logic.termp
            (%use (%instance (%thm lemma-1-for-logic.formulap-when-logic.termp)))
            (%use (%instance (%thm lemma-2-for-logic.formulap-when-logic.termp))))

(%autoprove logic.termp-when-logic.formulap)
