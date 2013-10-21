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


(%deflist logic.all-negationsp (x)
          (equal (logic.fmtype x) 'pnot*)
          :hintsmap ((logic.all-negationsp-of-remove-duplicates
                      (%cdr-induction x)
                      (%auto)
                      (%use (%instance (%thm equal-when-memberp-of-logic.all-negationsp)
                                       (a x1)
                                       (x x2))))
                     (logic.all-negationsp-of-subsetp-when-logic.all-negationsp
                      (%cdr-induction x)
                      (%auto)
                      (%use (%instance (%thm equal-when-memberp-of-logic.all-negationsp)
                                       (a x1)
                                       (x y))))))

(%autoprove logic.fmtype-of-car-when-logic.all-negationsp
            (%enable default equal-of-car-when-logic.all-negationsp))

(%autoprove logic.fmtype-when-memberp-of-logic.all-negationsp
            (%use (%instance (%thm equal-when-memberp-of-logic.all-negationsp))))

(%autoprove logic.fmtype-when-memberp-of-logic.all-negationsp-alt)



(%defprojection :list (logic.~args x)
                :element (logic.~arg x)
                :nil-preservingp t)


(%autoprove forcing-logic.formula-listp-of-logic.~args
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.~args
            (%cdr-induction x))

(%autoprove logic.~arg-of-car-when-all-equalp-of-logic.~args)

(defsection logic.negate-formulas

  (local (%disable default
                   forcing-logic.formulap-of-logic.pnot
                   aggressive-equal-of-logic.pnots
                   forcing-equal-of-logic.pnot-rewrite
                   forcing-equal-of-logic.pnot-rewrite-two))

  (%defprojection :list (logic.negate-formulas x)
                  :element (logic.pnot x)))

(%autoprove memberp-of-logic.pnot-in-logic.negate-formulas
            (%enable default memberp-of-logic.pnot-in-logic.negate-formulas-when-memberp)
            (%cdr-induction x))

(%autoprove logic.formula-listp-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove logic.formula-list-atblp-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove equal-of-logic.negate-formulas-and-logic.negate-formulas
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.~args-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.~args-of-logic.negate-formulas-free)

(%autoprove forcing-logic.all-negationsp-of-logic.negate-formulas
            (%cdr-induction x))

(%autoprove forcing-logic.all-negationsp-of-logic.negate-formulas-free)





(%autoadmit logic.smart-negate-formulas)

(%autoprove logic.smart-negate-formulas-when-not-consp (%restrict default logic.smart-negate-formulas (equal x 'x)))
(%autoprove logic.smart-negate-formulas-of-cons        (%restrict default logic.smart-negate-formulas (equal x '(cons a x))))

(%autoprove true-listp-of-logic.smart-negate-formulas  (%cdr-induction x))
(%autoprove logic.smart-negate-formulas-of-list-fix    (%cdr-induction x))
(%autoprove logic.smart-negate-formulas-of-app         (%cdr-induction x))
(%autoprove len-of-logic.smart-negate-formulas         (%cdr-induction x))
(%autoprove consp-of-logic.smart-negate-formulas       (%cdr-induction x))
(%autoprove logic.smart-negate-formulas-under-iff      (%cdr-induction x))
(%autoprove forcing-logic.formula-listp-of-logic.smart-negate-formulas      (%cdr-induction x))
(%autoprove forcing-logic.formula-list-atblp-of-logic.smart-negate-formulas (%cdr-induction x))

(%autoprove memberp-of-logic.pnot-in-logic.smart-negate-formulas
            (%cdr-induction x))

(%autoprove memberp-of-logic.pequal-in-logic.smart-negate-formulas
            (%cdr-induction x))

(%autoprove memberp-of-logic.~arg-in-logic.smart-negate-formulas
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../logic/negate-formulas")

