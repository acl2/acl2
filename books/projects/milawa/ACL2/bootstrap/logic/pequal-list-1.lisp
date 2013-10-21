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

(%autoadmit logic.pequal-list)

(%autoprove logic.pequal-list-when-not-consp-one
            (%restrict default logic.pequal-list (equal x 'x)))

(%autoprove logic.pequal-list-when-not-consp-two
            (%restrict default logic.pequal-list (equal x 'x)))

(%autoprove logic.pequal-list-of-cons-and-cons
            (%restrict default logic.pequal-list (equal x '(cons a x))))

(%autoprove logic.pequal-list-under-iff)

(%autoprove logic.pequal-list-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove logic.pequal-list-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove true-listp-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formulap-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formula-atblp-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove consp-of-logic.pequal-list)

(%autoprove car-of-logic.pequal-list
            ;; BOZO yuck, new car-cdr-elim code goes berserk here for some reason.
            ;; We just enable the function instead of dealing with it.
            (%restrict default logic.pequal-list (equal x 'x)))

(%autoprove cdr-of-logic.pequal-list)

(%autoprove len-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove logic.pequal-list-of-cons-and-repeat-plus-one)




(%deflist logic.all-atomicp (x)
          (equal (logic.fmtype x) 'pequal*)
          :hintsmap
          ;; These nasty hints are needed becuase the "equal" above ruins the
          ;; canonicalization we expect.
          ((logic.all-atomicp-of-remove-duplicates
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-atomicp)
                             (a x1)
                             (x x2))))
           (logic.all-atomicp-of-subsetp-when-logic.all-atomicp
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-atomicp)
                             (a x1)
                             (x y))))))

(%autoprove logic.fmtype-of-car-when-logic.all-atomicp
            (%enable default equal-of-car-when-logic.all-atomicp))

(%autoprove logic.fmtype-when-memberp-of-logic.all-atomicp
            (%use (%instance (%thm equal-when-memberp-of-logic.all-atomicp))))

(%autoprove logic.fmtype-when-memberp-of-logic.all-atomicp-alt)

(%autoprove forcing-logic.all-atomicp-of-logic.pequal-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.all-atomicp-of-logic.pequal-list-free)

(%autoprove logic.fmtype-of-nth-when-logic.all-atomicp)

