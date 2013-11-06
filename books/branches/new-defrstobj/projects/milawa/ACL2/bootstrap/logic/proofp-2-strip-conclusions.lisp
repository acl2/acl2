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
(include-book "proofp-1")
(%interactive)


(%defprojection :list (logic.strip-conclusions x)
                :element (logic.conclusion x)
                :nil-preservingp t)

(%autoprove second-of-logic.strip-conclusions)

(%autoprove forcing-logic.formula-listp-of-logic.strip-conclusions
            (%cdr-induction x))


(%autoprove logic.fmtype-of-logic.conclusion-of-nth-when-logic.all-disjunctionsp)

(%autoprove logic.fmtype-of-logic.conclusion-of-nth-when-logic.all-atomicp)

(%autoprove logic.vlhs-of-logic.conclusion-of-car-when-all-equalp)


(%autoprove logic.vlhs-of-logic.conclusion-of-nth-when-all-equalp-of-logic.vlhses
            (%autoinduct nth)
            (%restrict default nth (equal n 'n)))

(%autoprove logic.fmtype-of-logic.vrhs-of-logic.conclusion-of-nth-when-logic.all-disjunctionsp-of-logic.all-atomicp)

(%autoprove logic.formula-atblp-of-logic.conclusion-of-car)
(%autoprove logic.formula-atblp-of-logic.conclusion-of-second)
(%autoprove logic.formula-atblp-of-logic.conclusion-of-third)


(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)

(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-when-len-2)
