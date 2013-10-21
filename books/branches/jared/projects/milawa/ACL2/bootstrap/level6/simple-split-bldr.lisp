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
(include-book "simple-split")
(include-book "aux-split-bldr")
(%interactive)


(%autoadmit clause.simple-split-bldr)

(encapsulate
 ()
 (local (%enable default
                 clause.simple-split
                 clause.simple-split-bldr))

 (%autoprove forcing-logic.appealp-of-clause.simple-split-bldr)
 (%autoprove forcing-logic.conclusion-of-clause.simple-split-bldr)
 (%autoprove forcing-logic.proofp-of-clause.simple-split-bldr))



(%autoadmit clause.simple-split-bldr-okp)
(%autoadmit clause.simple-split-bldr-high)
(local (%enable default clause.simple-split-bldr-okp))
(%autoprove booleanp-of-clause.simple-split-bldr-okp)
(%autoprove clause.simple-split-bldr-okp-of-logic.appeal-identity)
(%autoprove lemma-1-for-soundness-of-clause.simple-split-bldr-okp)
(%autoprove lemma-2-for-soundness-of-clause.simple-split-bldr-okp)
(%autoprove forcing-soundness-of-clause.simple-split-bldr-okp
            (%enable default
                     lemma-1-for-soundness-of-clause.simple-split-bldr-okp
                     lemma-2-for-soundness-of-clause.simple-split-bldr-okp)
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (clause.simple-split-bldr (logic.extras x)
                                                          (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                       axioms thms atbl))))))
