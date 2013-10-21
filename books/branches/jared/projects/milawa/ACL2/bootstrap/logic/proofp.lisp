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
(include-book "proofp-3-provablep")
(include-book "proofp-3-subproofs")
(%interactive)



(%autoprove lemma-main-for-forcing-logic.provablep-when-logic.subproofs-provable
            (%restrict default definition-of-logic.proofp
                       (equal x '(logic.appeal (logic.method x)
                                               (logic.conclusion x)
                                               (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                            axioms thms atbl)
                                               (logic.extras x))))
            (%enable default lemma-appeal-step-for-forcing-logic.provablep-when-logic.subproofs-provable))


(%autoprove forcing-logic.provablep-when-logic.subproofs-provable
            (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                             (x (logic.appeal (logic.method x)
                                              (logic.conclusion x)
                                              (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                           axioms thms atbl)
                                              (logic.extras x)))))
            (%enable default lemma-main-for-forcing-logic.provablep-when-logic.subproofs-provable))

(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-of-cdr-when-logic.provable-listp)

(%autoprove logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest)


(%ensure-exactly-these-rules-are-missing "../../logic/proofp"
                                         ;; We don't have skip-okp here.
                                         logic.formula-atblp-of-logic.conclusion-when-logic.skip-okp
                                         booleanp-of-logic.skip-okp)

