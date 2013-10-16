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
(include-book "eqtrace-okp")
(%interactive)

(%autoprove lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)
(%autoprove lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
            (%enable default lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr))
(%autoprove lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)
(%autoprove lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)

(defsection rw.trans1-eqtrace-bldr
  (%autoadmit rw.trans1-eqtrace-bldr)
  (local (%enable default
                  rw.eqtrace-formula
                  rw.trans1-eqtrace-bldr
                  rw.trans1-eqtrace-okp
                  lemma-1-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                  lemma-2-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                  lemma-3-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr
                  lemma-4-for-forcing-logic.appealp-of-rw.trans1-eqtrace-bldr))

  ;; Originally I didn't have this, but later changes to the rewriter exposed some
  ;; kind of loop caused by this rule, which was horribly problematic.

  (local (%disable default RW.EQTRACE->RHS-OF-SUB1-WHEN-RW.TRANS1-EQTRACE-OKP))
  (%autoprove forcing-rw.trans1-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.trans1-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.trans1-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.trans1-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/trans1-eqtrace-bldr")



