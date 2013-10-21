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
(include-book "contradictionp")
(include-book "eqtrace-compiler")
(%interactive)


(%deftheorem theorem-inequality-of-not-x-and-x)
(%deftheorem theorem-not-x-and-x-under-iff)
(%deftheorem rw.eqtrace-contradiction-lemma1)

(defsection rw.eqtrace-contradiction-lemma2
  (%autoadmit rw.eqtrace-contradiction-lemma2)
  (local (%enable default
                  rw.eqtrace-contradiction-lemma2
                  theorem-not-x-and-x-under-iff
                  theorem-symmetry-of-iff))
  (%autoprove rw.eqtrace-contradiction-lemma2-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.eqtrace-contradiction-lemma2)
  (%autoprove forcing-logic.conclusion-of-rw.eqtrace-contradiction-lemma2)
  (%autoprove forcing-logic.proofp-of-rw.eqtrace-contradiction-lemma2))

(%defderiv rw.eqtrace-contradiction-bldr-lemma3a :omit-okp t)
(%defderiv rw.eqtrace-contradiction-bldr-lemma3 :omit-okp t)


(defsection rw.eqtrace-contradiction-bldr
  (%autoadmit rw.eqtrace-contradiction-bldr)
  (local (%enable default
                  rw.eqtrace-contradictionp
                  rw.eqtrace-contradiction-bldr
                  rw.eqtrace-formula
                  rw.eqtrace-contradiction-lemma1
                  theorem-inequality-of-not-x-and-x))
  (%autoprove rw.eqtrace-contradiction-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.eqtrace-contradiction-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.eqtrace-contradiction-bldr)
  (%autoprove forcing-logic.proofp-of-rw.eqtrace-contradiction-bldr))

(%autoadmit rw.eqtrace-contradiction-bldr-okp)

(%autoadmit rw.eqtrace-contradiction-bldr-high)

(defsection rw.eqtrace-contradiction-bldr-okp
  (local (%enable default rw.eqtrace-contradiction-bldr-okp))
  (%autoprove booleanp-of-rw.eqtrace-contradiction-bldr-okp)
  (%autoprove rw.eqtrace-contradiction-bldr-okp-of-logic.appeal-identity)
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free
                   forcing-logic.term-list-atblp-of-logic.function-args))
  (%autoprove lemma-1-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
  (%autoprove lemma-2-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
  (%autoprove forcing-soundness-of-rw.eqtrace-contradiction-bldr-okp
              (%enable default
                       lemma-1-for-soundness-of-rw.eqtrace-contradiction-bldr-okp
                       lemma-2-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.eqtrace-contradiction-bldr (first (logic.extras x))
                                                                 (second (logic.extras x))))))))


