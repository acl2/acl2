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

(%defderiv rw.direct-iff-eqtrace-nhyp-bldr-lemma-1 :omit-okp t)
(%defderiv rw.direct-iff-eqtrace-nhyp-bldr-lemma-2 :omit-okp t)

(defsection rw.direct-iff-eqtrace-nhyp-bldr
  (%autoadmit rw.direct-iff-eqtrace-nhyp-bldr)
  (local (%enable default
                  rw.direct-iff-eqtrace
                  rw.direct-iff-eqtrace-nhyp-bldr
                  theorem-not-when-nil
                  logic.term-formula))
  (local (%enable default
                  forcing-equal-of-logic.pequal-rewrite-two
                  forcing-equal-of-logic.pequal-rewrite
                  forcing-equal-of-logic.por-rewrite-two
                  forcing-equal-of-logic.por-rewrite
                  forcing-equal-of-logic.pnot-rewrite-two
                  forcing-equal-of-logic.pnot-rewrite))
  (%autoprove rw.direct-iff-eqtrace-nhyp-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.direct-iff-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.direct-iff-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.proofp-of-rw.direct-iff-eqtrace-nhyp-bldr))

(defsection rw.direct-iff-eqtrace-bldr
  (%autoadmit rw.direct-iff-eqtrace-bldr)
  (local (%enable default
                  rw.direct-iff-eqtrace-bldr
                  rw.direct-iff-eqtrace-okp
                  rw.hypbox-formula
                  rw.eqtrace-formula))
  (%autoprove rw.direct-iff-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.direct-iff-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.direct-iff-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.direct-iff-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/direct-iff-eqtrace-bldr"
                                         booleanp-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp-of-logic.appeal-identity
                                         lemma-1-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         lemma-2-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         forcing-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-2-okp
                                         booleanp-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp
                                         rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp-of-logic.appeal-identity
                                         lemma-1-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp
                                         lemma-2-for-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp
                                         forcing-soundness-of-rw.direct-iff-eqtrace-nhyp-bldr-lemma-1-okp)

