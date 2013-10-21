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

(%defderiv rw.primary-eqtrace-nhyp-bldr-lemma-1 :omit-okp t)
(%defderiv rw.primary-eqtrace-nhyp-bldr-lemma-2 :omit-okp t)

(defsection rw.primary-eqtrace-nhyp-bldr
  (%autoadmit rw.primary-eqtrace-nhyp-bldr)
  (local (%disable default
                   forcing-equal-of-logic.pequal-rewrite-two
                   forcing-equal-of-logic.pequal-rewrite
                   forcing-equal-of-logic.por-rewrite-two
                   forcing-equal-of-logic.por-rewrite
                   forcing-equal-of-logic.pnot-rewrite-two
                   forcing-equal-of-logic.pnot-rewrite))
  (local (%enable default
                  rw.primary-eqtrace
                  rw.primary-eqtrace-nhyp-bldr
                  theorem-not-when-nil
                  logic.term-formula))
  (%autoprove rw.primary-eqtrace-nhyp-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.primary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.primary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.proofp-of-rw.primary-eqtrace-nhyp-bldr))

(defsection rw.primary-eqtrace-bldr
  (%autoadmit rw.primary-eqtrace-bldr)
  (local (%enable default
                  rw.primary-eqtrace-bldr
                  rw.primary-eqtrace-okp
                  rw.hypbox-formula
                  rw.eqtrace-formula))
  (%autoprove rw.primary-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.primary-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.primary-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.primary-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/primary-eqtrace-bldr"

                                         BOOLEANP-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP
                                         RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP-OF-LOGIC.APPEAL-IDENTITY
                                         LEMMA-1-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP
                                         LEMMA-2-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP
                                         FORCING-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-1-OKP

                                         BOOLEANP-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP
                                         RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP-OF-LOGIC.APPEAL-IDENTITY
                                         LEMMA-1-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP
                                         LEMMA-2-FOR-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP
                                         FORCING-SOUNDNESS-OF-RW.PRIMARY-EQTRACE-NHYP-BLDR-LEMMA-2-OKP)
