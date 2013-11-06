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

(defsection rw.secondary-eqtrace-nhyp-bldr
  (%autoadmit rw.secondary-eqtrace-nhyp-bldr)
  (local (%enable default
                  rw.secondary-eqtrace
                  rw.secondary-eqtrace-nhyp-bldr
                  logic.term-formula))
  (local (%enable default
                  forcing-equal-of-logic.pequal-rewrite-two
                  forcing-equal-of-logic.pequal-rewrite
                  forcing-equal-of-logic.por-rewrite-two
                  forcing-equal-of-logic.por-rewrite
                  forcing-equal-of-logic.pnot-rewrite-two
                  forcing-equal-of-logic.pnot-rewrite))
  (%autoprove rw.secondary-eqtrace-nhyp-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.secondary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.secondary-eqtrace-nhyp-bldr)
  (%autoprove forcing-logic.proofp-of-rw.secondary-eqtrace-nhyp-bldr))

(defsection rw.secondary-eqtrace-bldr
  (%autoadmit rw.secondary-eqtrace-bldr)
  (local (%enable default
                  rw.secondary-eqtrace-bldr
                  rw.secondary-eqtrace-okp
                  rw.hypbox-formula
                  rw.eqtrace-formula))
  (%autoprove rw.secondary-eqtrace-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-rw.secondary-eqtrace-bldr)
  (%autoprove forcing-logic.conclusion-of-rw.secondary-eqtrace-bldr)
  (%autoprove forcing-logic.proofp-of-rw.secondary-eqtrace-bldr))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/secondary-eqtrace-bldr")

