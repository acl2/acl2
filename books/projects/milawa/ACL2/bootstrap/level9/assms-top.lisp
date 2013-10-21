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
(include-book "assmsp")
;; (include-book "contradiction-bldr")
(%interactive)


(%autoprove forcing-rw.eqset-okp-when-empty-box
            (%enable default rw.eqset-okp rw.eqsetp rw.eqset->tail))

(%autoprove forcing-rw.eqset-list-okp-when-empty-box
            (%cdr-induction x))

(%autoprove forcing-rw.eqdatabase-okp-when-empty-box
            (%enable default
                     rw.eqdatabasep
                     rw.eqdatabase-okp
                     rw.eqdatabase->equalsets
                     rw.eqdatabase->contradiction))

(%autoprove rw.eqrow-list-lookup-when-not-consp
            (%restrict default rw.eqset-list-lookup (equal eqsets 'eqsets)))

(%autoprove forcing-rw.try-equalities-when-empty-box
            (%enable default rw.try-equiv-database))





(%autoadmit rw.try-assms)

(%autoprove forcing-logic.termp-of-rw.try-assms
            (%enable default rw.try-assms))

(%autoprove forcing-logic.term-atblp-of-rw.try-assms
            (%enable default rw.try-assms))

(%autoprove forcing-rw.try-assms-when-empty-hypbox
            (%enable default
                     rw.try-assms
                     rw.assmsp
                     rw.assms->eqdatabase
                     rw.assms->hypbox))



(defsection rw.try-assms-bldr

  (%autoadmit rw.try-assms-bldr)

  (local (%enable default
                  rw.try-assms
                  rw.try-assms-bldr
                  rw.eqtrace-formula))

  (%autoprove forcing-logic.appealp-of-rw.try-assms-bldr)

  (%autoprove forcing-logic.conclusion-of-rw.try-assms-bldr
              (%auto)
              ;; BOZO: ugh, this shouldn't be necessary
              (%enable default rw.assmsp rw.assms->eqdatabase rw.assms->hypbox))

  (%autoprove forcing-logic.proofp-of-rw.try-assms-bldr))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/top")