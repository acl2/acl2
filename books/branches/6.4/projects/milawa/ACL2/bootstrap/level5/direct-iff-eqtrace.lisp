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
(include-book "eqtracep")
(%interactive)

(defsection rw.direct-iff-eqtrace
  (%autoadmit rw.direct-iff-eqtrace)
  (local (%enable default rw.direct-iff-eqtrace))
  (%autoprove forcing-rw.eqtrace->method-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtrace->iffp-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtrace->subtraces-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.direct-iff-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.direct-iff-eqtrace)
  (%autoprove rw.direct-iff-eqtrace-normalize-okp-1)
  (%autoprove rw.direct-iff-eqtrace-normalize-okp-2)
  (%autoprove rw.direct-iff-eqtrace-normalize-okp-3))


(defsection rw.find-nhyp-for-direct-iff-eqtracep
  (%autoadmit rw.find-nhyp-for-direct-iff-eqtracep)
  (local (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps 'nhyps)))
  (%autoprove rw.find-nhyp-for-direct-iff-eqtracep-of-nil
              (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps ''nil)))
  (%autoprove forcing-logic.termp-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-logic.term-atblp-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-memberp-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps))
  (%autoprove forcing-rw.direct-iff-eqtrace-of-rw.find-nhyp-for-direct-iff-eqtracep
              (%cdr-induction nhyps)))

(defsection rw.direct-iff-eqtrace-okp
  (%autoadmit rw.direct-iff-eqtrace-okp)
  (local (%enable default rw.direct-iff-eqtrace-okp))
  (%autoprove booleanp-of-rw.direct-iff-eqtrace-okp)
  (%autoprove lemma-for-forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace
              (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps 'nhyps))
              (%cdr-induction nhyps))
  (%autoprove forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace
              (%enable default lemma-for-forcing-rw.direct-iff-eqtrace-okp-rw.direct-iff-eqtrace)
              (%disable default rw.direct-iff-eqtrace-normalize-okp-1)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/direct-iff-eqtrace")

