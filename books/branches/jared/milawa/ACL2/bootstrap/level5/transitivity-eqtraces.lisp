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

(defsection rw.trans1-eqtrace-okp
  (%autoadmit rw.trans1-eqtrace-okp)
  (%enable default rw.trans1-eqtrace-okp)
  (%autoprove booleanp-of-rw.trans1-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub1-when-rw.trans1-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub1-when-rw.trans1-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub2-when-rw.trans1-eqtrace-okp))

(defsection rw.trans1-eqtrace
  (%autoadmit rw.trans1-eqtrace)
  (local (%enable default rw.trans1-eqtrace))
  (%autoprove rw.eqtrace->method-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->iffp-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->lhs-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->rhs-of-rw.trans1-eqtrace)
  (%autoprove rw.eqtrace->subtraces-of-rw.trans1-eqtrace)
  (%autoprove lemma-for-forcing-rw.eqtracep-of-rw.trans1-eqtrace
              (%disable default forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs)
              (%use (%instance (%thm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs) (x x)))
              (%use (%instance (%thm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs) (x y))))
  (%autoprove forcing-rw.eqtracep-of-rw.trans1-eqtrace
              (%enable default lemma-for-forcing-rw.eqtracep-of-rw.trans1-eqtrace))
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.trans1-eqtrace)
  (%autoprove forcing-rw.trans1-eqtrace-okp-of-rw.trans1-eqtrace))

(defsection rw.trans2-eqtrace-okp
  (%autoadmit rw.trans2-eqtrace-okp)
  (local (%enable default rw.trans2-eqtrace-okp))
  (%autoprove booleanp-of-rw.trans2-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub1-when-rw.trans2-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub1-when-rw.trans2-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub2-when-rw.trans2-eqtrace-okp))

(defsection rw.trans2-eqtrace
  (%autoadmit rw.trans2-eqtrace)
  (local (%enable default rw.trans2-eqtrace))
  (%autoprove rw.eqtrace->method-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->iffp-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->lhs-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->rhs-of-rw.trans2-eqtrace)
  (%autoprove rw.eqtrace->subtraces-of-rw.trans2-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.trans2-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.trans2-eqtrace)
  (%autoprove forcing-rw.trans2-eqtrace-okp-of-rw.trans2-eqtrace
              (%enable default rw.trans2-eqtrace-okp)))

(defsection rw.trans3-eqtrace-okp
  (%autoadmit rw.trans3-eqtrace-okp)
  (local (%enable default rw.trans3-eqtrace-okp))
  (%autoprove booleanp-of-rw.trans3-eqtrace-okp)
  (%autoprove rw.eqtrace->rhs-of-sub1-when-rw.trans3-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub1-when-rw.trans3-eqtrace-okp)
  (%autoprove rw.eqtrace->lhs-of-sub2-when-rw.trans3-eqtrace-okp))

(defsection rw.trans3-eqtrace
  (%autoadmit rw.trans3-eqtrace)
  (local (%enable default rw.trans3-eqtrace))
  (%autoprove rw.eqtrace->method-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->iffp-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->lhs-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->rhs-of-rw.trans3-eqtrace)
  (%autoprove rw.eqtrace->subtraces-of-rw.trans3-eqtrace)
  (%autoprove forcing-rw.eqtracep-of-rw.trans3-eqtrace)
  (%autoprove forcing-rw.eqtrace-atblp-of-rw.trans3-eqtrace)
  (%autoprove forcing-rw.trans3-eqtrace-okp-of-rw.trans3-eqtrace
              (%enable default rw.trans3-eqtrace-okp)))

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/transitivity-eqtraces")