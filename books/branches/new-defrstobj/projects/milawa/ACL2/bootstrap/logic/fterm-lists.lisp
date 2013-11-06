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
(include-book "terms")
(%interactive)


(%deflist logic.all-functionsp (x)
          (logic.functionp x))

(%defprojection :list (logic.strip-function-names x)
                :element (logic.function-name x)
                :nil-preservingp t)

(%autoprove forcing-logic.function-symbol-listp-of-logic.strip-function-names
            (%cdr-induction x))


(%defprojection :list (logic.strip-function-args x)
                :element (logic.function-args x)
                :nil-preservingp t)

(%autoprove forcing-logic.term-list-listp-of-logic.strip-function-args
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-logic.strip-function-args
            (%cdr-induction x))

(%autoprove forcing-true-list-listp-of-logic.strip-function-args
            (%cdr-induction x))

(%autoprove logic.term-listp-of-strip-firsts-when-all-lens-2
            (%cdr-induction x))

(%autoprove logic.term-listp-of-strip-seconds-when-all-lens-2
            (%cdr-induction x))

(%autoprove logic.term-list-atblp-of-strip-firsts-when-all-lens-2
            (%cdr-induction x))

(%autoprove logic.term-list-atblp-of-strip-seconds-when-all-lens-2
            (%cdr-induction x))




(%defprojection
 ;; Interestingly this doesn't need the hint we used in ACL2, which was to disable
 ;; the rule equal-of-logic.function-rewrite.
 :list (logic.function-list name x)
 :element (logic.function name x))

(%autoprove forcing-logic.term-listp-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.all-functionsp-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.strip-function-names-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.strip-function-args-of-logic.function-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-list-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.term-list-atblp-list-of-list2-list
            (%cdr-cdr-induction x y))

(%ensure-exactly-these-rules-are-missing "../../logic/fterm-lists")

