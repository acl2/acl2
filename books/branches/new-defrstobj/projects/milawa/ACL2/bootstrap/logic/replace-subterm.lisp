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
(include-book "substitute-term")
(%interactive)


(%autoadmit logic.flag-replace-subterm)
(%autoadmit logic.replace-subterm)
(%autoadmit logic.replace-subterm-list)

(%autoprove definition-of-logic.replace-subterm
            (%restrict default logic.flag-replace-subterm (or (equal x 'x) (equal x 'old)))
            (%enable default logic.replace-subterm logic.replace-subterm-list)
            ;; Causes a rlimit loop
            (%disable default forcing-logic.function-of-logic.function-name-and-logic.function-args-free))

(%autoprove definition-of-logic.replace-subterm-list
            (%restrict default logic.flag-replace-subterm (equal x 'x))
            (%enable default logic.replace-subterm logic.replace-subterm-list))

(%autoprove logic.flag-replace-subterm-of-term-removal
            (%enable default logic.replace-subterm))

(%autoprove logic.flag-replace-subterm-of-list-removal
            (%enable default logic.replace-subterm-list))

(%autoprove logic.replace-subterm-list-when-not-consp
            (%restrict default definition-of-logic.replace-subterm-list (equal x 'x)))

(%autoprove logic.replace-subterm-list-of-cons
            (%restrict default definition-of-logic.replace-subterm-list (equal x '(cons a x))))

(%defprojection :list (logic.replace-subterm-list x old new)
                :element (logic.replace-subterm x old new))



(%autoprove lemma-for-forcing-logic.termp-of-logic.replace-subterm
            (%logic.term-induction flag x)
            (%auto)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove forcing-logic.termp-of-logic.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-logic.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.term-listp-of-logic.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.termp-of-logic.replace-subterm)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.term-atblp-of-logic.replace-subterm
            (%logic.term-induction flag x)
            (%auto)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-logic.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-logic.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.term-list-atblp-of-logic.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.term-atblp-of-logic.replace-subterm)
                             (flag 'list))))



(%autoprove lemma-for-forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable
            (%logic.term-induction flag x)
            (%auto)
            (%restrict default definition-of-logic.replace-subterm (equal x 'x)))

(%autoprove forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable
            (%use (%instance (%thm lemma-for-forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable)
                             (flag 'term))))

(%autoprove forcing-logic.substitute-of-logic.replace-subterm-list-with-fresh-variable
            (%use (%instance (%thm lemma-for-forcing-logic.substitute-of-logic.replace-subterm-with-fresh-variable)
                             (flag 'list))))




(%defprojection :list (logic.replace-subterm-list-list x old new)
                :element (logic.replace-subterm-list x old new))

(%autoprove forcing-logic.term-list-listp-of-logic.replace-subterm-list-list                (%cdr-induction x))
(%autoprove forcing-logic.term-list-list-atblp-of-logic.replace-subterm-list-list           (%cdr-induction x))
(%autoprove cons-listp-of-logic.replace-subterm-list-list                                   (%cdr-induction x))
(%autoprove forcing-logic.substitute-of-logic.replace-subterm-list-list-with-fresh-variable (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../logic/replace-subterm")

