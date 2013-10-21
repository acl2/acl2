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
(include-book "utilities")
(%interactive)


(%autoadmit sort-symbols-insert)

(%autoprove sort-symbols-insert-when-not-consp
            (%restrict default sort-symbols-insert (equal x 'x)))

(%autoprove sort-symbols-insert-of-cons
            (%restrict default sort-symbols-insert (equal x '(cons b x))))

(%autoprove memberp-of-sort-symbols-insert
            (%cdr-induction x))

(%autoprove len-of-sort-symbols-insert
            (%cdr-induction x))

(%autoprove consp-of-sort-symbols-insert
            (%cdr-induction x))

(%autoprove car-of-sort-symbols-insert)

(%autoprove uniquep-of-sort-symbols-insert
            (%cdr-induction x))


(%autoadmit sort-symbols)

(%autoprove sort-symbols-when-not-consp
            (%restrict default sort-symbols (equal x 'x)))

(%autoprove sort-symbols-of-cons
            (%restrict default sort-symbols (equal x '(cons a x))))

(%autoprove memberp-of-sort-symbols
            (%cdr-induction x))

(%autoprove len-of-sort-symbols
            (%cdr-induction x))

(%autoprove disjointp-of-sort-symbols
            (%cdr-induction x))

(%autoprove uniquep-of-sort-symbols
            (%cdr-induction x))


(%autoadmit symbol-list-orderedp)

(%autoprove symbol-list-orderedp-when-not-consp
            (%restrict default symbol-list-orderedp (equal x 'x)))

(%autoprove symbol-list-orderedp-when-not-consp-of-cdr
            (%restrict default symbol-list-orderedp (equal x 'x)))

(%autoprove symbol-list-orderedp-of-cons
            (%restrict default symbol-list-orderedp (equal x '(cons a x))))

(%autoprove symbol-list-orderedp-of-sort-symbols-insert
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../utilities/sort-symbols")