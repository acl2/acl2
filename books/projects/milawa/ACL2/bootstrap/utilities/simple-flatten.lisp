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
(include-book "list-list-fix")
(%interactive)


(%autoadmit slow-simple-flatten)

(%autoprove slow-simple-flatten-when-not-consp
            (%restrict default slow-simple-flatten (equal x 'x)))

(%autoprove slow-simple-flatten-of-cons
            (%restrict default slow-simple-flatten (equal x '(cons a x))))

(%autoadmit fast-simple-flatten$)

(%autoadmit simple-flatten)

(%autoprove lemma-for-definition-of-simple-flatten
            (%autoinduct fast-simple-flatten$)
            (%restrict default fast-simple-flatten$ (equal x 'x)))

(%autoprove definition-of-simple-flatten
            (%enable default simple-flatten lemma-for-definition-of-simple-flatten))

(%autoprove simple-flatten-when-not-consp
            (%restrict default definition-of-simple-flatten (equal x 'x)))

(%autoprove simple-flatten-of-cons
            (%restrict default definition-of-simple-flatten (equal x '(cons a x))))

(%autoprove true-listp-of-simple-flatten
            (%cdr-induction x))

(%autoprove simple-flatten-of-list-fix
            (%cdr-induction x))

(%autoprove simple-flatten-of-app
            (%cdr-induction x))

(%autoprove simple-flatten-of-list-list-fix
            (%cdr-induction x))

(%autoprove forcing-fast-simple-flatten$-removal
            (%autoinduct fast-simple-flatten$)
            (%restrict default fast-simple-flatten$ (equal x 'x)))


(%autoadmit fast-simple-flatten-of-domain$)

(%autoprove fast-simple-flatten-of-domain$-removal
            (%autoinduct fast-simple-flatten-of-domain$)
            (%restrict default fast-simple-flatten-of-domain$ (equal x 'x)))

(%autoadmit fast-simple-flatten-of-range$)

(%autoprove fast-simple-flatten-of-range$-removal
            (%autoinduct fast-simple-flatten-of-range$)
            (%restrict default fast-simple-flatten-of-range$ (equal x 'x)))

(%ensure-exactly-these-rules-are-missing "../../utilities/simple-flatten")