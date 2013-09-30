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
(include-book "terms-2")
(%interactive)

(%autoprove logic.term-list-vars-when-not-consp
            (%restrict default definition-of-logic.term-list-vars (equal x 'x)))

(%autoprove logic.term-list-vars-of-cons
            (%restrict default definition-of-logic.term-list-vars (equal x '(cons a x))))

(%autoprove true-listp-of-logic.term-list-vars
            (%cdr-induction x))

(%autoprove true-listp-of-logic.term-vars
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove logic.term-vars-when-variable
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove logic.term-vars-when-constant
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove logic.term-vars-when-bad
            (%restrict default definition-of-logic.term-vars (equal x 'x)))

(%autoprove subsetp-of-logic.term-list-vars-of-cdr-with-logic.term-list-vars)

(%autoprove subsetp-of-logic.term-vars-of-car-with-logic.term-list-vars)

(%autoprove logic.term-list-vars-when-logic.variable-listp
            (%cdr-induction x))

(encapsulate
 ()
 (%autoprove lemma-for-subsetp-of-logic.term-list-vars-and-remove-duplicates
             (%cdr-induction x))

 (%autoprove subsetp-of-logic.term-list-vars-and-remove-duplicates
             (%cdr-induction x)
             (%enable default lemma-for-subsetp-of-logic.term-list-vars-and-remove-duplicates)))

(%autoprove subsetp-of-logic.term-list-vars-and-remove-duplicates-two
            (%cdr-induction x))

