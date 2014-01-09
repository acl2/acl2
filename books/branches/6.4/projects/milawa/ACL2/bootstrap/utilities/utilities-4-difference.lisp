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
(include-book "utilities-3")
(%interactive)


(%autoadmit difference)

(%autoprove difference-when-not-consp
            (%restrict default difference (equal x 'x)))

(%autoprove difference-of-cons
            (%restrict default difference (equal x '(cons a x))))

(%autoprove true-listp-of-difference
            (%cdr-induction x))

(%autoprove difference-of-list-fix-one
            (%cdr-induction x))

(%autoprove difference-of-list-fix-two
            (%cdr-induction x))

(%autoprove difference-of-app-one
            (%cdr-induction x))

(%autoprove difference-of-difference
            (%cdr-induction x))

(%autoprove rev-of-difference
            (%cdr-induction x))

(%autoprove difference-of-rev)

(%autoprove difference-of-rev-two
            (%cdr-induction x))

(%autoprove memberp-of-difference
            (%cdr-induction x))

(%autoprove difference-when-subsetp
            (%cdr-induction x))

(%autoprove subsetp-with-app-of-difference-onto-takeaway
            (%cdr-induction x))



(%autoadmit fast-difference$)

(%autoprove fast-difference$-when-not-consp
            (%restrict default fast-difference$ (equal x 'x)))

(%autoprove fast-difference$-of-cons
            (%restrict default fast-difference$ (equal x '(cons a x))))

(%autoprove forcing-fast-difference$-removal
            (%enable default fast-difference$-when-not-consp)
            (%enable default fast-difference$-of-cons)
            (%autoinduct fast-difference$))

