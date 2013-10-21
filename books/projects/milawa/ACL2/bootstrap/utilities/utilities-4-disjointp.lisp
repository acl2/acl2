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



(%autoadmit disjointp)


(%autoprove disjointp-when-not-consp-one
            (%restrict default disjointp (equal x 'x)))

(%autoprove disjointp-of-cons-one
            (%restrict default disjointp (equal x '(cons a x))))

(%autoprove booleanp-of-disjointp
            (%cdr-induction x))

(%autoprove disjointp-when-not-consp-two
            (%cdr-induction x))

(%autoprove disjointp-of-cons-two
            (%cdr-induction x))

(%autoprove symmetry-of-disjointp
            (%cdr-induction x))

(%autoprove disjointp-of-list-fix-one
            (%cdr-induction x))

(%autoprove disjointp-of-list-fix-two
            (%disable default symmetry-of-disjointp)
            (%use (%instance (%thm symmetry-of-disjointp) (x x) (y (list-fix y))))
            (%use (%instance (%thm symmetry-of-disjointp) (x y) (y x))))

(%autoprove disjointp-of-singleton-one)
(%autoprove disjointp-of-singleton-two)

(%autoprove disjointp-when-common-member-one
            (%cdr-induction x))

(%autoprove disjointp-when-common-member-two)

(%autoprove disjointp-of-app-two
            (%cdr-induction x))

(%autoprove disjointp-of-app-one)

(%autoprove disjointp-of-rev-two
            (%cdr-induction x))

(%autoprove disjointp-of-rev-one)

(%autoprove disjointp-when-subsetp-of-disjointp-one
            (%cdr-induction x))

(%autoprove disjointp-when-subsetp-of-disjointp-two)

(%autoprove disjointp-when-subsetp-of-disjointp-three
            (%cdr-induction x))

(%autoprove disjointp-when-subsetp-of-disjointp-four)

(%autoprove disjointp-when-subsetp-of-other-one
            (%cdr-induction x))

(%autoprove disjointp-when-subsetp-of-other-two
            (%cdr-induction y))

(%autoprove memberp-when-disjointp-one
            (%cdr-induction x))

(%autoprove memberp-when-disjointp-two)
