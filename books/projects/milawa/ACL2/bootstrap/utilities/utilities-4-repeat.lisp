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


(%autoadmit repeat)

(%autoprove repeat-of-zero
            (%restrict default repeat (equal n ''0)))

(%autoprove repeat-of-one
            (%restrict default repeat (equal n ''1)))

(%autoprove consp-of-repeat
            (%restrict default repeat (equal n 'n)))

(%autoprove repeat-under-iff
            (%restrict default repeat (equal n 'n)))

(%autoprove car-of-repeat
            (%restrict default repeat (equal n 'n)))

(%autoprove cdr-of-repeat
            (%restrict default repeat (equal n 'n)))

(%autoprove repeat-of-nfix
            (%dec-induction n)
            (%restrict default repeat (equal n '(nfix n))))

(%autoprove len-of-repeat
            (%dec-induction n)
            (%restrict default repeat (equal n 'n)))

(%autoprove true-listp-of-repeat
            (%dec-induction n)
            (%restrict default repeat (equal n 'n)))

(%autoprove memberp-of-repeat
            (%dec-induction n)
            (%split)
            ;; Could use (%restrict ...) (%auto) for 187m conses
            ;; Could use (%auto) (%restrict ...) (%auto) for 47m conses
            ;; Or leave these nasty hints for 36m conses
            (%cleanup)
            (%crewrite default)
            (%split)
            (%cleanup)
            (%restrict default repeat (or (equal n 'n) (equal n ''1))))

(%autoprove app-of-repeat
            (%dec-induction n1)
            (%split)
            (%restrict default repeat (or (equal n 'n1) (equal n ''0))))

(%autoprove lemma-for-rev-of-repeat
            (%dec-induction n)
            (%restrict default repeat (equal n 'n)))

(%autoprove rev-of-repeat
            (%dec-induction n)
            (%enable default lemma-for-rev-of-repeat)
            (%restrict default repeat (equal n 'n)))

