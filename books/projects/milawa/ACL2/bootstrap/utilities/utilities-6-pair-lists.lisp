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
(include-book "utilities-5")
(%interactive)



(%autoadmit pair-lists)

(%autoprove pair-lists-when-not-consp
            (%restrict default pair-lists (equal x 'x)))

(%autoprove pair-lists-of-cons-one
            (%restrict default pair-lists (equal x '(cons a x))))

(%autoprove pair-lists-of-cons-two
            (%restrict default pair-lists (equal y '(cons a y))))

(%autoprove true-listp-of-pair-lists
            (%autoinduct pair-lists))

(%autoprove pair-lists-of-list-fix-one
            (%autoinduct pair-lists))

(%autoprove pair-lists-of-list-fix-two
            (%autoinduct pair-lists))

(%autoprove domain-of-pair-lists
            (%autoinduct pair-lists))

(%autoprove range-of-pair-lists
            (%autoinduct pair-lists domain range))

(%autoprove lookup-of-pair-lists
            (%autoinduct pair-lists keys vals))

(%autoprove lookup-of-pair-lists-of-rev)

(%autoprove lookup-of-nth-in-pair-lists-when-unique-keys
            (%induct (rank x)
                     ((or (not (consp x))
                          (not (consp y)))
                      nil)
                     ((zp n)
                      nil)
                     ((and (consp x)
                           (consp y)
                           (not (zp n)))
                      (((n (- n 1))
                        (x (cdr x))
                        (y (cdr y))))))
            ;; somehow no urewrite saves a lot of conses
            (%auto :strategy (cleanup split crewrite)))



(%autoadmit fast-pair-lists$)

(%autoprove fast-pair-lists$-when-not-consp
            (%restrict default fast-pair-lists$ (equal x 'x)))

(%autoprove fast-pair-lists$-of-cons
            (%restrict default fast-pair-lists$ (equal x '(cons a x))))

(%autoprove forcing-fast-pair-lists$-removal
            (%autoinduct fast-pair-lists$)
            (%enable default fast-pair-lists$-when-not-consp fast-pair-lists$-of-cons))
