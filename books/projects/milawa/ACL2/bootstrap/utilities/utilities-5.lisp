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
(include-book "utilities-5-prefixp")
(include-book "utilities-5-firstn")
(include-book "utilities-5-restn")
(include-book "utilities-5-first-index")
(include-book "utilities-5-mapp")
(%interactive)



(%autoprove nth-of-first-index-of-domain-and-range
            (%cdr-induction x)
            (%restrict default firstn (equal n 'n)))

(%autoprove prefixp-of-firstn
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove prefixp-of-firstn-unusual
            (%autoinduct firstn)
            (%restrict default firstn (equal n 'n)))

(%autoprove app-of-firstn-and-restn
            (%autoinduct restn)
            (%restrict default firstn (equal n 'n))
            (%restrict default restn (equal n 'n)))

(%autoprove lemma-for-equal-of-app-with-firstn-and-restn)

(%autoprove lemma-2-for-equal-of-app-with-firstn-and-restn)

(%autoprove lemma-3-for-equal-of-app-with-firstn-and-restn)

(%autoprove lemma-4-for-equal-of-app-with-firstn-and-restn
            (%enable default lemma-3-for-equal-of-app-with-firstn-and-restn)
            (%use (%instance (%thm lemma-for-equal-of-app-with-firstn-and-restn)
                             (n (len y))
                             (x x)))
            (%use (%instance (%thm lemma-2-for-equal-of-app-with-firstn-and-restn)
                             (n (len y))
                             (y (list-fix y))))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove equal-of-app-with-firstn-and-restn
            (%enable default lemma-4-for-equal-of-app-with-firstn-and-restn)
            (%use (%instance (%thm lemma-for-equal-of-app-with-firstn-and-restn))))
