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
(include-book "primitives-3")
(%interactive)


;; Equalities with Sums.

(%autoprove |(= a (+ a b))|
            (%enable default nfix)
            (%disable default |[OUTSIDE](< a (+ a b))|)
            (%auto)
            (%use (%thm |(< a (+ a b))|))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove |(= a (+ b a))|)

(%autoprove |lemma for (= (+ a b) (+ a c))|
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (a a) (b b) (c c)))
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (a a) (b c) (c b)))
            (%disable default |[OUTSIDE](< (+ a b) (+ a c))|)
            (%disable default |(< (+ a b) (+ a c))|))

(%autoprove |(= (+ a b) (+ a c))|
            (%enable default nfix)
            (%use (%instance (%thm |lemma for (= (+ a b) (+ a c))|)
                             (a a)
                             (b (nfix b))
                             (c (nfix c)))))

(%autoprove |(= (+ a b) (+ c a))|)
(%autoprove |(= (+ b a) (+ c a))|)
(%autoprove |(= (+ b a) (+ a c))|)

(%autoprove |(= 0 (+ a b))|
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (a b) (b 0) (c a)))
            (%disable default
                      |(< (+ a b) (+ a c))|
                      |[OUTSIDE](< (+ a b) (+ a c))|)
            (%auto :strategy (cleanup split crewrite)))

(%autoprove |lemma for (= (+ a x b) (+ c x d))|)

(%autoprove |(= (+ a x b) (+ c x d))|
            (%use (%instance (%thm |lemma for (= (+ a x b) (+ c x d))|)
                             (e a) (b x) (c b) (d c) (f d))))

(%autoprove squeeze-law-one
            (%enable default nfix))

(%autoprove squeeze-law-two
            (%enable default nfix))

(%autoprove squeeze-law-three
            (%enable default nfix))

