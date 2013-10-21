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
(include-book "primitives-2")
(%interactive)



;; Less-Than and Addition.

(%autoprove |(< (+ a b) (+ a c))| (%use (build.axiom (axiom-less-than-of-plus-and-plus))))

(%autoprove |(< a (+ a b))|
            (%disable default
                      |(< (+ a b) (+ a c))|
                      |[OUTSIDE](< (+ a b) (+ a c))|)
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (b 0) (c b))))

(%autoprove |(< a (+ b a))|)

(%autoprove |(< (+ a b) a)|
            (%disable default
                      |(< (+ a b) (+ a c))|
                      |[OUTSIDE](< (+ a b) (+ a c))|)
            (%use (%instance (%thm |(< (+ a b) (+ a c))|) (c 0))))

(%autoprove |(< (+ b a) a)|)

(%autoprove |(< a (+ b c a))|)
(%autoprove |(< a (+ b a c))|)
(%autoprove |(< a (+ b c d a))|)
(%autoprove |(< a (+ b c a d))|)
(%autoprove |(< a (+ b c d e a))|)
(%autoprove |(< a (+ b c d a e))|)
(%autoprove |(< a (+ b c d e f a))|)
(%autoprove |(< a (+ b c d e a f))|)

(%autoprove |(< (+ a b) (+ c a))|)
(%autoprove |(< (+ b a) (+ c a))|)
(%autoprove |(< (+ b a) (+ a c))|)

(%autoprove |(< (+ a b) (+ c a d))|)
(%autoprove |(< (+ b a c) (+ d a))|)

(%autoprove |a <= b, c != 0 --> a < b+c| (%enable default zp))
(%autoprove |a <= b, c != 0 --> a < c+b|)

(%autoprove |a <= b, c != 0 --> a < c+b+d|
            ;; BOZO, why do I have to disable this?
            (%disable default [OUTSIDE]LESS-OF-ZERO-LEFT))
(%autoprove |a <= b, c != 0 --> a < c+d+b|
            (%disable default [OUTSIDE]LESS-OF-ZERO-LEFT))


(%autoprove |c < a, d <= b --> c+d < a+b|
            (%use (%instance (%thm transitivity-of-<-three) (a (+ c d)) (b (+ c b)) (c (+ a b)))))
(%autoprove |c < a, d <= b --> c+d < b+a|)

(%autoprove |c <= a, d < b --> c+d < a+b|
            (%use (%instance (%thm |c < a, d <= b --> c+d < a+b|) (c d) (a b) (d c) (b a))))
(%autoprove |c <= a, d < b --> c+d < b+a|)
(%autoprove |c <= a, d <= b --> c+d <= a+b|
            (%use (%instance (%thm transitivity-of-<-four) (a (+ c d)) (b (+ c b)) (c (+ a b)))))
(%autoprove |c <= a, d <= b --> c+d <= b+a|)

