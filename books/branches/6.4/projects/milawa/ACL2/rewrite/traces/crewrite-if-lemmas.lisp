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
(include-book "if-lemmas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "crewrite-trace-if-lemmas.tex")


(defderiv rw.disjoined-iff-implies-equal-if-bldr
  :derive (v P (= (equal (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))
  :from   ((proof x (v P (= (iff (? a1) (? a2)) t)))
           (proof y (v P (v (!= (not (? a2)) nil) (= (equal (? b1) (? b2)) t))))
           (proof z (v P (v (!= (? a2) nil) (= (equal (? c1) (? c2)) t)))))
  :proof  (@derive
           ((v P (= (iff (? a1) (? a2)) t))                                                  (@given x) *1)
           ((v P (v (!= (not (? a2)) nil) (= (equal (? b1) (? b2)) t)))                      (@given y) *2)
           ((v P (v (!= (? a2) nil) (= (equal (? c1) (? c2)) t)))                            (@given z) *3)
           ((v (!= (iff x1 x2) t)
              (v (! (v (!= (not x2) nil) (= (equal y1 y2) t)))
                 (v (! (v (!= x2 nil) (= (equal z1 z2) t)))
                    (= (equal (if x1 y1 z1) (if x2 y2 z2)) t))))                             (build.theorem (rw.theorem-iff-implies-equal-if-combined)))
           ((v (!= (iff (? a1) (? a2)) t)
               (v (! (v (!= (not (? a2)) nil) (= (equal (? b1) (? b2)) t)))
                  (v (! (v (!= (? a2) nil) (= (equal (? c1) (? c2)) t)))
                     (= (equal (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))))    (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)) (z2 . (? c2)))))
           ((v P (= (equal (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))          (rw.three-disjoined-modus-ponens *1 *2 *3 @-)))
  :minatbl ((if . 3)))

(defderiv rw.disjoined-iff-implies-iff-if-bldr
  :derive (v P (= (iff (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))
  :from   ((proof x (v P (= (iff (? a1) (? a2)) t)))
           (proof y (v P (v (!= (not (? a2)) nil) (= (iff (? b1) (? b2)) t))))
           (proof z (v P (v (!= (? a2) nil) (= (iff (? c1) (? c2)) t)))))
  :proof  (@derive
           ((v P (= (iff (? a1) (? a2)) t))                                                (@given x)  *1)
           ((v P (v (!= (not (? a2)) nil) (= (iff (? b1) (? b2)) t)))                      (@given y)  *2)
           ((v P (v (!= (? a2) nil) (= (iff (? c1) (? c2)) t)))                            (@given z)  *3)
           ((v (!= (iff x1 x2) t)
               (v (! (v (!= (not x2) nil) (= (iff y1 y2) t)))
                  (v (! (v (!= x2 nil) (= (iff z1 z2) t)))
                     (= (iff (if x1 y1 z1) (if x2 y2 z2)) t))))                            (build.theorem (rw.theorem-iff-implies-iff-if-combined)))
           ((v (!= (iff (? a1) (? a2)) t)
               (v (! (v (!= (not (? a2)) nil) (= (iff (? b1) (? b2)) t)))
                  (v (! (v (!= (? a2) nil) (= (iff (? c1) (? c2)) t)))
                     (= (iff (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))))    (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)) (z2 . (? c2)))))
           ((v P (= (iff (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))          (rw.three-disjoined-modus-ponens *1 *2 *3 @-)))
  :minatbl ((if . 3)))

(dd.close)
