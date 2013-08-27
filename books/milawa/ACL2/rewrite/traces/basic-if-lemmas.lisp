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

(dd.open "basic-trace-if-lemmas.tex")

(defderiv rw.iff-implies-equal-if-specialcase-nil-bldr
  :derive (= (equal (if (? a1) (? b1) (? c1)) (? c2)) t)
  :from   ((proof x (= (iff (? a1) nil) t))
           (proof y (= (equal (? c1) (? c2)) t))
           (term b1 (? b1)))
  :proof  (@derive
           ((= (iff (? a1) nil) t)                                                                                        (@given x) *1)
           ((= (equal (? c1) (? c2)) t)                                                                                   (@given y) *2)
           ((v (!= (iff x1 nil) t) (v (!= (equal z1 z2) t) (= (equal (if x1 y1 z1) z2) t)))                               (build.theorem (rw.theorem-iff-implies-equal-if-specialcase-nil)))
           ((v (!= (iff (? a1) nil) t) (v (!= (equal (? c1) (? c2)) t) (= (equal (if (? a1) (? b1) (? c1)) (? c2)) t)))   (build.instantiation @- (@sigma (x1 . (? a1)) (y1 . (? b1)) (z1 . (? c1)) (z2 . (? c2)))))
           ((= (equal (if (? a1) (? b1) (? c1)) (? c2)) t)                                                                (rw.two-modus-ponens *1 *2 @-)))
  :minatbl ((if . 3)
            (equal . 2)))

(defderiv rw.iff-implies-iff-if-specialcase-nil-bldr
  :derive (= (iff (if (? a1) (? b1) (? c1)) (? c2)) t)
  :from   ((proof x (= (iff (? a1) nil) t))
           (proof y (= (iff (? c1) (? c2)) t))
           (term b1 (? b1)))
  :proof  (@derive
           ((= (iff (? a1) nil) t)                                                                                     (@given x) *1)
           ((= (iff (? c1) (? c2)) t)                                                                                  (@given y) *2)
           ((v (!= (iff x1 nil) t) (v (!= (iff z1 z2) t) (= (iff (if x1 y1 z1) z2) t)))                                (build.theorem (rw.theorem-iff-implies-iff-if-specialcase-nil)))
           ((v (!= (iff (? a1) nil) t) (v (!= (iff (? c1) (? c2)) t) (= (iff (if (? a1) (? b1) (? c1)) (? c2)) t)))    (build.instantiation @- (@sigma (x1 . (? a1)) (y1 . (? b1)) (z1 . (? c1)) (z2 . (? c2)))))
           ((= (iff (if (? a1) (? b1) (? c1)) (? c2)) t)                                                               (rw.two-modus-ponens *1 *2 @-)))
  :minatbl ((if . 3)))



(defderiv rw.iff-implies-equal-if-specialcase-t-bldr
  :derive (= (equal (if (? a1) (? b1) (? c1)) (? b2)) t)
  :from   ((proof x (= (iff (? a1) (? a2)) t))
           (proof y (!= (? a2) nil))
           (proof z (= (equal (? b1) (? b2)) t))
           (term c1 (? c1)))
  :proof  (@derive
           ((= (iff (? a1) (? a2)) t)                                                                                                           (@given x) *1)
           ((!= (? a2) nil)                                                                                                                     (@given y) *2)
           ((= (equal (? b1) (? b2)) t)                                                                                                         (@given z) *3)
           ((v (!= (iff x1 x2) t) (v (= x2 nil) (v (!= (equal y1 y2) t) (= (equal (if x1 y1 z1) y2) t))))                                       (build.theorem (rw.theorem-iff-implies-equal-if-specialcase-t)))
           ((v (!= (iff (? a1) (? a2)) t) (v (= (? a2) nil) (v (!= (equal (? b1) (? b2)) t) (= (equal (if (? a1) (? b1) (? c1)) (? b2)) t))))   (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)))))
           ((= (equal (if (? a1) (? b1) (? c1)) (? b2)) t)                                                                                      (rw.mp-mp2-mp *1 *2 *3 @-)))
  :minatbl ((equal . 2)
            (if . 3)))

(defderiv rw.iff-implies-iff-if-specialcase-t-bldr
  :derive (= (iff (if (? a1) (? b1) (? c1)) (? b2)) t)
  :from   ((proof x (= (iff (? a1) (? a2)) t))
           (proof y (!= (? a2) nil))
           (proof z (= (iff (? b1) (? b2)) t))
           (term c1 (? c1)))
  :proof  (@derive
           ((= (iff (? a1) (? a2)) t)                                                                                                       (@given x) *1)
           ((!= (? a2) nil)                                                                                                                 (@given y) *2)
           ((= (iff (? b1) (? b2)) t)                                                                                                       (@given z) *3)
           ((v (!= (iff x1 x2) t) (v (= x2 nil) (v (!= (iff y1 y2) t) (= (iff (if x1 y1 z1) y2) t))))                                       (build.theorem (rw.theorem-iff-implies-iff-if-specialcase-t)))
           ((v (!= (iff (? a1) (? a2)) t) (v (= (? a2) nil) (v (!= (iff (? b1) (? b2)) t) (= (iff (if (? a1) (? b1) (? c1)) (? b2)) t))))   (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)))))
           ((= (iff (if (? a1) (? b1) (? c1)) (? b2)) t)                                                                                    (rw.mp-mp2-mp *1 *2 *3 @-)))
  :minatbl ((if . 3)))



(defderiv rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr
  :derive (v P (= (equal (if (? a1) (? b1) (? c1)) (? c2)) t))
  :from   ((proof x (v P (= (iff (? a1) nil) t)))
           (proof y (v P (= (equal (? c1) (? c2)) t)))
           (term b1 (? b1)))
  :proof  (@derive
           ((v P (= (iff (? a1) nil) t))                                                                                        (@given x) *1)
           ((v P (= (equal (? c1) (? c2)) t))                                                                                   (@given y) *2)
           ((v (!= (iff x1 nil) t) (v (!= (equal z1 z2) t) (= (equal (if x1 y1 z1) z2) t)))                                     (build.theorem (rw.theorem-iff-implies-equal-if-specialcase-nil)))
           ((v (!= (iff (? a1) nil) t) (v (!= (equal (? c1) (? c2)) t) (= (equal (if (? a1) (? b1) (? c1)) (? c2)) t)))         (build.instantiation @- (@sigma (x1 . (? a1)) (y1 . (? b1)) (z1 . (? c1)) (z2 . (? c2)))))
           ((v P (= (equal (if (? a1) (? b1) (? c1)) (? c2)) t))                                                                (rw.two-disjoined-modus-ponens *1 *2 @-)))
  :minatbl ((if . 3)
            (equal . 2)))

(defderiv rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr
  :derive (v P (= (iff (if (? a1) (? b1) (? c1)) (? c2)) t))
  :from   ((proof x (v P (= (iff (? a1) nil) t)))
           (proof y (v P (= (iff (? c1) (? c2)) t)))
           (term b1 (? b1)))
  :proof  (@derive
           ((v P (= (iff (? a1) nil) t))                                                                                   (@given x) *1)
           ((v P (= (iff (? c1) (? c2)) t))                                                                                (@given y) *2)
           ((v (!= (iff x1 nil) t) (v (!= (iff z1 z2) t) (= (iff (if x1 y1 z1) z2) t)))                                    (build.theorem (rw.theorem-iff-implies-iff-if-specialcase-nil)))
           ((v (!= (iff (? a1) nil) t) (v (!= (iff (? c1) (? c2)) t) (= (iff (if (? a1) (? b1) (? c1)) (? c2)) t)))        (build.instantiation @- (@sigma (x1 . (? a1)) (y1 . (? b1)) (z1 . (? c1)) (z2 . (? c2)))))
           ((v P (= (iff (if (? a1) (? b1) (? c1)) (? c2)) t))                                                             (rw.two-disjoined-modus-ponens *1 *2 @-)))
  :minatbl ((if . 3)))



(defderiv rw.disjoined-iff-implies-equal-if-specialcase-t-bldr
  :derive (v P (= (equal (if (? a1) (? b1) (? c1)) (? b2)) t))
  :from   ((proof x (v P (= (iff (? a1) (? a2)) t)))
           (proof y (v P (!= (? a2) nil)))
           (proof z (v P (= (equal (? b1) (? b2)) t)))
           (term c1 (? c1)))
  :proof  (@derive
           ((v P (= (iff (? a1) (? a2)) t))                                                                                                          (@given x) *1)
           ((v P (!= (? a2) nil))                                                                                                                    (@given y) *2)
           ((v P (= (equal (? b1) (? b2)) t))                                                                                                        (@given z) *3)
           ((v (!= (iff x1 x2) t) (v (= x2 nil) (v (!= (equal y1 y2) t) (= (equal (if x1 y1 z1) y2) t))))                                            (build.theorem (rw.theorem-iff-implies-equal-if-specialcase-t)))
           ((v (!= (iff (? a1) (? a2)) t) (v (= (? a2) nil) (v (!= (equal (? b1) (? b2)) t) (= (equal (if (? a1) (? b1) (? c1)) (? b2)) t))))        (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)))))
           ((v P (= (equal (if (? a1) (? b1) (? c1)) (? b2)) t))                                                                                     (rw.disjoined-mp-mp2-mp *1 *2 *3 @-)))
  :minatbl ((equal . 2)
            (if . 3)))

(defderiv rw.disjoined-iff-implies-iff-if-specialcase-t-bldr
  :derive (v P (= (iff (if (? a1) (? b1) (? c1)) (? b2)) t))
  :from   ((proof x (v P (= (iff (? a1) (? a2)) t)))
           (proof y (v P (!= (? a2) nil)))
           (proof z (v P (= (iff (? b1) (? b2)) t)))
           (term c1 (? c1)))
  :proof  (@derive
           ((v P (= (iff (? a1) (? a2)) t))                                                                                                      (@given x) *1)
           ((v P (!= (? a2) nil))                                                                                                                (@given y) *2)
           ((v P (= (iff (? b1) (? b2)) t))                                                                                                      (@given z) *3)
           ((v (!= (iff x1 x2) t) (v (= x2 nil) (v (!= (iff y1 y2) t) (= (iff (if x1 y1 z1) y2) t))))                                            (build.theorem (rw.theorem-iff-implies-iff-if-specialcase-t)))
           ((v (!= (iff (? a1) (? a2)) t) (v (= (? a2) nil) (v (!= (iff (? b1) (? b2)) t) (= (iff (if (? a1) (? b1) (? c1)) (? b2)) t))))        (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)))))
           ((v P (= (iff (if (? a1) (? b1) (? c1)) (? b2)) t))                                                                                   (rw.disjoined-mp-mp2-mp *1 *2 *3 @-)))
  :minatbl ((if . 3)))

(dd.close)
