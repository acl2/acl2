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
(include-book "multiply")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm natp-of-floor
  (equal (natp (floor a b))
         t)
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-zp-left-cheap
  (implies (zp a)
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-zp-right-cheap
  (implies (zp b)
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm |(floor 0 a)|
  (equal (floor 0 a)
         0))

(defthm |(floor a 0)|
  (equal (floor a 0)
         0))

(defthm floor-when-smaller
  (implies (< a b)
           (equal (floor a b)
                  0))
  :hints(("Goal" :expand (floor a b))))

(defthm |(floor a a)|
  (equal (floor a a)
         (if (zp a)
             0
           1))
  :hints(("Goal" :expand (floor a a))))

(defthm |(floor 1 a)|
  (equal (floor 1 a)
         (if (equal a 1)
             1
           0))
  :hints(("Goal" :expand (floor 1 a))))

(defthm |(floor a 1)|
  (equal (floor a 1)
         (nfix a))
  :hints(("Goal"
          :induct (sub-induction a 1)
          :expand (floor a 1))))

(defthm |(< a (floor a b))|
  (equal (< a (floor a b))
         nil)
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (floor a b))))

(defthm |(< (floor a b) a)|
  (equal (< (floor a b) a)
         (cond ((zp a) nil)
               ((zp b) t)
               ((equal a 1) (< a b))
               ((equal b 1) nil)
               (t t)))
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (floor a b))))

(defthm |(floor (* a b) b)|
  (equal (floor (* a b) b)
         (if (zp b)
             0
           (nfix a)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (floor (* a b) b))))

(defthm |(floor (* a b) a)|
  (equal (floor (* a b) a)
         (if (zp a)
             0
           (nfix b)))
  :hints(("Goal"
          :in-theory (disable |(floor (* a b) b)|)
          :use ((:instance |(floor (* a b) b)| (a b) (b a))))))

