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
(include-book "extended-primitives")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm natp-of-*
  (equal (natp (* a b))
         t)
  :hints(("Goal" :expand (* a b))))

(defthm *-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (* a b))))

(defthm *-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b))))

(defthm *-when-zp-left-cheap
  (implies (zp a)
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (* a b))))

(defthm *-when-zp-right-cheap
  (implies (zp b)
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b))))

(defthm |(* 0 a)|
  (equal (* 0 a)
         0)
  :hints(("Goal" :expand (* 0 a))))

(defthm |(* a 0)|
  (equal (* a 0)
         0)
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a 0))))

(defthm |(* (nfix a) b)|
  (equal (* (nfix a) b)
         (* a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(* a (nfix b))|
  (equal (* a (nfix b))
         (* a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(* 1 a)|
  (equal (* 1 a)
         (nfix a))
  :hints(("Goal" :expand (* 1 a))))

(defthm |(* a 1)|
  (equal (* a 1)
         (nfix a))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a 1))))

(defthm |(equal (* a b) 0)|
  (equal (equal (* a b) 0)
         (or (zp a)
             (zp b)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b))))

(defthm |(* (+ a c) b)|
  (equal (* (+ a c) b)
         (+ (* a b) (* c b)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand ((* (+ 1 c) b)
                   (* (+ a c) b)
                   (* a b)))))

(defthm |(* a (+ b c))|
  (equal (* a (+ b c))
         (+ (* a b) (* a c)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand ((* a (+ b c))
                   (* a b)
                   (* a c)))))

(defthm |(* (- a b) c)|
  (equal (* (- a b) c)
         (- (* a c) (* b c)))
  :hints(("Goal"
          :induct (dec-dec-induction a b)
          :expand ((* (- a b) c)
                   (* a c)
                   (* b c)))))

(defthm |(* a (- b c))|
  (equal (* a (- b c))
         (- (* a b) (* a c)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand ((* a b)
                   (* a c)
                   (* a (- b c)))
          :in-theory (disable |(* (- a b) c)|)
          :do-not-induct t)))

(defthm |(< a (* a b))|
  (equal (< a (* a b))
         (and (not (zp a))
              (< 1 b)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm |(< b (* a b))|
  (equal (< b (* a b))
         (and (not (zp b))
              (< 1 a)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b)
          :in-theory (disable |(* (- a b) c)|))))

(defthm |(< (* a b) a)|
  (equal (< (* a b) a)
         (and (not (zp a))
              (zp b)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm |(< (* a b) b)|
  (equal (< (* a b) b)
         (and (not (zp b))
              (zp a)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm |(< (* a c) (* b c))|
  (equal (< (* a c) (* b c))
         (and (< a b)
              (not (zp c))))
  :hints(("Goal" :induct (dec-dec-induction a b))))

(defthm |(< (* a b) (* a c))|
  (equal (< (* a b) (* a c))
         (and (< b c)
              (not (zp a))))
  :hints(("Goal" :induct (dec-induction a))))

(defthm associativity-of-*
  (equal (* (* a b) c)
         (* a (* b c)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm commutativity-of-*
  (equal (* a b)
         (* b a))
  :hints(("Goal" :induct (dec-induction a))))

(defthm commutativity-of-*-two
  (equal (* a (* b c))
         (* b (* a c)))
  :hints(("Goal" :use ((:instance commutativity-of-* (a a) (b (* b c)))))))

(defthm |(= a (* a b))|
  (equal (equal a (* a b))
         (if (zp a)
             (natp a)
           (equal b 1)))
  :hints(("Goal"
          :expand ((* a b)
                   (* b (- a 1)))
          :in-theory (disable |(* a (- b c))|))))

(defthm |(= 1 (* a b))|
  (equal (equal 1 (* a b))
         (and (equal a 1)
              (equal b 1)))
  :hints(("Goal"
          :expand ((* a b))
          :use ((:instance |(* a (- b c))| (a b) (b a) (c 1)))
          :in-theory (disable |(* a (- b c))|))))

