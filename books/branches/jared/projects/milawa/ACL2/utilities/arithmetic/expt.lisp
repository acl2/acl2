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


(defthm natp-of-expt
  (equal (natp (expt a n))
         t)
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (expt a n)
                  (if (zp n)
                      1
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-not-natp-right-cheap
  (implies (not (natp n))
           (equal (expt a n)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-zp-left-cheap
  (implies (zp a)
           (equal (expt a n)
                  (if (zp n)
                      1
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-zp-right-cheap
  (implies (zp n)
           (equal (expt a n)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm |(expt 0 n)|
  (equal (expt 0 n)
         (if (zp n)
             1
           0)))

(defthm |(expt a 0)|
  (equal (expt a 0)
         1))

(defthm |(expt (nfix a) n)|
  (equal (expt (nfix a) n)
         (expt a n))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(expt a (nfix n))|
  (equal (expt a (nfix n))
         (expt a n))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(expt 1 n)|
  (equal (expt 1 n)
         1)
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt 1 n))))

(defthm |(expt n 1)|
  (equal (expt n 1)
         (nfix n))
  :hints(("Goal" :expand (expt n 1))))

(defthm |(= 0 (expt a n))|
  (equal (equal 0 (expt a n))
         (and (zp a)
              (not (zp n))))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt a n))))

(defthmd lemma-for-expt-of-plus-right
  (equal (expt a (+ 1 n))
         (* a (expt a n)))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand ((expt a (+ 1 n))
                   (expt a 2)))))

(defthm |(expt a (+ n m))|
  (equal (expt a (+ n m))
         (* (expt a n)
            (expt a m)))
  :hints(("Goal"
          :induct (dec-induction m)
          :in-theory (enable lemma-for-expt-of-plus-right)
          :expand ((expt a (+ m n))
                   (expt a m)))))

(defthm |(< a (expt a n))|
  (equal (< a (expt a n))
         (cond ((zp a) (zp n))
               ((equal a 1) nil)
               (t (< 1 n))))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand ((expt a n)
                   (expt a (- n 1))))))

(defthm |(< (expt a n) a)|
  (equal (< (expt a n) a)
         (and (< 1 a)
              (zp n)))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt a n))))

(defthm |(< (expt a n) (expt a m))|
  (equal (< (expt a n) (expt a m))
         (cond ((zp a)      (and (zp m) (not (zp n))))
               ((equal a 1) nil)
               (t           (< n m))))
  :hints(("Goal"
          :induct (dec-dec-induction n m)
          :expand ((expt a n)
                   (expt a m)))))

(defthm |(= 1 (expt a n))|
  (equal (equal 1 (expt a n))
         (or (zp n)
             (equal a 1)))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt a n))))

