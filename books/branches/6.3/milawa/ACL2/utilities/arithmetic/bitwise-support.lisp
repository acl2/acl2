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

(in-package "ACL2")

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (in-theory (disable evenp oddp floor mod logior logxor logand logbitp)))

(local (defun floor2-floor2-induction (a b)
         (declare (xargs :measure (nfix a)))
         (if (or (zp a)
                 (zp b))
             nil
           (floor2-floor2-induction (floor a 2) (floor b 2)))))

(local (defthm evenp-when-natp
         (implies (force (natp a))
                  (equal (evenp a)
                         (equal (mod a 2)
                                0)))
         :hints(("Goal" :in-theory (enable evenp)))))

(local (defthm oddp-when-natp
         (implies (force (natp a))
                  (equal (oddp a)
                         (equal (mod a 2)
                                1)))
         :hints(("Goal" :in-theory (enable oddp)))))


(defthm logand-positive-when-natps
  (implies (and (<= 0 a)
                (<= 0 b)
                (integerp a)
                (integerp b))
           (<= 0 (logand a b)))
  :hints(("Goal" :in-theory (enable logand))))

(defthm recursive-logand-when-natps
  (implies (and (natp a)
                (natp b))
           (equal (logand a b)
                  (cond ((zp a) 0)
                        ((zp b) 0)
                        (t (+ (if (or (equal (mod a 2) 0)
                                      (equal (mod b 2) 0))
                                  0
                                1)
                              (* 2 (logand (floor a 2) (floor b 2))))))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logand))))


(defthm logior-positive-when-natps
  (implies (and (<= 0 a)
                (<= 0 b)
                (integerp a)
                (integerp b))
           (<= 0 (logior a b)))
  :hints(("Goal"
          :in-theory (enable logior*)
          :induct (floor2-floor2-induction a b))))

(defthm recursive-logior-when-natps
   (implies (and (natp a)
                 (natp b))
            (equal (logior a b)
                   (cond ((zp a) b)
                         ((zp b) a)
                         (t (+ (if (or (equal (mod a 2) 1)
                                       (equal (mod b 2) 1))
                                   1
                                 0)
                               (* 2 (logior (floor a 2) (floor b 2))))))))
   :rule-classes :definition
   :hints(("Goal"
           :do-not '(generalize fertilize)
           :in-theory (enable logior*)
           :induct (floor2-floor2-induction a b))))


(defthm logxor-positive-when-natps
  (implies (and (<= 0 a)
                (<= 0 b)
                (integerp a)
                (integerp b))
           (<= 0 (logxor a b)))
  :hints(("Goal"
          :in-theory (enable logxor*)
          :induct (floor2-floor2-induction a b))))

(defthm recursive-logxor-when-natps
   (implies (and (natp a)
                 (natp b))
            (equal (logxor a b)
                   (cond ((zp a) b)
                         ((zp b) a)
                         (t (+ (if (equal (mod a 2) (mod b 2))
                                   0
                                 1)
                               (* 2 (logxor (floor a 2) (floor b 2))))))))
   :rule-classes :definition
   :hints(("Goal"
           :in-theory (enable logxor*)
           :induct (floor2-floor2-induction a b))))



(local (defun dec-floor2-induction (n a)
         (declare (xargs :measure (nfix n)))
         (if (zp n)
             a
           (dec-floor2-induction (- n 1) (floor a 2)))))

(defthm recursive-logbitp-when-natps
  (implies (and (natp n)
                (natp a))
           (equal (logbitp n a)
                  (if (zp n)
                      (equal (mod a 2) 1)
                    (logbitp (- n 1) (floor a 2)))))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logbitp*)
          :induct (dec-floor2-induction n a))))
