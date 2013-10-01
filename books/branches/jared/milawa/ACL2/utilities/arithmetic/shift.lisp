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
(include-book "expt")
(include-book "floor")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(local (in-theory (enable definition-of-bitwise-shl
                          definition-of-bitwise-shr)))


;; One option for reasoning about shifting operations is to just remove them
;; entirely by nonrecursively redefining them in terms of floor, *, and expt.
;; To do this, just enable the following theorems.

(defthmd bitwise-shl-as-expt
  (equal (bitwise-shl a n)
         (* (expt 2 n) a))
  :hints(("Goal" :in-theory (enable definition-of-expt))))

;; BOZO prove me
;; (defthmd bitwise-shr-as-expt
;;    (equal (bitwise-shr a n)
;;           (floor a (expt 2 n)))
;;    :hints(("Goal" :in-theory (enable definition-of-expt))))



;; Otherwise, you can leave the functions in and reason about them directly.

(defthm natp-of-bitwise-shl
  (equal (natp (bitwise-shl a n))
         t))

(defthm bitwise-shl-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (bitwise-shl a n)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm bitwise-shl-when-not-natp-right-cheap
  (implies (not (natp n))
           (equal (bitwise-shl a n)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm |(bitwise-shl 0 n)|
  (equal (bitwise-shl 0 n)
         0))

(defthm |(bitwise-shl a 0)|
  (equal (bitwise-shl a 0)
         (nfix a)))

(defthm |(bitwise-shl (nfix a) n)|
  (equal (bitwise-shl (nfix a) n)
         (bitwise-shl a n)))

(defthm |(bitwise-shl a (nfix n))|
  (equal (bitwise-shl a (nfix n))
         (bitwise-shl a n)))

(defthm bitwise-shl-of-bitwise-shl
  (equal (bitwise-shl (bitwise-shl a n) m)
         (bitwise-shl a (+ n m)))
  :hints(("Goal" :in-theory (enable bitwise-shl-as-expt))))

(defthm |(= a (bitwise-shl a n))|
  (equal (equal a (bitwise-shl a n))
         (if (zp a)
             (natp a)
           (zp n)))
  :hints(("Goal" :in-theory (enable bitwise-shl-as-expt))))




(defthm natp-of-bitwise-shr
  (equal (natp (bitwise-shr a n))
         t))

(defthm bitwise-shr-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (bitwise-shr a n)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm bitwise-shr-when-not-natp-right-cheap
  (implies (not (natp n))
           (equal (bitwise-shr a n)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm |(bitwise-shr 0 n)|
  (equal (bitwise-shr 0 n)
         0))

(defthm |(bitwise-shr a 0)|
  (equal (bitwise-shr a 0)
         (nfix a)))

(defthm |(bitwise-shr (nfix a) n)|
  (equal (bitwise-shr (nfix a) n)
         (bitwise-shr a n)))

(defthm |(bitwise-shr a (nfix n))|
  (equal (bitwise-shr a (nfix n))
         (bitwise-shr a n)))

(defthm |(< (bitwise-shr a n) a)|
  (equal (< (bitwise-shr a n) a)
         (and (not (zp a))
              (not (zp n))))
  :hints(("Goal"
          :in-theory (enable definition-of-bitwise-shr)
          :induct (dec-induction n))))