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
(include-book "dividesp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(local (in-theory (enable definition-of-bitwise-and)))


(defthm natp-of-bitwise-and
  (equal (natp (bitwise-and a b))
         t))

(defthm bitwise-and-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (bitwise-and a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm bitwise-and-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (bitwise-and a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm |(bitwise-and 0 a)|
  (equal (bitwise-and 0 a)
         0))

(defthm |(bitwise-and a 0)|
  (equal (bitwise-and a 0)
         0))

;; (defthm |(bitwise-and 1 a)|
;;   (equal (bitwise-and 1 a)
;;          (not (dividesp 2 a)))
;;   :hints(("Goal" :in-theory (enable dividesp))))





(defthm natp-of-bitwise-or
  (equal (natp (bitwise-or a b))
         t)
  :hints(("Goal" :in-theory (enable definition-of-bitwise-or))))

(defthm natp-of-bitwise-xor
  (equal (natp (bitwise-xor a b))
         t)
  :hints(("Goal" :in-theory (enable definition-of-bitwise-xor))))

(defthm booleanp-of-bitwise-nth
  (equal (booleanp (bitwise-nth a b))
         t)
  :hints(("Goal" :in-theory (enable definition-of-bitwise-nth))))

