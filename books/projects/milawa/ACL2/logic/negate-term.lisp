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
(include-book "substitute-term")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund logic.negate-term (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.function 'not (list x)))

(defthm forcing-logic.termp-of-logic.negate-term
  (implies (force (logic.termp x))
           (equal (logic.termp (logic.negate-term x))
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term))))

(defthm forcing-logic.term-atblp-of-logic.negate-term
  (implies (force (and (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-atblp (logic.negate-term x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term))))



(defprojection :list (logic.negate-term-list x)
               :element (logic.negate-term x)
               :guard (logic.term-listp x))

(defthm forcing-logic.term-listp-of-logic.negate-term-list
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (logic.negate-term-list x))
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term-list))))

(defthm forcing-logic.term-list-atblp-of-logic.negate-term-list
  (implies (force (and (logic.term-list-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-atblp (logic.negate-term-list x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.negate-term-list))))



(defthm logic.substitute-of-logic.negate-term
  (equal (logic.substitute (logic.negate-term x) sigma)
         (logic.negate-term (logic.substitute x sigma)))
  :hints(("Goal" :in-theory (enable logic.negate-term))))

(defthm logic.substitute-list-of-logic.negate-term-list
  (equal (logic.substitute-list (logic.negate-term-list x) sigma)
         (logic.negate-term-list (logic.substitute-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))