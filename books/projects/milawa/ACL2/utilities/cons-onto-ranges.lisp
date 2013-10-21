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
(include-book "deflist")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; (cons-onto-ranges a x)
;;
;; X is a map.  We produce a new map whose entries are (key . (a . value))
;; for every (key . value) pair in x.

;; BOZO tail recursive version?

;; BOZO more complete theory?

(defund cons-onto-ranges (a x)
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (cons (car (car x))
                  (cons a (cdr (car x))))
            (cons-onto-ranges a (cdr x)))
    nil))

(defthm cons-onto-ranges-when-not-consp
  (implies (not (consp x))
           (equal (cons-onto-ranges a x)
                  nil))
  :hints(("Goal" :in-theory (enable cons-onto-ranges))))

(defthm cons-onto-ranges-of-cons
  (equal (cons-onto-ranges a (cons b x))
         (cons (cons (car b) (cons a (cdr b)))
               (cons-onto-ranges a x)))
  :hints(("Goal" :in-theory (enable cons-onto-ranges))))

(defthm cons-onto-ranges-of-list-fix
  (equal (cons-onto-ranges a (list-fix x))
         (cons-onto-ranges a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-cons-onto-ranges
  (equal (true-listp (cons-onto-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-onto-ranges-of-app
  (equal (cons-onto-ranges a (app x y))
         (app (cons-onto-ranges a x)
              (cons-onto-ranges a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mapp-of-cons-onto-ranges
  (equal (mapp (cons-onto-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm domain-of-cons-onto-ranges
  (equal (domain (cons-onto-ranges a x))
         (domain x))
  :hints(("Goal" :induct (cdr-induction x))))

