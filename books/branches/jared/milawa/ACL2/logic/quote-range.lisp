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
(include-book "groundp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Walk through a map, quoting every element in the range.

(defund logic.quote-range (x)
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (cons (car (car x))
                  (list 'quote (cdr (car x))))
            (logic.quote-range (cdr x)))
    nil))

(defthm logic.quote-range-when-not-consp
  (implies (not (consp x))
           (equal (logic.quote-range x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.quote-range))))

(defthm logic.quote-range-of-cons
  (equal (logic.quote-range (cons a x))
         (cons (cons (car a) (list 'quote (cdr a)))
               (logic.quote-range x)))
  :hints(("Goal" :in-theory (enable logic.quote-range))))

(defthm true-listp-of-logic.quote-range
  (equal (true-listp (logic.quote-range x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.quote-range-of-list-fix
  (equal (logic.quote-range (list-fix x))
         (logic.quote-range x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-logic.quote-range
  (equal (len (logic.quote-range x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.quote-range-of-app
  (equal (logic.quote-range (app x y))
         (app (logic.quote-range x)
              (logic.quote-range y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.sigmap-of-logic.quote-range
  (implies (force (logic.sigmap x))
           (equal (logic.sigmap (logic.quote-range x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.sigma-atblp-of-logic.quote-range
  (implies (force (logic.variable-listp (domain sigma)))
           (equal (logic.sigma-atblp (logic.quote-range sigma) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction sigma))))

(defthm forcing-logic.constant-listp-of-range-of-logic.quote-range
  (implies (force (logic.sigmap x))
           (equal (logic.constant-listp (range (logic.quote-range x)))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.ground-listp-of-range-of-logic.quote-range
  (implies (force (logic.sigmap x))
           (equal (logic.ground-listp (range (logic.quote-range x)))
                  t)))

(defthm forcing-domain-of-logic.quote-range
  (equal (domain (logic.quote-range x))
         (domain x))
  :hints(("Goal" :induct (cdr-induction x))))

