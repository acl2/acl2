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
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund logic.formula-size (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cond ((equal (car x) 'por*)
             (+ 1
                (+ (if (consp (cdr x))
                       (logic.formula-size (second x))
                     1)
                   (if (and (consp (cdr x))
                            (consp (cdr (cdr x))))
                       (logic.formula-size (third x))
                     1))))
            ((equal (car x) 'pnot*)
             (+ 1
                (if (consp (cdr x))
                    (logic.formula-size (second x))
                  1)))
            (t
             (+ 1
                (+ (if (consp (cdr x))
                       (logic.formula-size (second x))
                     1)
                   (if (and (consp (cdr x))
                            (consp (cdr (cdr x))))
                       (logic.formula-size (third x))
                     1)))))
    1))

(defthm natp-of-logic.formula-size
  (natp (logic.formula-size x))
  :hints(("Goal" :in-theory (e/d (logic.formula-size)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm logic.formula-size-nonzero
  (equal (equal (logic.formula-size x) 0)
         nil)
  :hints(("Goal" :in-theory (enable logic.formula-size))))

(defthm ordp-of-logic.formula-size
  (equal (ordp (logic.formula-size x))
         t))

(defthm forcing-logic.formula-size-of-logic.=lhs
  (implies (force (equal (logic.fmtype x) 'pequal*))
           (equal (< (logic.formula-size (logic.=lhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.=lhs))))

(defthm forcing-logic.formula-size-of-logic.=rhs
  (implies (force (equal (logic.fmtype x) 'pequal*))
           (equal (< (logic.formula-size (logic.=rhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.=rhs))))

(defthm forcing-logic.formula-size-of-logic.~arg
  (implies (force (equal (logic.fmtype x) 'pnot*))
           (equal (< (logic.formula-size (logic.~arg x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.~arg))))

(defthm forcing-logic.formula-size-of-logic.vlhs
  (implies (force (equal (logic.fmtype x) 'por*))
           (equal (< (logic.formula-size (logic.vlhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vlhs))))

(defthm forcing-logic.formula-size-of-logic.vrhs
  (implies (force (equal (logic.fmtype x) 'por*))
           (equal (< (logic.formula-size (logic.vrhs x))
                     (logic.formula-size x))
                  t))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vrhs))))

(defthm logic.formula-size-of-logic.pnot
  (equal (logic.formula-size (logic.pnot x))
         (+ 1 (logic.formula-size x)))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.pnot))))

(defthm logic.formula-size-of-logic.por
  (equal (logic.formula-size (logic.por x y))
         (+ 1 (+ (logic.formula-size x) (logic.formula-size y))))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.por))))

(defthm logic.formula-size-of-pequal
  (equal (logic.formula-size (logic.pequal x y))
         (+ 1 (+ (logic.formula-size x) (logic.formula-size y))))
  :hints(("Goal" :in-theory (enable logic.formula-size logic.pequal))))



(defund logic.formula-list-size (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ (logic.formula-size (car x))
         (logic.formula-list-size (cdr x)))
    0))

(defthm logic.formula-list-size-when-not-consp
  (implies (not (consp x))
           (equal (logic.formula-list-size x)
                  0))
  :hints(("Goal" :in-theory (enable logic.formula-list-size))))

(defthm logic.formula-list-size-of-cons
  (equal (logic.formula-list-size (cons a x))
         (+ (logic.formula-size a)
            (logic.formula-list-size x)))
  :hints(("Goal" :in-theory (enable logic.formula-list-size))))

(defthm natp-of-logic.formula-list-size
  (equal (natp (logic.formula-list-size x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordp-of-logic.formula-list-size
  (equal (ordp (logic.formula-list-size x))
         t))
