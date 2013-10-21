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
(include-book "utilities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund sort-symbols-insert (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (symbol-< a (car x))
          (cons a x)
        (cons (car x)
              (sort-symbols-insert a (cdr x))))
    (list a)))

(defthm sort-symbols-insert-when-not-consp
  (implies (not (consp x))
           (equal (sort-symbols-insert a x)
                  (list a)))
  :hints(("Goal" :in-theory (enable sort-symbols-insert))))

(defthm sort-symbols-insert-of-cons
  (equal (sort-symbols-insert a (cons b x))
         (if (symbol-< a b)
             (cons a (cons b x))
           (cons b (sort-symbols-insert a x))))
  :hints(("Goal" :in-theory (enable sort-symbols-insert))))

(defthm memberp-of-sort-symbols-insert
  (equal (memberp a (sort-symbols-insert b x))
         (or (equal a b)
             (memberp a x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-sort-symbols-insert
  (equal (len (sort-symbols-insert a x))
         (+ 1 (len x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-sort-symbols-insert
  (equal (consp (sort-symbols-insert a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm car-of-sort-symbols-insert
  (equal (car (sort-symbols-insert a x))
         (if (consp x)
             (if (symbol-< a (car x))
                 a
               (car x))
           a)))

(defthm uniquep-of-sort-symbols-insert
  (equal (uniquep (sort-symbols-insert a x))
         (and (uniquep x)
              (not (memberp a x))))
  :hints(("Goal" :induct (cdr-induction x))))



(defund sort-symbols (x)
  (declare (xargs :guard t))
  (if (consp x)
      (sort-symbols-insert (car x)
                           (sort-symbols (cdr x)))
    nil))

(defthm sort-symbols-when-not-consp
  (implies (not (consp x))
           (equal (sort-symbols x)
                  nil))
  :hints(("Goal" :in-theory (enable sort-symbols))))

(defthm sort-symbols-of-cons
  (equal (sort-symbols (cons a x))
         (sort-symbols-insert a (sort-symbols x)))
  :hints(("Goal" :in-theory (enable sort-symbols))))

(defthm memberp-of-sort-symbols
  (equal (memberp a (sort-symbols x))
         (memberp a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-sort-symbols
  (equal (len (sort-symbols x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-of-sort-symbols
  (equal (disjointp x (sort-symbols y))
         (disjointp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm uniquep-of-sort-symbols
  (equal (uniquep (sort-symbols x))
         (uniquep x))
  :hints(("Goal" :induct (cdr-induction x))))


(defund symbol-list-orderedp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (cdr x))
          (and (not (symbol-< (second x) (first x)))
               (symbol-list-orderedp (cdr x)))
        t)
    t))

(defthm symbol-list-orderedp-when-not-consp
  (implies (not (consp x))
           (equal (symbol-list-orderedp x)
                  t))
  :hints(("Goal" :in-theory (enable symbol-list-orderedp))))

(defthm symbol-list-orderedp-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (symbol-list-orderedp x)
                  t))
  :hints(("Goal" :in-theory (enable symbol-list-orderedp))))

(defthm symbol-list-orderedp-of-cons
  (equal (symbol-list-orderedp (cons a x))
         (if (consp x)
             (and (not (symbol-< (car x) a))
                  (symbol-list-orderedp x))
           t))
  :hints(("Goal" :in-theory (enable symbol-list-orderedp))))

(defthm symbol-list-orderedp-of-sort-symbols-insert
  (implies (symbol-list-orderedp x)
           (symbol-list-orderedp (sort-symbols-insert a x)))
  :hints(("Goal" :induct (cdr-induction x))))







