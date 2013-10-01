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


;; We say that x is an ordered subset of y when every member of x is also a
;; member of y, and the elements occur in the same order in x and y.

(defund ordered-subsetp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (if (equal (car x) (car y))
               (ordered-subsetp (cdr x) (cdr y))
             (ordered-subsetp x (cdr y))))
    t))

(defthm ordered-subsetp-when-not-consp-one
  (implies (not (consp x))
           (equal (ordered-subsetp x y)
                  t))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-when-not-consp-two
  (implies (not (consp y))
           (equal (ordered-subsetp x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-cons-and-cons
  (equal (ordered-subsetp (cons a x) (cons b y))
         (if (equal a b)
             (ordered-subsetp x y)
           (ordered-subsetp (cons a x) y)))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm booleanp-of-ordered-subsetp
  (equal (booleanp (ordered-subsetp x y))
         t)
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(encapsulate
 ()
 (local (defun my-induction (x y)
          (declare (xargs :export nil))
          (if (and (consp x)
                   (consp y))
              (list (my-induction x (cdr y))
                    (my-induction (cdr x) (cdr y)))
            nil)))

 (defthm ordered-subsetp-of-cdr-when-ordered-subsetp
   (implies (ordered-subsetp x y)
            (equal (ordered-subsetp (cdr x) y)
                   t))
   :hints(("Goal" :induct (my-induction x y)))))

(defthm ordered-subsetp-when-ordered-subsetp-of-cons
  (implies (ordered-subsetp (cons a x) y)
           (equal (ordered-subsetp x y)
                  t))
  :hints(("Goal" :use ((:instance ordered-subsetp-of-cdr-when-ordered-subsetp
                                  (x (cons a x))
                                  (y y))))))

(defthm ordered-subsetp-of-cons-when-ordered-subsetp
  (implies (ordered-subsetp x y)
           (equal (ordered-subsetp x (cons a y))
                  t))
  :hints(("Goal" :expand (ordered-subsetp x (cons a y)))))

(defthm ordered-subsetp-when-ordered-subsetp-of-cdr
  (implies (ordered-subsetp x (cdr y))
           (equal (ordered-subsetp x y)
                  t)))

(defthm ordered-subsetp-is-reflexive
  (equal (ordered-subsetp x x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(encapsulate
 ()
 (local (defun my-induction (x y z)
          (declare (xargs :measure (+ (rank x) (+ (rank y) (rank z)))
                          :export nil))
          (if (and (consp x)
                   (consp y)
                   (consp z))
              (list (my-induction (cdr x) (cdr y) (cdr z))
                    (my-induction (cdr x) (cdr y) z)
                    (my-induction x (cdr y) (cdr z))
                    (my-induction x y (cdr z)))
            nil)))

 (defthm ordered-subsetp-is-transitive
   (implies (and (ordered-subsetp x y)
                 (ordered-subsetp y z))
            (equal (ordered-subsetp x z)
                   t))
   :hints(("Goal" :induct (my-induction x y z)))))

(defthm ordered-subsetp-of-list-fix-one
  (equal (ordered-subsetp (list-fix x) y)
         (ordered-subsetp x y))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-list-fix-two
  (equal (ordered-subsetp x (list-fix y))
         (ordered-subsetp x y))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-app-when-ordered-subsetp-one
  (implies (ordered-subsetp x y)
           (ordered-subsetp x (app y z)))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-app-one
  (equal (ordered-subsetp x (app x y))
         t))

(defthm ordered-subsetp-of-app-two
  (equal (ordered-subsetp x (app y x))
         t)
  :hints(("Goal" :induct (cdr-induction y))))

(defthm ordered-subsetp-of-app-when-ordered-subsetp-two
  (implies (ordered-subsetp x y)
           (ordered-subsetp x (app z y)))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm subsetp-when-ordered-subsetp
  (implies (ordered-subsetp x y)
           (equal (subsetp x y)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable ordered-subsetp))))

(defthm ordered-subsetp-of-remove-duplicates
  (equal (ordered-subsetp (remove-duplicates x) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordered-subsetp-of-remove-all
  (equal (ordered-subsetp (remove-all a x) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm ordered-subsetp-of-difference
  (equal (ordered-subsetp (difference x y) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

