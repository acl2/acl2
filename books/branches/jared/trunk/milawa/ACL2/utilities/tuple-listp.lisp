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
(include-book "strip-firsts")
(include-book "strip-seconds")
(include-book "strip-lens")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; BOZO this doesn't really belong here
(deflist true-list-listp (x)
  (true-listp x)
  :elementp-of-nil t)



(deflist tuple-listp (n x)
  (tuplep n x)
  :guard (natp n))

(defthm rank-of-strip-firsts-when-tuple-listp-2
  (implies (and (tuple-listp 2 x)
                (consp x))
           (equal (< (rank (strip-firsts x)) (rank x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rank-of-strip-seconds-when-tuple-listp-2
  (implies (and (tuple-listp 2 x)
                (consp x))
           (equal (< (rank (strip-seconds x)) (rank x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm strip-lens-when-tuple-listp
  (implies (tuple-listp n x)
           (equal (strip-lens x)
                  (repeat (nfix n) (len x))))
  :hints(("Goal" :induct (cdr-induction x))))





(defund list2-list (x y)
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp y))
      (cons (list (car x) (car y))
            (list2-list (cdr x) (cdr y)))
    nil))

(defthm list2-list-when-not-consp-one
  (implies (not (consp x))
           (equal (list2-list x y)
                  nil))
  :hints(("Goal" :in-theory (enable list2-list))))

(defthm list2-list-when-not-consp-two
  (implies (not (consp y))
           (equal (list2-list x y)
                  nil))
  :hints(("Goal" :in-theory (enable list2-list))))

(defthm list2-list-of-cons-and-cons
  (equal (list2-list (cons a x) (cons b y))
         (cons (list a b)
               (list2-list x y)))
  :hints(("Goal" :in-theory (enable list2-list))))

(defthm true-listp-of-list2-list
  (equal (true-listp (list2-list x y))
         t)
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm true-listp-list-of-list2-list
  (equal (true-list-listp (list2-list x y))
         t)
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm list2-list-of-list-fix-one
  (equal (list2-list (list-fix x) y)
         (list2-list x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm list2-list-of-list-fix-two
  (equal (list2-list x (list-fix y))
         (list2-list x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm len-of-list2-list
  (equal (len (list2-list x y))
         (min (len x) (len y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm strip-lens-of-list2-list
  (equal (strip-lens (list2-list x y))
         (repeat 2 (min (len x) (len y))))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))


(defthm tuple-listp-of-list2-list
  (equal (tuple-listp n (list2-list x y))
         (or (not (consp x))
             (not (consp y))
             (equal n 2)))
  :hints(("Goal" :in-theory (enable list2-list)))) ;; yuck

(defthm forcing-strip-firsts-of-list2-list
  (implies (force (equal (len x) (len y)))
           (equal (strip-firsts (list2-list x y))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-strip-seconds-of-list2-list
  (implies (force (equal (len x) (len y)))
           (equal (strip-seconds (list2-list x y))
                  (list-fix y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))
