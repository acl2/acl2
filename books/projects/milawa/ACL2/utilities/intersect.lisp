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

(defund intersect (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (if (memberp (car x) y)
          (cons (car x)
                (intersect (cdr x) y))
        (intersect (cdr x) y))
    nil))

(defthm intersect-when-not-consp-one
  (implies (not (consp x))
           (equal (intersect x y)
                  nil))
  :hints(("Goal" :in-theory (enable intersect))))

(defthm intersect-of-cons-one
  (equal (intersect (cons a x) y)
         (if (memberp a y)
             (cons a (intersect x y))
           (intersect x y)))
  :hints(("Goal" :in-theory (enable intersect))))

(defthm intersect-when-not-consp-two
  (implies (not (consp y))
           (equal (intersect x y)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-under-iff
  (iff (intersect x y)
       (not (disjointp x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-intersect
  (equal (true-listp (intersect x y))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-list-fix-one
  (equal (intersect (list-fix x) y)
         (intersect x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-list-fix-two
  (equal (intersect x (list-fix y))
         (intersect x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-app-one
  (equal (intersect (app x y) z)
         (app (intersect x z)
              (intersect y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-intersect
  (equal (rev (intersect x y))
         (intersect (rev x) y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-of-rev-two
  (equal (intersect x (rev y))
         (intersect x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-intersect-one
  (equal (subsetp (intersect x y) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-intersect-two
  (equal (subsetp (intersect x y) y)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-when-subsetp
  (implies (subsetp x y)
           (equal (intersect x y)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm intersect-with-self
  (equal (intersect x x)
         (list-fix x)))
