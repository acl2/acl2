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
(include-book "tuple-listp")
(include-book "list-list-fix")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund remove-all-from-ranges (a x)
  (declare (xargs :guard (mapp x)))
  (if (consp x)
      (cons (cons (car (car x))
                  (remove-all a (cdr (car x))))
            (remove-all-from-ranges a (cdr x)))
    nil))

(defthm remove-all-from-ranges-when-not-consp
  (implies (not (consp x))
           (equal (remove-all-from-ranges a x)
                  nil))
  :hints(("Goal" :in-theory (enable remove-all-from-ranges))))

(defthm remove-all-from-ranges-of-cons
  (equal (remove-all-from-ranges a (cons b x))
         (cons (cons (car b) (remove-all a (cdr b)))
               (remove-all-from-ranges a x)))
  :hints(("Goal" :in-theory (enable remove-all-from-ranges))))

(defthm true-listp-of-remove-all-from-ranges
  (equal (true-listp (remove-all-from-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-list-listp-of-remove-all-from-ranges
  (equal (true-list-listp (remove-all-from-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mapp-of-remove-all-from-ranges
  (equal (mapp (remove-all-from-ranges a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-all-from-ranges-of-list-fix
  (equal (remove-all-from-ranges a (list-fix x))
         (remove-all-from-ranges a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-all-from-ranges-of-list-list-fix
  (equal (remove-all-from-ranges a (list-list-fix x))
         (remove-all-from-ranges a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-all-from-ranges-of-app
  (equal (remove-all-from-ranges a (app x y))
         (app (remove-all-from-ranges a x)
              (remove-all-from-ranges a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-all-from-ranges-of-rev
  (equal (remove-all-from-ranges a (rev x))
         (rev (remove-all-from-ranges a x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm len-of-remove-all-from-ranges
  (equal (len (remove-all-from-ranges a x))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))
