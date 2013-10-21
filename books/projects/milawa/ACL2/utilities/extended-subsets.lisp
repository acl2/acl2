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
(include-book "cons-listp")
(include-book "remove-duplicates-list")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (superset-of-somep a x)
;;
;; Return true if there is some subset of a in x.  Note: this is an O(n^3)
;; operation since subsetp testing is quadratic.

(defund superset-of-somep (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (or (subsetp (car x) a)
          (superset-of-somep a (cdr x)))
    nil))

(defthm superset-of-somep-when-not-consp
  (implies (not (consp x))
           (equal (superset-of-somep a x)
                  nil))
  :hints(("Goal" :expand (superset-of-somep a x))))

(defthm superset-of-somep-of-cons
  (equal (superset-of-somep a (cons b x))
         (or (subsetp b a)
             (superset-of-somep a x)))
  :hints(("Goal" :expand (superset-of-somep a (cons b x)))))

(defthm booleanp-of-superset-of-somep
  (equal (booleanp (superset-of-somep a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-of-list-fix-one
  (equal (superset-of-somep (list-fix a) x)
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-of-list-fix-two
  (equal (superset-of-somep a (list-fix x))
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-of-app
  (equal (superset-of-somep a (app x y))
         (or (superset-of-somep a x)
             (superset-of-somep a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-of-rev
  (equal (superset-of-somep a (rev x))
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-when-not-superset-of-somep-cheap
  (implies (not (superset-of-somep a x))
           (equal (memberp a x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-when-obvious
  (implies (and (subsetp e a)
                (memberp e x))
           (equal (superset-of-somep a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-when-obvious-alt
  (implies (and (memberp e x)
                (subsetp e a))
           (equal (superset-of-somep a x)
                  t)))



;; (find-subset a x)
;;
;; A is a list and X is a list of lists.  We return the first list in x which
;; is a subset of a, or nil if none exists.

(defund find-subset (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (subsetp (car x) a)
          (car x)
        (find-subset a (cdr x)))
    nil))

(defthm find-subset-when-not-consp
  (implies (not (consp x))
           (equal (find-subset a x)
                  nil))
  :hints(("Goal" :in-theory (enable find-subset))))

(defthm find-subset-of-cons
  (equal (find-subset a (cons b x))
         (if (subsetp b a)
             b
           (find-subset a x)))
  :hints(("Goal" :in-theory (enable find-subset))))

(defthm find-subset-of-list-fix-one
  (equal (find-subset (list-fix a) x)
         (find-subset a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-subset-of-list-fix-two
  (equal (find-subset a (list-fix x))
         (find-subset a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-subset-of-rev-one
  (equal (find-subset (rev a) x)
         (find-subset a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-find-subset
  (equal (subsetp (find-subset a x) a)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-find-subset
  (equal (memberp (find-subset a x) x)
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-when-find-subset
  (implies (find-subset a x)
           (equal (superset-of-somep a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-subset-of-app
  (equal (find-subset a (app x y))
         (if (memberp (find-subset a x) x)
             (find-subset a x)
           (find-subset a y)))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm find-subset-when-subsetp-two
  (implies (and (memberp (find-subset a x) x)
                (subsetp x y))
           (equal (memberp (find-subset a y) y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-when-subsetp-two
  (implies (and (superset-of-somep a x)
                (subsetp x y))
           (equal (superset-of-somep a y)
                  t))
  :hints(("Goal"
          :in-theory (disable superset-of-somep-when-obvious
                              superset-of-somep-when-obvious-alt)
          :use ((:instance superset-of-somep-when-obvious
                           (a a)
                           (e (find-subset a x))
                           (x y))))))

(defthm superset-of-somep-when-subsetp-two-alt
  (implies (and (subsetp x y)
                (superset-of-somep a x))
           (equal (superset-of-somep a y)
                  t)))

(defthm superset-of-somep-when-superset-of-somep-of-smaller
  (implies (and (superset-of-somep sub x)
                (subsetp sub sup))
           (equal (superset-of-somep sup x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-when-superset-of-somep-of-smaller-alt
  (implies (and (subsetp sub sup)
                (superset-of-somep sub x))
           (equal (superset-of-somep sup x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(deflist all-superset-of-somep (x ys)
  (superset-of-somep x ys))

(defthm all-superset-of-somep-of-list-fix-two
  (equal (all-superset-of-somep x (list-fix y))
         (all-superset-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-cons-two
  (implies (all-superset-of-somep x y)
           (all-superset-of-somep x (cons a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-all-two
  (implies (all-superset-of-somep x y)
           (all-superset-of-somep x (app y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-all-two-alt
  (implies (all-superset-of-somep x y)
           (all-superset-of-somep x (app z y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-rev-two
  (equal (all-superset-of-somep x (rev y))
         (all-superset-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-when-subsetp-two
  (implies (and (all-superset-of-somep x y)
                (subsetp y z))
           (all-superset-of-somep x z))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-when-subsetp-two-alt
  (implies (and (subsetp y z)
                (all-superset-of-somep x y))
           (all-superset-of-somep x z))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-cons-two-when-irrelevant
  (implies (superset-of-somep a y)
           (equal (all-superset-of-somep x (cons a y))
                  (all-superset-of-somep x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-app-two-when-irrelevant
  ;; BOZO add similar rule for (app z y)?
  (implies (all-superset-of-somep y z)
           (equal (all-superset-of-somep x (app y z))
                  (all-superset-of-somep x z)))
  :hints(("Goal" :induct (cdr-induction y))))

(defthm superset-of-somep-when-all-superset-of-somep
  (implies (and (superset-of-somep a x)
                (all-superset-of-somep x y))
           (equal (superset-of-somep a y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm superset-of-somep-when-all-superset-of-somep-alt
  (implies (and (all-superset-of-somep x y)
                (superset-of-somep a x))
           (equal (superset-of-somep a y)
                  t)))

(defthm all-superset-of-somep-is-reflexive
  (equal (all-superset-of-somep x x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-is-transitive
  (implies (and (all-superset-of-somep x y)
                (all-superset-of-somep y z))
           (equal (all-superset-of-somep x z)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-remove-duplicates-list
  (equal (all-superset-of-somep x (remove-duplicates-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-remove-duplicates-list-gen
  (implies (all-superset-of-somep x y)
           (equal (all-superset-of-somep x (remove-duplicates-list y))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))





;; (remove-supersets1 todo done)
;;
;; Let todo = [t1, ..., tn] and done = [d1, ..., dn].  We produce a list
;; whose members are:
;;
;;   (1) every member of [d1, ..., dn]
;;   (2) every member of [t1, ..., tn] that is not a superset of any other
;;       ti or di.
;;
;; To do this, we just look at t1, and check if it is a superset of any di
;; or any tj in [t2, ..., tn].  If so, we throw it out and keep going.
;; Else, we push it onto the done list and keep going.
;;
;; Note: This is an O(n^4) operation since superset-of-somep is O(n^3).

(defund remove-supersets1 (todo done)
  (declare (xargs :guard t))
  (if (consp todo)
      (let ((candidate (car todo))
            (remaining (cdr todo)))
        (if (or (superset-of-somep candidate remaining)
                (superset-of-somep candidate done))
            ;; It's a superset of something else; drop it.
            (remove-supersets1 remaining done)
          ;; Not a superset; keep it.
          (remove-supersets1 remaining (cons candidate done))))
    (fast-rev done)))

(defthm remove-supersets1-when-not-consp
  (implies (not (consp x))
           (equal (remove-supersets1 x done)
                  (fast-rev done)))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm remove-supersets1-of-cons
  (equal (remove-supersets1 (cons a x) done)
         (if (or (superset-of-somep a x)
                 (superset-of-somep a done))
             (remove-supersets1 x done)
           (remove-supersets1 x (cons a done))))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm true-listp-of-remove-supersets1
  (equal (true-listp (remove-supersets1 x done))
         t)
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm uniquep-of-remove-supersets1
  (implies (uniquep done)
           (uniquep (remove-supersets1 todo done)))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm all-superset-of-somep-of-remove-supersets1
  (equal (all-superset-of-somep x (remove-supersets1 todo done))
         (all-superset-of-somep x (app todo done)))
  :hints(("Goal"
          :in-theory (enable remove-supersets1)
          :induct (remove-supersets1 todo done))))

(defthm cons-listp-when-not-superset-of-some-is-non-consp
  (implies (and (superset-of-somep a x)
                (not (consp a)))
           (equal (cons-listp x)
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-remove-supersets1
  (equal (cons-listp (remove-supersets1 todo done))
         (and (cons-listp todo)
              (cons-listp done)))
  :hints(("Goal" :in-theory (enable remove-supersets1))))



;; (remove-supersets x)
;;
;; We walk through [x1, ..., xn] and remove any xi which is a superset of xj,
;; where i != j.

(defund remove-supersets (x)
  (declare (xargs :guard t))
  (remove-supersets1 x nil))

(defthm true-listp-of-remove-supersets
  (equal (true-listp (remove-supersets x))
         t)
  :hints(("Goal" :in-theory (enable remove-supersets))))

(defthm all-superset-of-somep-of-remove-supersets
  (equal (all-superset-of-somep x (remove-supersets x))
         t)
  :hints(("Goal" :in-theory (enable remove-supersets))))

(defthm all-superset-of-somep-of-remove-supersets-gen
  (implies (all-superset-of-somep x y)
           (equal (all-superset-of-somep x (remove-supersets y))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-remove-supersets
  (equal (cons-listp (remove-supersets x))
         (cons-listp x))
  :hints(("Goal" :in-theory (enable remove-supersets))))










;; (subset-of-somep a x)
;;
;; Return true if a is a subset of some b in x.  Note: this is an O(n^3)
;; operation since subsetp testing is quadratic.

(defund subset-of-somep (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (or (subsetp a (car x))
          (subset-of-somep a (cdr x)))
    nil))

(defthm subset-of-somep-when-not-consp
  (implies (not (consp x))
           (equal (subset-of-somep a x)
                  nil))
  :hints(("Goal" :expand (subset-of-somep a x))))

(defthm subset-of-somep-of-cons
  (equal (subset-of-somep a (cons b x))
         (or (subsetp a b)
             (subset-of-somep a x)))
  :hints(("Goal" :expand (subset-of-somep a (cons b x)))))

(defthm booleanp-of-subset-of-somep
  (equal (booleanp (subset-of-somep a x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-of-list-fix-one
  (equal (subset-of-somep (list-fix a) x)
         (subset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-of-list-fix-two
  (equal (subset-of-somep a (list-fix x))
         (subset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-of-app
  (equal (subset-of-somep a (app x y))
         (or (subset-of-somep a x)
             (subset-of-somep a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-of-rev
  (equal (subset-of-somep a (rev x))
         (subset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-when-not-subset-of-somep-cheap
  (implies (not (subset-of-somep a x))
           (equal (memberp a x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-when-obvious
  (implies (and (subsetp a e)
                (memberp e x))
           (equal (subset-of-somep a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-when-obvious-alt
  (implies (and (memberp e x)
                (subsetp a e))
           (equal (subset-of-somep a x)
                  t)))




;; (find-superset a x)
;;
;; A is a list and X is a list of lists.  We return the first list in x which
;; is a superset of a, or nil if none exists.

(defund find-superset (a x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (subsetp a (car x))
          (car x)
        (find-superset a (cdr x)))
    nil))

(defthm find-superset-when-not-consp
  (implies (not (consp x))
           (equal (find-superset a x)
                  nil))
  :hints(("Goal" :in-theory (enable find-superset))))

(defthm find-superset-of-cons
  (equal (find-superset a (cons b x))
         (if (subsetp a b)
             b
           (find-superset a x)))
  :hints(("Goal" :in-theory (enable find-superset))))

(defthm find-superset-of-list-fix-one
  (equal (find-superset (list-fix a) x)
         (find-superset a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-superset-of-list-fix-two
  (equal (find-superset a (list-fix x))
         (find-superset a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-superset-of-rev-one
  (equal (find-superset (rev a) x)
         (find-superset a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subsetp-of-find-superset
  (implies (subset-of-somep a x)
           (equal (subsetp a (find-superset a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-find-superset
  (implies (subset-of-somep a x)
           (equal (memberp (find-superset a x) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-when-find-superset
  (implies (find-superset a x)
           (equal (subset-of-somep a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-superset-when-subsetp-two
  (implies (and (memberp (find-superset a x) x)
                (subsetp x y)
                (subset-of-somep a x))
           (equal (memberp (find-superset a y) y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-when-subsetp-two
  (implies (and (subset-of-somep a x)
                (subsetp x y))
           (equal (subset-of-somep a y)
                  t))
  :hints(("Goal"
          :in-theory (disable subset-of-somep-when-obvious
                              subset-of-somep-when-obvious-alt)
          :use ((:instance subset-of-somep-when-obvious
                           (a a)
                           (e (find-superset a x))
                           (x y))))))

(defthm subset-of-somep-when-subsetp-two-alt
  (implies (and (subsetp x y)
                (subset-of-somep a x))
           (equal (subset-of-somep a y)
                  t)))

(defthm subset-of-somep-when-subset-of-somep-of-smaller
  (implies (and (subset-of-somep a x)
                (subsetp b a))
           (equal (subset-of-somep b x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-when-subset-of-somep-of-smaller-alt
  (implies (and (subsetp b a)
                (subset-of-somep a x))
           (equal (subset-of-somep b x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(deflist all-subset-of-somep (x ys)
  (subset-of-somep x ys))

(defthm all-subset-of-somep-of-list-fix-two
  (equal (all-subset-of-somep x (list-fix y))
         (all-subset-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-cons-two
  (implies (all-subset-of-somep x y)
           (all-subset-of-somep x (cons a y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-all-two
  (implies (all-subset-of-somep x y)
           (all-subset-of-somep x (app y z)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-all-two-alt
  (implies (all-subset-of-somep x y)
           (all-subset-of-somep x (app z y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-rev-two
  (equal (all-subset-of-somep x (rev y))
         (all-subset-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-when-subsetp-two
  (implies (and (all-subset-of-somep x y)
                (subsetp y z))
           (all-subset-of-somep x z))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-when-subsetp-two-alt
  (implies (and (subsetp y z)
                (all-subset-of-somep x y))
           (all-subset-of-somep x z))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-cons-two-when-irrelevant
  (implies (subset-of-somep a y)
           (equal (all-subset-of-somep x (cons a y))
                  (all-subset-of-somep x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-app-two-when-irrelevant
  ;; BOZO add similar rule for (app z y)?
  (implies (all-subset-of-somep y z)
           (equal (all-subset-of-somep x (app y z))
                  (all-subset-of-somep x z)))
  :hints(("Goal" :induct (cdr-induction y))))

(defthm subset-of-somep-when-all-subset-of-somep
  (implies (and (subset-of-somep a x)
                (all-subset-of-somep x y))
           (equal (subset-of-somep a y)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm subset-of-somep-when-all-subset-of-somep-alt
  (implies (and (all-subset-of-somep x y)
                (subset-of-somep a x))
           (equal (subset-of-somep a y)
                  t)))

(defthm all-subset-of-somep-is-reflexive
  (equal (all-subset-of-somep x x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-is-transitive
  (implies (and (all-subset-of-somep x y)
                (all-subset-of-somep y z))
           (equal (all-subset-of-somep x z)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-remove-duplicates-list
  (equal (all-subset-of-somep x (remove-duplicates-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-remove-duplicates-list-gen
  (implies (all-subset-of-somep x y)
           (equal (all-subset-of-somep x (remove-duplicates-list y))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))
