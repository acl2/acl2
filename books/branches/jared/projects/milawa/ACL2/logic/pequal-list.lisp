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


(defund logic.pequal-list (x y)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.term-listp y)
                              (equal (len x) (len y)))))
  (if (and (consp x)
           (consp y))
      (cons (logic.pequal (car x) (car y))
            (logic.pequal-list (cdr x) (cdr y)))
    nil))

(defthm logic.pequal-list-when-not-consp-one
  (implies (not (consp x))
           (equal (logic.pequal-list x y)
                  nil))
  :hints(("Goal" :in-theory (enable logic.pequal-list))))

(defthm logic.pequal-list-when-not-consp-two
  (implies (not (consp y))
           (equal (logic.pequal-list x y)
                  nil))
  :hints(("Goal" :in-theory (enable logic.pequal-list))))

(defthm logic.pequal-list-of-cons-and-cons
  (equal (logic.pequal-list (cons a x) (cons b y))
         (cons (logic.pequal a b)
               (logic.pequal-list x y)))
  :hints(("Goal" :in-theory (enable logic.pequal-list))))

(defthm logic.pequal-list-under-iff
  (iff (logic.pequal-list x y)
       (and (consp x)
            (consp y)))
  :hints(("Goal" :in-theory (enable logic.pequal-list))))

(defthm logic.pequal-list-of-list-fix-one
  (equal (logic.pequal-list (list-fix x) y)
         (logic.pequal-list x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm logic.pequal-list-of-list-fix-two
  (equal (logic.pequal-list x (list-fix y))
         (logic.pequal-list x y))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm true-listp-of-logic.pequal-list
  (equal (true-listp (logic.pequal-list x y))
         t)
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-logic.formulap-of-logic.pequal-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-listp y)))
           (equal (logic.formula-listp (logic.pequal-list x y))
                  t))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-logic.formula-atblp-of-logic.pequal-list
  (implies (and (force (logic.term-list-atblp x atbl))
                (force (logic.term-list-atblp y atbl)))
           (equal (logic.formula-list-atblp (logic.pequal-list x y) atbl)
                  t))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm consp-of-logic.pequal-list
  (equal (consp (logic.pequal-list x y))
         (and (consp x)
              (consp y))))

(defthm car-of-logic.pequal-list
  (equal (car (logic.pequal-list x y))
         (if (and (consp x)
                  (consp y))
             (logic.pequal (car x) (car y))
           nil))
  :hints(("Goal" :expand (logic.pequal-list x y))))

(defthm cdr-of-logic.pequal-list
  (equal (cdr (logic.pequal-list x y))
         (logic.pequal-list (cdr x) (cdr y))))

(defthm len-of-logic.pequal-list
  (equal (len (logic.pequal-list x y))
         (if (< (len x) (len y))
             (len x)
           (len y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm logic.pequal-list-of-cons-and-repeat-plus-one
  (equal (logic.pequal-list (cons a x) (repeat b (+ 1 n)))
         (cons (logic.pequal a b)
               (logic.pequal-list x (repeat b n)))))

(defthm equal-of-logic.pequal-list-and-logic.pequal-list
  (implies (force (and (logic.term-listp a)
                       (logic.term-listp b)
                       (logic.term-listp c)
                       (logic.term-listp d)
                       (equal (len a) (len b))
                       (equal (len c) (len d))))
           (equal (equal (logic.pequal-list a b)
                         (logic.pequal-list c d))
                  (and (equal (list-fix a) (list-fix c))
                       (equal (list-fix b) (list-fix d)))))
  :hints(("Goal" :induct (four-cdrs-induction a b c d))))

(defthm logic.pequal-list-of-app-and-app
  (implies (equal (len a) (len c))
           (equal (logic.pequal-list (app a b) (app c d))
                  (app (logic.pequal-list a c)
                       (logic.pequal-list b d))))
  :hints(("Goal" :induct (cdr-cdr-induction a c))))

(defthm rev-of-logic.pequal-list
  (implies (force (equal (len a) (len b)))
           (equal (rev (logic.pequal-list a b))
                  (logic.pequal-list (rev a) (rev b))))
  :hints(("Goal" :induct (cdr-cdr-induction a b))))




;; We call formulas of the form t1 = t2 atomic.  Given a list of atomic
;; formula, [t1 = s1, t2 = s2, ..., tn = sn], it is sometimes useful to
;; consider the lists of left and right hand sides.  That is, the lists [t1,
;; t2, ..., tn] and [s1, s2, ..., sn].  The functions logic.=lhses and
;; logic.=rhses will do this for us.

(deflist logic.all-atomicp (x)
  (equal (logic.fmtype x) 'pequal*)
  :elementp-of-nil nil
  :guard (logic.formula-listp x))

;; Some of the rules that are generated aren't very good because they're
;; for the general case; we replace them.
(in-theory (disable equal-of-car-when-logic.all-atomicp
                    equal-when-memberp-of-logic.all-atomicp
                    equal-when-memberp-of-logic.all-atomicp-alt))

(defthm logic.fmtype-of-car-when-logic.all-atomicp
  (implies (and (logic.all-atomicp x)
                (consp x))
           (equal (logic.fmtype (car x))
                  'pequal*)))

(defthm logic.fmtype-when-memberp-of-logic.all-atomicp
  (implies (and (memberp a x)
                (logic.all-atomicp x))
           (equal (logic.fmtype a)
                  'pequal*))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-when-memberp-of-logic.all-atomicp-alt
  (implies (and (logic.all-atomicp x)
                (memberp a x))
           (equal (logic.fmtype a)
                  'pequal*)))

(defthm forcing-logic.all-atomicp-of-logic.pequal-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-listp y)))
           (equal (logic.all-atomicp (logic.pequal-list x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.pequal-list))))

(defthm forcing-logic.all-atomicp-of-logic.pequal-list-free
  (implies (and (equal a (logic.pequal-list x y))
                (force (logic.term-listp x))
                (force (logic.term-listp y)))
           (equal (logic.all-atomicp a)
                  t)))

(defthm logic.fmtype-of-nth-when-logic.all-atomicp
  (implies (logic.all-atomicp x)
           (equal (logic.fmtype (nth n x))
                  (if (< (nfix n) (len x))
                      'pequal*
                    nil)))
  :hints(("Goal" :in-theory (enable nth))))




(defprojection :list (logic.=lhses x)
               :element (logic.=lhs x)
               :guard (and (logic.formula-listp x)
                           (logic.all-atomicp x))
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-logic.=lhses
  (implies (and (force (logic.formula-listp x))
                (force (logic.all-atomicp x)))
           (equal (logic.term-listp (logic.=lhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-logic.=lhses
  (implies (and (force (logic.formula-list-atblp x atbl))
                (force (logic.all-atomicp x)))
           (equal (logic.term-list-atblp (logic.=lhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.=lhses-of-logic.pequal-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-listp y))
                (force (equal (len x) (len y))))
           (equal (logic.=lhses (logic.pequal-list x y))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-logic.=lhses-of-logic.pequal-list-free
  (implies (and (equal a (logic.pequal-list x y))
                (force (logic.term-listp x))
                (force (logic.term-listp y))
                (force (equal (len x) (len y))))
           (equal (logic.=lhses a)
                  (list-fix x))))





(defprojection :list (logic.=rhses x)
               :element (logic.=rhs x)
               :guard (and (logic.formula-listp x)
                           (logic.all-atomicp x))
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-logic.=rhses
  (implies (and (force (logic.formula-listp x))
                (force (logic.all-atomicp x)))
           (equal (logic.term-listp (logic.=rhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-logic.=rhses
  (implies (and (force (logic.formula-list-atblp x atbl))
                (force (logic.all-atomicp x)))
           (equal (logic.term-list-atblp (logic.=rhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-logic.=rhses-free
  (implies (and (equal x (logic.=rhses y))
                (force (logic.formula-list-atblp y atbl))
                (force (logic.all-atomicp y)))
           (equal (logic.term-list-atblp x atbl)
                  t)))

(defthm forcing-logic.=rhses-of-logic.pequal-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-listp y))
                (force (equal (len x) (len y))))
           (equal (logic.=rhses (logic.pequal-list x y))
                  (list-fix y)))
  :hints(("Goal" :induct (cdr-cdr-induction x y))))

(defthm forcing-logic.=rhses-of-logic.pequal-list-free
  (implies (and (equal a (logic.pequal-list x y))
                (force (logic.term-listp x))
                (force (logic.term-listp y))
                (force (equal (len x) (len y))))
           (equal (logic.=rhses a)
                  (list-fix y))))

(defthm forcing-logic.pequal-list-of-logic.=lhses-and-logic.=rhses
  (implies (and (force (logic.formula-listp x))
                (force (logic.all-atomicp x)))
           (equal (logic.pequal-list (logic.=lhses x)
                                     (logic.=rhses x))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm forcing-equal-of-logic.pequal-list-rewrite
  (implies (and (force (equal (len x) (len y)))
                (force (logic.term-listp x))
                (force (logic.term-listp y)))
           (equal (equal (logic.pequal-list x y) z)
                  (and (true-listp z)
                       (logic.formula-listp z)
                       (logic.all-atomicp z)
                       (equal (list-fix x) (logic.=lhses z))
                       (equal (list-fix y) (logic.=rhses z)))))
  :hints(("Goal" :induct (cdr-cdr-cdr-induction x y z))))

(defthm logic.pequal-list-of-app-with-repeat
  (implies (and (force (equal n (+ (len x) (len y))))
                (force (logic.term-listp y))
                (force (logic.term-listp x))
                (force (logic.termp a)))
           (equal (logic.pequal-list (app x y) (repeat a n))
                  (app (logic.pequal-list x (repeat a (len x)))
                       (logic.pequal-list y (repeat a (len y))))))
  :hints(("Goal" :induct (cdr-induction x))))

