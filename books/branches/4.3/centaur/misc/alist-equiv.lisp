; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

; alist-equiv.lisp -- basic alist equivalence relations

(in-package "ACL2")
(include-book "misc/hons-help2" :dir :system)
(include-book "cutil/defsection" :dir :system)
(include-book "alist-defs")


(defsection alists-agree
  (local (in-theory (enable alists-agree)))

  (defthmd alists-agree-hons-assoc-equal
    (implies (and (alists-agree keys a b)
                  (member-equal x keys))
             (equal (hons-assoc-equal x b)
                    (hons-assoc-equal x a))))

  (defthm alists-agree-self
    (alists-agree keys a a))

  (defthmd alists-agree-sym
    (implies (alists-agree keys a b)
             (alists-agree keys b a)))

  (defund alists-disagree-witness (keys al1 al2)
    (and (consp keys)
         (if (not (equal (hons-get (car keys) al1)
                         (hons-get (car keys) al2)))
             (car keys)
           (alists-disagree-witness (cdr keys) al1 al2))))

  (defthmd alists-agree-iff-witness
    (iff (alists-agree keys al1 al2)
         (let ((x (alists-disagree-witness keys al1 al2)))
           (implies (member-equal x keys)
                    (equal (hons-assoc-equal x al1)
                           (hons-assoc-equal x al2)))))
    :hints (("goal" :in-theory (enable alists-disagree-witness))))

  (defthmd alists-agree-trans
    (implies (and (alists-agree keys x y)
                  (alists-agree keys y z))
             (alists-agree keys x z))))

(defsection alist-keys
  (local (in-theory (enable alist-keys)))
  (defthm alist-keys-when-atom
    (implies (atom x)
             (equal (alist-keys x)
                    nil)))

  (defthm alist-keys-of-cons
    (equal (alist-keys (cons a x))
           (if (consp a)
               (cons (car a) (alist-keys x))
             (alist-keys x))))

  (defthm true-listp-of-alist-keys
    (true-listp (alist-keys x))
    :rule-classes :type-prescription)

  (defthm alist-keys-of-hons-acons
    (equal (alist-keys (hons-acons key val x))
           (cons key (alist-keys x))))

  (defthm alist-keys-member-hons-assoc-equal
    (iff (member-equal x (alist-keys a))
         (hons-assoc-equal x a))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthmd hons-assoc-equal-iff-member-alist-keys
    (iff (hons-assoc-equal x a)
         (member-equal x (alist-keys a)))
    :hints (("goal" :in-theory (enable alist-keys-member-hons-assoc-equal))))

  (defthmd hons-assoc-equal-when-not-member-alist-keys
    (implies (not (member-equal x (alist-keys a)))
             (equal (hons-assoc-equal x a) nil))
    :hints (("goal" :in-theory (enable alist-keys-member-hons-assoc-equal))))

  (defthm alist-keys-append
    (equal (alist-keys (append a b))
           (append (alist-keys a) (alist-keys b)))))




(defsection sub-alistp

  (defund sub-alistp (a b)
    (alists-agree (alist-keys a) a b))

  (local (in-theory (enable sub-alistp)))

  (defthm sub-alistp-self
    (sub-alistp x x))

  (defthmd sub-alistp-hons-assoc-equal
    (implies (and (sub-alistp a b)
                  (hons-assoc-equal x a))
             (equal (hons-assoc-equal x a)
                    (hons-assoc-equal x b)))
    :hints(("Goal" :in-theory (enable alists-agree-hons-assoc-equal))))

  (defun not-sub-alistp-witness (a b)
    (alists-disagree-witness (alist-keys a) a b))

  (defthmd sub-alistp-iff-witness
    (iff (sub-alistp a b)
         (let ((x (not-sub-alistp-witness a b)))
           (implies (hons-assoc-equal x a)
                    (equal (hons-assoc-equal x a)
                           (hons-assoc-equal x b)))))
    :hints(("Goal" :in-theory (e/d (alists-agree-iff-witness)
                                   (alists-agree)))))

  (defthmd sub-alistp-when-witness
    (implies (let ((x (not-sub-alistp-witness a b)))
               (implies (hons-assoc-equal x a)
                        (equal (hons-assoc-equal x a)
                               (hons-assoc-equal x b))))
             (sub-alistp a b))
    :hints (("goal" :use sub-alistp-iff-witness)))


  (defthmd sub-alistp-trans
    (implies (and (sub-alistp x y)
                  (sub-alistp y z))
             (sub-alistp x z))
    :hints(("Goal" :in-theory (e/d (sub-alistp-when-witness)
                                   (sub-alistp
                                    not-sub-alistp-witness))
            :use ((:instance sub-alistp-hons-assoc-equal
                             (x (not-sub-alistp-witness x z))
                             (a x) (b y))
                  (:instance sub-alistp-hons-assoc-equal
                             (x (not-sub-alistp-witness x z))
                             (a y) (b z)))))))


(defsection alist-equiv

  (defund alist-equiv (a b)
    (and (sub-alistp a b)
         (sub-alistp b a)))

  (local (in-theory (enable alist-equiv alists-agree)))

  (defthmd alist-equiv-means-all-keys-agree
    (implies (alist-equiv x y)
             (alists-agree keys x y))
    :hints (("subgoal *1/3"
             :use ((:instance sub-alistp-hons-assoc-equal
                              (x (car keys)) (a x) (b y))
                   (:instance sub-alistp-hons-assoc-equal
                              (x (car keys)) (a y) (b x))))))

  (defequiv alist-equiv
    :hints(("Goal" :in-theory (enable sub-alistp-trans))))


  (defcong alist-equiv equal (hons-assoc-equal x a) 2
    :hints (("goal" :use ((:instance alist-equiv-means-all-keys-agree
                                     (keys (list x)) (x a) (y a-equiv)))
             :in-theory (e/d (alists-agree)
                             (alist-equiv-means-all-keys-agree)))))



  (defchoose alist-equiv-bad-guy (bg) (al1 al2)
    (not (equal (hons-assoc-equal bg al1)
                (hons-assoc-equal bg al2))))

  (defthmd alists-agree-when-agree-on-alist-equiv-bad-guy
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (alists-agree keys al1 al2))
    :hints(("Goal" :in-theory (enable alists-agree)
            :induct (len keys))
           ("Subgoal *1/1"
            :use ((:instance alist-equiv-bad-guy
                             (bg (car keys)))))))

  (defthmd alists-agree-when-agree-on-alist-equiv-bad-guy1
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (alists-agree keys al2 al1))
    :hints(("Goal" :in-theory (enable alists-agree)
            :induct (len keys))
           ("Subgoal *1/1"
            :use ((:instance alist-equiv-bad-guy
                             (bg (car keys)))))))

  (defthmd sub-alistp-when-agree-on-alist-equiv-bad-guy
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (sub-alistp al1 al2))
    :hints(("Goal" :in-theory
            (enable sub-alistp
                    alists-agree-when-agree-on-alist-equiv-bad-guy))))

  (defthmd sub-alistp-when-agree-on-alist-equiv-bad-guy1
    (implies (let ((bg (alist-equiv-bad-guy al2 al1)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (sub-alistp al1 al2))
    :hints(("Goal" :in-theory
            (enable sub-alistp
                    alists-agree-when-agree-on-alist-equiv-bad-guy1))))

  (defthmd alist-equiv-when-agree-on-bad-guy
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (equal (alist-equiv al1 al2) t))
    :hints(("Goal" :in-theory
            (enable alist-equiv
                    sub-alistp-when-agree-on-alist-equiv-bad-guy
                    sub-alistp-when-agree-on-alist-equiv-bad-guy1))))

  (defthmd alist-equiv-iff-agree-on-bad-guy
    (iff (alist-equiv al1 al2)
         (let ((bg (alist-equiv-bad-guy al1 al2)))
           (equal (hons-assoc-equal bg al1)
                  (hons-assoc-equal bg al2))))
    :hints (("goal" :in-theory (e/d (alist-equiv-when-agree-on-bad-guy
                                     sub-alistp-hons-assoc-equal)
                                    (alist-equiv)))))

  (defcong alist-equiv alist-equiv (cons a b) 2
    :hints (("goal" :in-theory (e/d (alist-equiv-when-agree-on-bad-guy)
                                    (alist-equiv))))))



(defsection alist-vals

  (local (in-theory (enable alist-vals)))

  (defthm alist-vals-when-atom
    (implies (atom x)
             (equal (alist-vals x)
                    nil)))

  (defthm alist-vals-of-cons
    (equal (alist-vals (cons a x))
           (if (consp a)
               (cons (cdr a) (alist-vals x))
             (alist-vals x))))

  (defthm true-listp-of-alist-vals
    (true-listp (alist-vals x))
    :rule-classes :type-prescription)

  (defthm alist-vals-of-hons-acons
    (equal (alist-vals (hons-acons key val x))
           (cons val (alist-vals x))))

  (defthm alist-vals-pairlis$
    (implies (equal (len keys) (len vals))
             (equal (alist-vals (pairlis$ keys vals))
                    (append vals nil))))

  (defthm len-alist-vals
    (equal (len (alist-vals x))
           (len (alist-keys x)))
    :hints(("Goal" :in-theory (enable alist-keys alist-vals))))

  (defthm alist-vals-append
    (equal (alist-vals (append a b))
           (append (alist-vals a) (alist-vals b)))))



(defsection hons-rassoc-equal

  (defund hons-rassoc-equal (val map)
    (declare (xargs :guard t))
    (cond ((atom map)
           nil)
          ((and (consp (car map))
                (equal val (cdar map)))
           (car map))
          (t
           (hons-rassoc-equal val (cdr map)))))

  (local (in-theory (enable hons-rassoc-equal)))

  (defthm hons-rassoc-equal-when-atom
    (implies (atom map)
             (equal (hons-rassoc-equal val map)
                    nil)))

  (defthm hons-rassoc-equal-of-hons-acons
    (equal (hons-rassoc-equal a (cons (cons key b) map))
           (if (equal a b)
               (cons key b)
             (hons-rassoc-equal a map))))

  (defthm hons-rassoc-equal-type
    (or (not (hons-rassoc-equal val map))
        (consp (hons-rassoc-equal val map)))
    :rule-classes :type-prescription)

  (defthm consp-of-hons-rassoc-equal
    (equal (consp (hons-rassoc-equal val map))
           (if (hons-rassoc-equal val map)
               t
             nil)))

  (defthm cdr-of-hons-rassoc-equal
    (equal (cdr (hons-rassoc-equal val map))
           (if (hons-rassoc-equal val map)
               val
             nil))))



(defthm member-equal-of-alist-vals-under-iff
  (iff (member-equal val (alist-vals map))
       (hons-rassoc-equal val map))
  :hints(("Goal" :in-theory (enable hons-rassoc-equal alist-vals))))

(defthm hons-assoc-equal-of-car-when-hons-rassoc-equal
  (implies (hons-rassoc-equal val map)
           (hons-assoc-equal (car (hons-rassoc-equal val map)) map))
  :hints(("Goal" :in-theory (enable hons-assoc-equal hons-rassoc-equal))))

(defthm hons-assoc-equal-of-car-when-hons-rassoc-equal-and-no-duplicates
  (implies (and (no-duplicatesp-equal (alist-keys map))
                (hons-rassoc-equal val map))
           (equal (hons-assoc-equal (car (hons-rassoc-equal val map)) map)
                  (hons-rassoc-equal val map)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal hons-rassoc-equal))))

(defthm member-equal-of-car-when-hons-rassoc-equal
  (implies (hons-rassoc-equal val map)
           (member-equal (car (hons-rassoc-equal val map))
                         (alist-keys map))))


(defthm hons-rassoc-equal-of-cdr-when-hons-assoc-equal
  (implies (hons-assoc-equal key map)
           (hons-rassoc-equal (cdr (hons-assoc-equal key map)) map))
  :hints(("Goal" :in-theory (enable hons-assoc-equal hons-rassoc-equal))))

(defthm hons-rassoc-equal-of-cdr-when-hons-assoc-equal-and-no-duplicates
  (implies (and (no-duplicatesp-equal (alist-vals map))
                (hons-assoc-equal key map))
           (equal (hons-rassoc-equal (cdr (hons-assoc-equal key map)) map)
                  (hons-assoc-equal key map)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal hons-rassoc-equal))))

(defthm member-equal-of-cdr-when-hons-assoc-equal
  (implies (hons-assoc-equal key map)
           (member-equal (cdr (hons-assoc-equal key map))
                         (alist-vals map))))

(defthmd consp-hons-assoc-equal
  (iff (consp (hons-assoc-equal x y))
       (hons-assoc-equal x y)))



(defcong alist-equiv equal (alists-agree keys a b) 2
  :hints (("goal" :in-theory (enable alists-agree))))

(defcong alist-equiv equal (alists-agree keys a b) 3
  :hints (("goal" :in-theory (enable alists-agree))))
