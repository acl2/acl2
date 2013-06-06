; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "alist-keys")
(local (include-book "std/lists/sets" :dir :system))

(defund alist-vals (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-vals (cdr x)))
        (t
         (cons (cdar x) (alist-vals (cdr x))))))

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

(encapsulate
  ()
  (local (defthmd l0
           (equal (alist-vals (list-fix x))
                  (alist-vals x))))

  (defcong list-equiv equal (alist-vals x) 1
    :hints(("Goal"
            :use ((:instance l0 (x x))
                  (:instance l0 (x acl2::x-equiv)))))))

(encapsulate
  ()
  (local (defthm l0
           (implies (member (cons a b) x)
                    (member b (alist-vals x)))))

  (local (defthm l1
           (implies (and (subsetp x y)
                         (member a (alist-vals x)))
                    (member a (alist-vals y)))))

  (local (defthm l2
           (implies (subsetp x y)
                    (subsetp (alist-vals x)
                             (alist-vals y)))))

  (defcong set-equiv set-equiv (alist-vals x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))

(defthm true-listp-of-alist-vals
  (true-listp (alist-vals x))
  :rule-classes :type-prescription)

(defthm alist-vals-of-hons-acons
  (equal (alist-vals (hons-acons key val x))
         (cons val (alist-vals x))))

(defthm alist-vals-of-pairlis$
  (implies (equal (len keys) (len vals))
           (equal (alist-vals (pairlis$ keys vals))
                  (list-fix vals))))

(defthm len-of-alist-vals
  (equal (len (alist-vals x))
         (len (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys alist-vals))))

(defthm alist-vals-of-append
  (equal (alist-vals (append x y))
         (append (alist-vals x)
                 (alist-vals y))))

(defthm alist-vals-of-rev
  (equal (alist-vals (rev x))
         (rev (alist-vals x))))

(defthm alist-vals-of-revappend
  (equal (alist-vals (revappend x y))
         (revappend (alist-vals x)
                    (alist-vals y))))

(defthm member-equal-of-cdr-when-hons-assoc-equal
  (implies (hons-assoc-equal key map)
           (member-equal (cdr (hons-assoc-equal key map))
                         (alist-vals map))))