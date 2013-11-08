; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "misc/records" :dir :system)

; local.lisp -- supporting theorems to be only locally included

(in-theory (disable nth
                    update-nth
                    make-list-ac
                    (make-list-ac)))

(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc)))
  :hints(("Goal" :in-theory (enable make-list-ac))))

(defthm acl2-count-of-nth-weak
  (<= (acl2-count (nth n x))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable nth))))

(defthm acl2-count-of-nth-strong
  (implies (consp x)
           (< (acl2-count (nth n x))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable nth))))

(defthm true-listp-of-update-nth
  (implies (true-listp arr)
           (true-listp (update-nth n val arr))))

(defthm update-nth-switch
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n val1 (update-nth m val2 x))
                  (update-nth m val2 (update-nth n val1 x))))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm update-nth-of-nth
  (implies (and (natp n)
                (< n (len arr)))
           (equal (update-nth n (nth n arr) arr)
                  arr))
  :hints(("Goal" :in-theory (enable update-nth nth))))

(defthm update-nth-of-nth-other
  (implies (and (natp n)
                (< n (len arr))
                (natp m)
                (not (equal n m))
                (< m (len arr)))
           (equal (update-nth n (nth n arr)
                              (update-nth m val arr))
                  (update-nth m val arr))))

(defthm s-nil-nil
  (equal (s k nil nil)
         nil)
  :hints(("Goal" :in-theory (enable s acl2->rcd rcd->acl2))))

(defthm update-nth-same
  (implies (equal (nfix i) (nfix j))
           (equal (update-nth j b (update-nth i a l))
                  (update-nth j b l)))
  :hints(("Goal" :in-theory (enable update-nth))))

(defthm true-listp-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary
    (implies (true-listp ac)
             (true-listp (make-list-ac n val ac)))))
  :hints(("Goal" :in-theory (enable make-list-ac))))
