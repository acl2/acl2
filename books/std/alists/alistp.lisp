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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "../lists/list-defuns")
(local (include-book "../lists/append"))
(local (include-book "../lists/rev"))
(local (include-book "../lists/take"))
(local (include-book "../lists/repeat"))

(local (in-theory (enable alistp)))

(defthm alistp-when-atom
  (implies (atom x)
           (equal (alistp x)
                  (not x))))

(defthm alistp-of-cons
  (equal (alistp (cons a x))
         (and (consp a)
              (alistp x))))

(defthm true-listp-when-alistp
  (implies (alistp x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(defthm alistp-of-append
  (equal (alistp (append x y))
         (and (alistp (list-fix x))
              (alistp y))))

(defthm alistp-of-revappend
  (equal (alistp (revappend x y))
         (and (alistp (list-fix x))
              (alistp y))))

(defthm alistp-of-rev
  (equal (alistp (rev x))
         (alistp (list-fix x)))
  :hints(("Goal" :induct (len x))))

(defthm alistp-of-reverse
  (equal (alistp (reverse x))
         (and (not (stringp x))
              (alistp (list-fix x))))
  :hints(("Goal" :induct (len x))))

(defthm alistp-of-cdr
  (implies (alistp x)
           (alistp (cdr x))))

(defthm consp-of-car-when-alistp
  (implies (alistp x)
           (equal (consp (car x))
                  (if x t nil))))

(defthm alistp-of-member
  (implies (alistp x)
           (alistp (member a x))))

(defthm alistp-of-repeat
  (equal (alistp (repeat x n))
         (or (zp n)
             (consp x)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm alistp-of-take
  (implies (alistp x)
           (equal (alistp (take n x))
                  (<= (nfix n) (len x))))
  :hints(("Goal" :in-theory (enable take-redefinition))))

(defthm alistp-of-nthcdr
  (implies (alistp x)
           (alistp (nthcdr n x))))

(defthm alistp-of-delete-assoc-equal
  (implies (alistp x)
           (alistp (delete-assoc-equal key x))))

(defthm alistp-of-pairlis$
  (alistp (pairlis$ x y)))
