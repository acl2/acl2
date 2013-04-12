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
(include-book "../lists/list-defuns")
(local (include-book "../lists/sets"))
(local (include-book "../lists/take"))
(local (include-book "../lists/repeat"))
(local (include-book "../lists/nthcdr"))

(local (in-theory (enable strip-cars)))

(defthm strip-cars-when-atom
  (implies (atom x)
           (equal (strip-cars x)
                  nil)))

(defthm strip-cars-of-cons
  (equal (strip-cars (cons a x))
         (cons (car a)
               (strip-cars x))))

(defthm len-of-strip-cars
   (equal (len (strip-cars x))
          (len x)))

(defthm consp-of-strip-cars
  (equal (consp (strip-cars x))
         (consp x)))

(defthm car-of-strip-cars
  (equal (car (strip-cars x))
         (car (car x))))

(defthm cdr-of-strip-cars
  (equal (cdr (strip-cars x))
         (strip-cars (cdr x))))

(defthm strip-cars-under-iff
  (iff (strip-cars x)
       (consp x)))

(defthm strip-cars-of-list-fix
  (equal (strip-cars (list-fix x))
         (strip-cars x))
  :hints(("Goal" :in-theory (enable list-fix))))

(defcong list-equiv equal (strip-cars x) 1
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (strip-cars-of-list-fix))
          :use ((:instance strip-cars-of-list-fix (x x))
                (:instance strip-cars-of-list-fix (x x-equiv))))))

(encapsulate
  ()
  (local (defthm l1
           (implies (and (member-equal a x)
                         (not (consp a)))
                    (member-equal nil (strip-cars x)))))

  (local (defthm l2
           (implies (member-equal (cons a b) x)
                    (member-equal a (strip-cars x)))))

  (local (defthm l3
           (implies (and (subsetp x y)
                         (member a x))
                    (member (car a) (strip-cars y)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm l4
           (implies (subsetp x y)
                    (subsetp (strip-cars x) (strip-cars y)))
           :hints(("Goal" :induct (len x)))))

  (defcong set-equiv set-equiv (strip-cars x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))

(defthm strip-cars-of-append
  (equal (strip-cars (append x y))
         (append (strip-cars x)
                 (strip-cars y))))

(defthm strip-cars-of-rev
  (equal (strip-cars (rev x))
         (rev (strip-cars x))))

(defthm strip-cars-of-revappend
  (equal (strip-cars (revappend x y))
         (revappend (strip-cars x)
                    (strip-cars y))))

(defthm strip-cars-of-repeat
  (equal (strip-cars (repeat x n))
         (repeat (car x) n))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm strip-cars-of-take
  (equal (strip-cars (take n x))
         (take n (strip-cars x))))

(defthm strip-cars-of-nthcdr
  (equal (strip-cars (nthcdr n x))
         (nthcdr n (strip-cars x))))

(defthm strip-cars-of-last
  (equal (strip-cars (last x))
         (last (strip-cars x))))

(defthm strip-cars-of-butlast
  (equal (strip-cars (butlast x n))
         (butlast (strip-cars x) n)))

(defthm strip-cars-of-pairlis$
  (equal (strip-cars (pairlis$ x y))
         (list-fix x)))

