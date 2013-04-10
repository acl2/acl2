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
(local (include-book "../lists/sets"))
(local (include-book "../lists/take"))
(local (include-book "../lists/repeat"))
(local (include-book "../lists/nthcdr"))
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable strip-cdrs)))

(defthm strip-cdrs-when-atom
  (implies (atom x)
           (equal (strip-cdrs x)
                  nil)))

(defthm strip-cdrs-of-cons
  (equal (strip-cdrs (cons a x))
         (cons (cdr a)
               (strip-cdrs x))))

(defthm len-of-strip-cdrs
   (equal (len (strip-cdrs x))
          (len x)))

(defthm consp-of-strip-cdrs
  (equal (consp (strip-cdrs x))
         (consp x)))

(defthm car-of-strip-cdrs
  (equal (car (strip-cdrs x))
         (cdr (car x))))

(defthm cdr-of-strip-cdrs
  (equal (cdr (strip-cdrs x))
         (strip-cdrs (cdr x))))

(defthm strip-cdrs-under-iff
  (iff (strip-cdrs x)
       (consp x)))

(defthm strip-cdrs-of-list-fix
  (equal (strip-cdrs (list-fix x))
         (strip-cdrs x))
  :hints(("Goal" :in-theory (enable list-fix))))

(defcong list-equiv equal (strip-cdrs x) 1
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (strip-cdrs-of-list-fix))
          :use ((:instance strip-cdrs-of-list-fix (x x))
                (:instance strip-cdrs-of-list-fix (x x-equiv))))))

(encapsulate
  ()
  (local (defthm l1
           (implies (and (member-equal a x)
                         (not (consp a)))
                    (member-equal nil (strip-cdrs x)))))

  (local (defthm l2
           (implies (member-equal (cons a b) x)
                    (member-equal b (strip-cdrs x)))))

  (local (defthm l3
           (implies (and (subsetp x y)
                         (member a x))
                    (member (cdr a) (strip-cdrs y)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm l4
           (implies (subsetp x y)
                    (subsetp (strip-cdrs x) (strip-cdrs y)))
           :hints(("Goal" :induct (len x)))))

  (defcong set-equiv set-equiv (strip-cdrs x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))

(defthm strip-cdrs-of-append
  (equal (strip-cdrs (append x y))
         (append (strip-cdrs x)
                 (strip-cdrs y))))

(defthm strip-cdrs-of-rev
  (equal (strip-cdrs (rev x))
         (rev (strip-cdrs x))))

(defthm strip-cdrs-of-revappend
  (equal (strip-cdrs (revappend x y))
         (revappend (strip-cdrs x)
                    (strip-cdrs y))))

(defthm strip-cdrs-of-repeat
  (equal (strip-cdrs (repeat x n))
         (repeat (cdr x) n))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm strip-cdrs-of-take
  (equal (strip-cdrs (take n x))
         (take n (strip-cdrs x))))

(defthm strip-cdrs-of-nthcdr
  (equal (strip-cdrs (nthcdr n x))
         (nthcdr n (strip-cdrs x))))

(defthm strip-cdrs-of-last
  (equal (strip-cdrs (last x))
         (last (strip-cdrs x))))

(defthm strip-cdrs-of-butlast
  (equal (strip-cdrs (butlast x n))
         (butlast (strip-cdrs x) n)))

(defthm strip-cdrs-of-pairlis$
  (equal (strip-cdrs (pairlis$ x y))
         (if (<= (len x) (len y))
             (take (len x) y)
           (append y (repeat nil (- (len x) (len y))))))
  :hints(("Goal"
          :induct (pairlis$ x y)
          :in-theory (enable repeat))))

