;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(local (include-book "take"))
(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(defund list-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (list-fix (cdr x)))
    nil))

(defund simpler-take (n xs)
  ;; Redundant from take.lisp
  (declare (xargs :guard (and (natp n)
                              (true-listp xs))))
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take (1- n) (cdr xs)))))

(defthm list-fix-when-not-consp
  (implies (not (consp x))
           (equal (list-fix x)
                  nil))
  :hints(("Goal" :in-theory (enable list-fix))))

(defthm list-fix-of-cons
  (equal (list-fix (cons a x))
         (cons a (list-fix x)))
  :hints(("Goal" :in-theory (enable list-fix))))

(defthm car-of-list-fix
  (equal (car (list-fix x))
         (car x)))

(defthm cdr-of-list-fix
  (equal (cdr (list-fix x))
         (list-fix (cdr x))))

(defthm list-fix-when-len-zero
  (implies (equal (len x) 0)
           (equal (list-fix x)
                  nil)))

(defthm true-listp-of-list-fix
  (true-listp (list-fix x)))

(defthm len-of-list-fix
  (equal (len (list-fix x))
         (len x)))

(defthm list-fix-when-true-listp
  (implies (true-listp x)
           (equal (list-fix x) x)))

(defthm list-fix-under-iff
  (iff (list-fix x)
       (consp x))
  :hints(("Goal" :induct (len x))))

(defthm consp-of-list-fix
  (equal (consp (list-fix x))
         (consp x))
  :hints(("Goal" :induct (len x))))

(defthm last-of-list-fix
  (equal (last (list-fix x))
         (list-fix (last x))))

(defthm simpler-take-of-list-fix
  (equal (simpler-take n (list-fix l))
         (simpler-take n l))
  :hints(("Goal" :in-theory (enable simpler-take))))

(defthm take-of-list-fix
  (equal (take n (list-fix l))
         (take n l)))

(defthm butlast-of-list-fix
  (equal (butlast (list-fix x) n)
         (butlast x n))
  :hints(("Goal" :in-theory (enable butlast))))

