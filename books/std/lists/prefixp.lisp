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
(include-book "list-fix")
(local (include-book "take"))
(local (include-book "arithmetic/top" :dir :system))

(defund prefixp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

(defthm prefixp-when-not-consp-left
  (implies (not (consp x))
           (prefixp x y))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-cons-left
  (equal (prefixp (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (prefixp x (cdr y))))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm prefixp-when-not-consp-right
  (implies (not (consp y))
           (equal (prefixp x y)
                  (not (consp x))))
  :hints(("Goal" :induct (len x))))

(defthm prefixp-of-cons-right
  (equal (prefixp x (cons a y))
         (if (consp x)
             (and (equal (car x) a)
                  (prefixp (cdr x) y))
           t)))

(defthm prefixp-of-list-fix-left
  (equal (prefixp (list-fix x) y)
         (prefixp x y))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-list-fix-right
  (equal (prefixp x (list-fix y))
         (prefixp x y))
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm len-when-prefixp
  (implies (prefixp x y)
           (equal (< (len y) (len x))
                  nil))
  :rule-classes ((:rewrite)
                 (:linear :corollary (implies (prefixp x y)
                                              (<= (len x) (len y)))))
  :hints(("Goal" :in-theory (enable (:induction prefixp)))))

(defthm take-when-prefixp
  (implies (prefixp x y)
           (equal (take (len x) y)
                  (list-fix x)))
  :hints(("Goal"
          :in-theory (enable (:induction prefixp)))))

