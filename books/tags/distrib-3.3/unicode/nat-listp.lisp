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

(include-book "app")

(defund nat-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (natp (car x))
           (nat-listp (cdr x)))
    t))

(defthm nat-listp-when-not-consp
  (implies (not (consp x))
           (nat-listp x))
  :hints(("Goal" :in-theory (enable nat-listp))))

(defthm nat-listp-of-cons
  (equal (nat-listp (cons a x))
         (and (natp a)
              (nat-listp x)))
  :hints(("Goal" :in-theory (enable nat-listp))))

(defthm nat-listp-of-list-fix
  (equal (nat-listp (list-fix x))
         (nat-listp x))
  :hints(("Goal" :induct (len x))))

(defthm nat-listp-of-app
  (equal (nat-listp (app x y))
         (and (nat-listp x)
              (nat-listp y)))
  :hints(("Goal" :induct (len x))))

(defthm natp-of-car-when-nat-listp
  (implies (nat-listp x)
           (and (equal (integerp (car x))
                       (consp x))
                (<= 0 (car x))))
  :hints(("Goal" :induct (len x))))

(defthm nat-listp-of-cdr-when-nat-listp
  (implies (nat-listp x)
           (nat-listp (cdr x))))