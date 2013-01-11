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

(include-book "std/lists/nat-listp" :dir :system)

(defund sum-list (x)
  (declare (xargs :guard (nat-listp x)))
  (if (consp x)
      (+ (car x)
         (sum-list (cdr x)))
    0))

(defthm sum-list-when-not-consp
  (implies (not (consp x))
           (equal (sum-list x)
                  0))
  :hints(("Goal" :in-theory (enable sum-list))))

(defthm sum-list-of-cons
  (equal (sum-list (cons a x))
         (+ a (sum-list x)))
  :hints(("Goal" :in-theory (enable sum-list))))

(defthm sum-list-of-list-fix
  (equal (sum-list (list-fix x))
         (sum-list x))
  :hints(("Goal" :induct (len x))))

(defthm sum-list-of-app
  (equal (sum-list (app x y))
         (+ (sum-list x)
            (sum-list y)))
  :hints(("Goal" :induct (len x))))

(defthm natp-of-sum-list-when-nat-listp
  (implies (nat-listp x)
           (and (integerp (sum-list x))
                (<= 0 (sum-list x))))
  :hints(("Goal" :induct (len x))))

(defthm natp-of-sum-list-when-nat-listp-linear
  (implies (nat-listp x)
           (<= 0 (sum-list x)))
  :rule-classes :linear)
