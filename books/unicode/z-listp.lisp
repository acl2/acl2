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

(defund z-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (if (integerp (car x))
               (<= (car x) 0)
             t)
           (z-listp (cdr x)))
    t))

(defthm z-listp-when-not-consp
  (implies (not (consp x))
           (z-listp x))
  :hints(("Goal" :in-theory (enable z-listp))))

(defthm z-listp-of-cons
  (equal (z-listp (cons a x))
         (and (zp a)
              (z-listp x)))
  :hints(("Goal" :in-theory (enable z-listp))))

(defthm z-listp-of-list-fix
  (equal (z-listp (list-fix x))
         (z-listp x))
  :hints(("Goal" :induct (len x))))

(defthm z-listp-of-app
  (equal (z-listp (app x y))
         (and (z-listp x)
              (z-listp y)))
  :hints(("Goal" :induct (len x))))

(defthm z-listp-of-cdr-when-z-listp
  (implies (z-listp x)
           (z-listp (cdr x))))

(defthm z-listp-forward-to-zp-of-car
  (implies (z-listp x)
           (zp (car x)))
  :rule-classes :forward-chaining
  :hints(("Goal" :induct (len x))))

