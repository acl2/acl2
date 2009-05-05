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

(defund consless-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (consp (car x)))
           (consless-listp (cdr x)))
    t))

(defthm consless-listp-when-not-consp
  (implies (not (consp x))
           (consless-listp x))
  :hints(("Goal" :in-theory (enable consless-listp))))

(defthm consless-listp-of-cons
  (equal (consless-listp (cons a x))
         (and (not (consp a))
              (consless-listp x)))
  :hints(("Goal" :in-theory (enable consless-listp))))

(defthm consless-listp-of-list-fix
  (equal (consless-listp (list-fix x))
         (consless-listp x))
  :hints(("Goal" :induct (len x))))

(defthm consless-listp-of-app
  (equal (consless-listp (app x y))
         (and (consless-listp x)
              (consless-listp y)))
  :hints(("Goal" :induct (len x))))

(defthm consp-of-car-when-consless-listp
  (implies (consless-listp x)
           (equal (consp (car x))
                  nil))
  :hints(("Goal" :induct (len x))))

(defthm consless-listp-of-cdr-when-consless-listp
  (implies (consless-listp x)
           (consless-listp (cdr x))))  

