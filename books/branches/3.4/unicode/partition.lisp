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

(include-book "flatten")
(include-book "sum-list")
(local (include-book "z-listp"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "nthcdr"))

(defund partition (sizes x)
  (declare (xargs :guard (and (nat-listp sizes)
                              (true-listp x))))
  (if (consp sizes)
      (cons (take (car sizes) x)
            (partition (cdr sizes) 
                       (nthcdr (car sizes) x)))
    nil))

(defthm partition-when-not-consp
  (implies (not (consp sizes))
           (equal (partition sizes x)
                  nil))
  :hints(("Goal" :in-theory (enable partition))))

(defthm partition-of-cons
  (equal (partition (cons size sizes) x)
         (cons (take size x)
               (partition sizes (nthcdr size x))))
  :hints(("Goal" :in-theory (enable partition))))

(defthm consp-of-partition-under-iff
  (equal (consp (partition sizes x))
         (if (partition sizes x) 
             t 
           nil))
  :hints(("Goal" :in-theory (enable partition))))

(local (defthm consless-listp-of-partition
         (equal (consless-listp (partition sizes x))
                (z-listp sizes))
         :hints(("Goal" :in-theory (enable partition)))))

(local (defthm sum-list-when-nat-listp-and-z-listp
         (implies (and (nat-listp x)
                       (z-listp x))
                  (equal (sum-list x)
                         0))
         :hints(("Goal" :induct (len x)))))

(local (defthm equal-of-simpler-take-and-list-fix
         (equal (equal (simpler-take n x) (list-fix x))
                (equal (nfix n) (len x)))))

(defthm flatten-of-partition
  (implies (and (nat-listp sizes)
                (equal (sum-list sizes) (len x)))
           (equal (flatten (partition sizes x))
                  (list-fix x)))
  :hints(("Goal" :in-theory (enable partition))))

(defthm len-of-car-of-partition
  (equal (len (car (partition sizes x)))
         (nfix (car sizes))))

