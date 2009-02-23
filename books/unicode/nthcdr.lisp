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

(encapsulate
 ()
 (local (include-book "arithmetic-3/bind-free/top" :dir :system))

 (defthm nthcdr-of-non-consp
   (implies (not (consp x))
            (equal (nthcdr n x)
                   (if (zp n)
                       x
                     nil)))
   :hints (("Goal" :in-theory (enable nthcdr))))

 (defthm consp-of-nthcdr
   (equal (consp (nthcdr n l))
          (< (nfix n) (len l)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

;; arithmetic-3 loops??
(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (if (natp n)
             (max 0 (- (len l) n))
           (len l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-1
  (equal (nthcdr 1 x)
         (cdr x)))

(defthm nthcdr-of-2
  (equal (nthcdr 2 x)
         (cddr x)))

(defthm nthcdr-of-3
  (equal (nthcdr 3 x)
         (cdddr x)))

(defthm nthcdr-of-4
  (equal (nthcdr 4 x)
         (cddddr x)))

(local (defthm acl2-count-of-cdr
         (implies (consp x)
                  (< (acl2-count (cdr x))
                     (acl2-count x)))
         :rule-classes :linear))

(local (defthm acl2-count-of-cdr-weak
         (<= (acl2-count (cdr x))
             (acl2-count x))
         :rule-classes :linear))

(local (defthm acl2-count-of-consp-positive
         (implies (consp x)
                  (< 0 (acl2-count x)))
         :rule-classes :linear))

(defthm acl2-count-of-nthcdr-rewrite
  (equal (< (acl2-count (nthcdr n x))
            (acl2-count x))
         (if (zp n)
             nil
           (or (consp x)
               (< 0 (acl2-count x))))))
           
(defthm acl2-count-of-nthcdr-linear
  (implies (and (not (zp n))
                (consp x))
           (< (acl2-count (nthcdr n x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-of-nthcdr-linear-weak
  (<= (acl2-count (nthcdr n x))
      (acl2-count x))
  :rule-classes :linear)

(defthm car-of-nthcdr
  (equal (car (nthcdr i x)) (nth i x)))

(defthm nthcdr-of-cdr
  (equal (nthcdr i (cdr x))
         (cdr (nthcdr i x))))

(defthm nthcdr-when-less-than-len-under-iff
  (implies (< (nfix n) (len x))
           (iff (nthcdr n x) t)))