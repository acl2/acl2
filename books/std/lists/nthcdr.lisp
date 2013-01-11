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
 (local (defthmd lemma1
          (implies (true-listp x)
                   (true-listp (nthcdr n x)))
          :hints(("Goal" :in-theory (enable nthcdr)))))

 (local (defthmd lemma2
          (implies (< (len x) (nfix n))
                   (true-listp (nthcdr n x)))
          :hints(("Goal" :in-theory (enable nthcdr)))))

 (local (defthmd lemma3
          (implies (and (not (true-listp x))
                        (not (< (len x) (nfix n))))
                   (not (true-listp (nthcdr n x))))
          :hints(("Goal" :in-theory (enable nthcdr)))))

 (defthm true-listp-of-nthcdr
   (equal (true-listp (nthcdr n x))
          (or (true-listp x)
              (< (len x) (nfix n))))
   :rule-classes ((:rewrite)
                  (:type-prescription :corollary (implies (true-listp x)
                                                          (true-listp (nthcdr n x)))))
   :hints(("Goal"
           :in-theory (disable nthcdr)
           :use ((:instance lemma1)
                 (:instance lemma2)
                 (:instance lemma3))))))

(defthm nthcdr-when-not-natp
  (implies (not (natp n))
           (equal (nthcdr n x)
                  x)))

(defthm nthcdr-when-non-consp
   (implies (not (consp x))
            (equal (nthcdr n x)
                   (if (zp n)
                       x
                     nil)))
   :hints (("Goal" :in-theory (enable nthcdr))))

(local (defthm equal-len-0
         (equal (equal (len x) 0)
                (atom x))))

(encapsulate
 ()
 (local (defthmd l0
          (implies (< (nfix n) (len x))
                   (consp (nthcdr n x)))
          :hints(("Goal" :induct (nthcdr n x)))))

 (local (defthmd l1
          (implies (not (< (nfix n) (len x)))
                   (not (consp (nthcdr n x))))
          :hints(("goal" :induct (nthcdr n x)))))

 (defthm consp-of-nthcdr
   (equal (consp (nthcdr n x))
          (< (nfix n) (len x)))
   :hints(("Goal" :use ((:instance l0)
                        (:instance l1))))))

(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (nfix (- (len l) (nfix n))))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm open-small-nthcdr
  (implies (syntaxp (and (quotep n)
                         (natp (unquote n))
                         (< (unquote n) 5)))
           (equal (nthcdr n x)
                  (if (zp n)
                      x
                    (nthcdr (+ -1 n) (cdr x)))))
  :hints(("Goal" :in-theory (enable nthcdr))))

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
  (equal (car (nthcdr i x))
         (nth i x)))

(defthm nthcdr-of-cdr
  (equal (nthcdr i (cdr x))
         (cdr (nthcdr i x))))

(defthm nthcdr-when-less-than-len-under-iff
  (implies (< (nfix n) (len x))
           (iff (nthcdr n x)
                t)))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr a (nthcdr b x))
         (nthcdr (+ (nfix a) (nfix b)) x))
  :hints(("Goal" :induct (nthcdr b x))))
