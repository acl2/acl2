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
(local (include-book "nthcdr"))


(defund binary-app (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (binary-app (cdr x) y))
    (list-fix y)))

(defmacro app (x y &rest rst)
  (xxxjoin 'binary-app (list* x y rst)))

(add-macro-alias app binary-app)

(defthm app-when-not-consp
  (implies (not (consp x))
           (equal (app x y)
                  (list-fix y)))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-cons
  (equal (app (cons a x) y)
         (cons a (app x y)))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-list-fix-one
  (equal (app (list-fix x) y)
         (app x y))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-list-fix-two
  (equal (app x (list-fix y))
         (app x y))
  :hints(("Goal" :in-theory (enable app))))

(defthm app-of-app
  (equal (app (app x y) z)
         (app x (app y z)))
  :hints(("Goal" :induct (len x))))

(defthm true-listp-of-app
  (equal (true-listp (app x y))
         t)
  :hints(("Goal" :induct (len x))))

(defthm consp-of-app
  (equal (consp (app x y))
         (or (consp x)
             (consp y)))
  :hints(("Goal" :induct (len x))))

(defthm app-under-iff
  (iff (app x y)
       (or (consp x)
           (consp y)))
  :hints(("Goal" :induct (len x))))

(defthm len-of-app
  (equal (len (app x y))
         (+ (len x)
            (len y)))
  :hints(("Goal" :induct (len x))))

(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(defthm nth-of-app
  (implies (and (integerp n)
                (<= 0 n))
           (equal (nth n (app x y))
                  (if (< n (len x))
                      (nth n x)
                    (nth (- n (len x)) y))))
  :hints(("Goal"
          :in-theory (enable nth)
          :induct (nth n x))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (< n (len x))
                   (equal (app (simpler-take n x)
                               (nthcdr n x))
                          (list-fix x)))
          :hints(("Goal" :in-theory (enable simpler-take nthcdr)))))

 (local (defthm lemma2
          (implies (and (natp n)
                        (<= (len x) n))
                   (equal (app (simpler-take n x) (nthcdr n x))
                          (simpler-take n x)))
          :hints(("Goal" :in-theory (enable simpler-take nthcdr)))))

 (defthm app-of-take-and-nthcdr
   (equal (app (simpler-take n x) (nthcdr n x))
          (if (< (nfix n) (len x))
              (list-fix x)
            (simpler-take n x)))
   :hints(("Goal" :in-theory (enable simpler-take nthcdr)))))

(defthm append-to-app
  (implies (true-listp y)
           (equal (append x y)
                  (app x y))))

(defthm car-of-app
  (equal (car (app a x))
         (if (consp a)
             (car a)
           (car x))))

(defthm simpler-take-of-len-from-app
  (equal (simpler-take (len x) (app x y))
         (list-fix x))
  :hints(("Goal"
          :in-theory (enable simpler-take)
          :induct (len x))))

(defthm take-of-len-from-app
  (equal (take (len x) (app x y))
         (list-fix x)))

(defthm nthcdr-of-len-from-app
  (equal (nthcdr (len x) (app x y))
         (list-fix y))
  :hints(("Goal"
          :induct (len x)
          :in-theory (disable prefer-positive-addends-<))))
