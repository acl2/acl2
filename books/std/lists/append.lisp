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
(local (include-book "arithmetic/top" :dir :system))

(local (defthm len-when-consp
         (implies (consp x)
                  (< 0 (len x)))
         :rule-classes ((:linear) (:rewrite))))

(defthm append-when-not-consp
  (implies (not (consp x))
           (equal (append x y)
                  y)))

(defthm append-of-cons
  (equal (append (cons a x) y)
         (cons a (append x y))))

(defthm true-listp-of-append
  (equal (true-listp (append x y))
         (true-listp y)))

(defthm consp-of-append
  (equal (consp (append x y))
         (or (consp x)
             (consp y))))

(defthm append-under-iff
  (iff (append x y)
       (or (consp x)
           y)))

(defthm len-of-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm nth-of-append
  (equal (nth n (append x y))
         (if (< (nfix n) (len x))
             (nth n x)
           (nth (- n (len x)) y))))

(defthm equal-when-append-same
  (equal (equal (append x y1)
                (append x y2))
         (equal y1 y2)))

(local (defthm append-nonempty-list
         (implies (consp x)
                  (not (equal (append x y) y)))
         :hints(("Goal" :use ((:instance len (x (append x y)))
                              (:instance len (x y)))))))

(local (defun cdr-cdr-induction (a b)
         (declare (xargs :guard t))
         (if (and (consp a)
                  (consp b))
             (cdr-cdr-induction (cdr a) (cdr b))
           nil)))

(defthm equal-of-appends-when-true-listps
  (implies (and (true-listp x1)
                (true-listp x2))
           (equal (equal (append x1 y)
                         (append x2 y))
                  (equal x1 x2)))
  :hints(("Goal" :induct (cdr-cdr-induction x1 x2))))

(defthm append-of-nil
  (equal (append x nil)
         (list-fix x)))

(defthm car-of-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))

(defthm associativity-of-append
  (equal (append (append a b) c)
         (append a (append b c))))


;; BOZO this rule should really not be here
(defthm character-listp-of-append
  (implies (and (character-listp x)
                (character-listp y))
           (character-listp (append x y))))
