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

(local (include-book "arithmetic/top" :dir :system))

(defund simpler-take (n xs)
  (declare (xargs :guard (and (natp n)
                              (true-listp xs))))
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take (1- n) (cdr xs)))))

(local (in-theory (enable simpler-take)))

(encapsulate
 ()
 (local (defthm equivalence-lemma
          (implies (true-listp acc)
                   (equal (first-n-ac n xs acc)
                          (revappend acc (simpler-take n xs))))))

 (defthm take-redefinition
   (equal (take n xs)
          (simpler-take n xs))
   :rule-classes :definition)

 (in-theory (disable (:definition take))))

(defthm consp-of-simpler-take
  (equal (consp (simpler-take n xs))
         (not (zp n))))

(defthm len-of-simpler-take
  (equal (len (simpler-take n xs))
         (nfix n)))

(defthm simpler-take-of-cons
  (equal (simpler-take n (cons a x))
         (if (zp n)
             nil
           (cons a (simpler-take (1- n) x)))))

(local (defun simpler-take-induction (n x)
         (declare (xargs :guard (natp n)))
         (if (zp n)
             (list n x)
           (if (consp x)
               (simpler-take-induction (1- n) (cdr x))
             (list n x)))))

(defthm simpler-take-of-append
  (equal (simpler-take n (append x y))
         (if (< (nfix n) (len x))
             (simpler-take n x)
           (append x (simpler-take (- n (len x)) y))))
  :hints(("Goal" :induct (simpler-take-induction n x))))

(defthm simpler-take-of-1
  (equal (simpler-take 1 x)
         (list (car x))))

(defthm car-of-simple-take
  (implies (<= 1 (nfix n))
           (equal (car (simpler-take n x))
                  (car x))))

(defthm second-of-simple-take
  (implies (<= 2 (nfix n))
           (equal (second (simpler-take n x))
                  (second x))))

(defthm third-of-simple-take
  (implies (<= 3 (nfix n))
           (equal (third (simpler-take n x))
                  (third x))))

(defthm fourth-of-simple-take
  (implies (<= 4 (nfix n))
           (equal (fourth (simpler-take n x))
                  (fourth x))))
