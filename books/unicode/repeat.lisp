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
(include-book "take")

(defund repeat (x n)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat x (- n 1))))
       :exec (make-list-ac n x nil)))

(defthm |(repeat x 0)|
  (equal (repeat x 0)
         nil)
  :hints(("Goal" :in-theory (enable repeat))))

(defthm repeat-under-iff
  (iff (repeat x n)
       (not (zp n)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm simpler-take-when-not-consp
  (implies (not (consp x))
           (equal (simpler-take n x)
                  (repeat nil n)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm len-of-repeat
  (equal (len (repeat x n))
         (nfix n))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm repeat-of-nfix
  (equal (repeat x (nfix n))
         (repeat x n))
  :hints(("Goal" :in-theory (enable repeat))))

(encapsulate
 ()
 (local (include-book "append"))

 (local (defun silly-repeat (x n acc)
          (if (zp n)
              acc
            (cons x (silly-repeat x (- n 1) acc)))))

 (local (defthm lemma1
          (equal (make-list-ac n x acc)
                 (silly-repeat x n acc))))

 (local (defthm lemma2
          (equal (silly-repeat x n acc)
                 (append (repeat x n) acc))
          :hints(("Goal"
                  :in-theory (enable repeat)))))

 (local (defthm main-lemma
          (equal (make-list-ac n x acc)
                 (append (repeat x n) 
                         acc))))
 
 (verify-guards repeat
                :hints(("Goal" :in-theory (enable repeat)))))
