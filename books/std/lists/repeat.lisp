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
(local (include-book "misc/take" :dir :system))

(defund simpler-take (n xs)
  ;; Redundant from take.lisp
  (declare (xargs :guard (and (natp n)
                              (true-listp xs))))
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take (1- n) (cdr xs)))))

(defund repeat (x n)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (mbe :logic (if (zp n)
                  nil
                (cons x (repeat x (- n 1))))

; On CCL, a simple loop of (loop for i from 1 to 10000 do (repeat 6 10000))
; finished in 2.74 seconds when we use make-list, versus 3.69 seconds when
; we use make-list-ac.  So lets use make-list.

       :exec (make-list n :initial-element x)))

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
  :hints(("Goal" :in-theory (enable repeat simpler-take))))

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

 (defthmd make-list-ac->repeat
   (equal (make-list-ac n x acc)
          (append (repeat x n)
                  acc)))

 (verify-guards repeat
                :hints(("Goal" :in-theory (enable repeat
                                                  make-list-ac->repeat)))))
