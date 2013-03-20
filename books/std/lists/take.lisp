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

; NOTE: This file was originally in books/unicode/, but has been moved here to
; solve a circular dependency issue introduced when this book was locally
; included in symbol-btree.lisp.

(in-package "ACL2")
(local (include-book "arithmetic/top" :dir :system))

(in-theory (disable (:definition take)))

(defun simpler-take-induction (n xs)
  ;; Not generally meant to be used; only meant for take-induction
  ;; and take-redefinition.
  (if (zp n)
      nil
    (cons (car xs)
          (simpler-take-induction (1- n) (cdr xs)))))

(encapsulate
  ()
  (local (in-theory (enable take)))

  (local (defthm equivalence-lemma
           (implies (true-listp acc)
                    (equal (first-n-ac n xs acc)
                           (revappend acc (simpler-take-induction n xs))))))

  (defthm take-redefinition
    (equal (take n x)
           (if (zp n)
               nil
             (cons (car x)
                   (take (1- n) (cdr x)))))
    :rule-classes ((:definition :controller-alist ((TAKE T NIL))))))

(defthm take-induction t
  :rule-classes ((:induction
                  :pattern (take n x)
                  :scheme (simpler-take-induction n x))))

;; The built-in type-prescription for take is awful:
;;
;; (OR (CONSP (TAKE N L))
;;            (EQUAL (TAKE N L) NIL)
;;            (STRINGP (TAKE N L)))
;;
;; So fix it...

(in-theory (disable (:type-prescription take)))

(defthm true-listp-of-take
  (true-listp (take n xs))
  :rule-classes :type-prescription)

(defthm consp-of-take
  (equal (consp (take n xs))
         (not (zp n))))

(defthm len-of-take
  (equal (len (take n xs))
         (nfix n)))

(defthm take-of-cons
  (equal (take n (cons a x))
         (if (zp n)
             nil
           (cons a (take (1- n) x)))))

(defthm take-of-append
  (equal (take n (append x y))
         (if (< (nfix n) (len x))
             (take n x)
           (append x (take (- n (len x)) y))))
  :hints(("Goal" :induct (take n x))))

(defthm take-of-1
  (equal (take 1 x)
         (list (car x))))

(defthm car-of-simple-take
  (implies (<= 1 (nfix n))
           (equal (car (take n x))
                  (car x))))

(defthm second-of-simple-take
  (implies (<= 2 (nfix n))
           (equal (second (take n x))
                  (second x))))

(defthm third-of-simple-take
  (implies (<= 3 (nfix n))
           (equal (third (take n x))
                  (third x))))

(defthm fourth-of-simple-take
  (implies (<= 4 (nfix n))
           (equal (fourth (take n x))
                  (fourth x))))

(encapsulate
  ()
  (local (defun repeat (x n)
           (if (zp n)
               nil
             (cons x (repeat x (- n 1))))))

  (local (defthm l0
           (equal (append (repeat x n) (cons x y))
                  (cons x (append (repeat x n) y)))))

  (local (defthm l1
           (equal (make-list-ac n val acc)
                  (append (repeat val n) acc))
           :hints(("Goal"
                   :induct (make-list-ac n val acc)))))

  (local (defthm l2
           (implies (atom x)
                    (equal (take n x)
                           (make-list n)))))

  (defun first-n (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (take n x)
         :exec
         (cond ((zp n)
                nil)
               ((atom x)
                (make-list n))
               (t
                (cons (car x)
                      (first-n (- n 1) (cdr x))))))))
