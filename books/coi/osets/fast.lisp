#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
#|

   Fully Ordered Finite Sets, Version 0.9
   Copyright (C) 2003, 2004 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.
|#

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(in-package "SET")
(include-book "membership")
(include-book "std/osets/union" :dir :system)
(include-book "std/osets/intersect" :dir :system)
(include-book "std/osets/difference" :dir :system)
(set-verify-guards-eagerness 2)

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

;;; First we introduce some basic theory about cons and sets.  Note
;;; that this theory is disabled at the end of this file.  However, if
;;; you are introducing fast versions of new set functions, you can
;;; enable these theorems by enabling cons-theory.

(defthm cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X))))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-nonempty
  (implies (and (setp X)
                (<< a (head X)))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory
                                    primitive-order-theory))))

(defthm cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))


(deftheory cons-theory
  '(cons-set
    cons-head
    cons-to-insert-empty
    cons-to-insert-nonempty
    cons-in))

(in-theory (disable cons-theory))
