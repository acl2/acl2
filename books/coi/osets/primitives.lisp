#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
#||
   Fully Ordered Finite Sets, Version 0.9
   Copyright (C) 2003, 2004 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.

||#

(in-package "SET")
(set-verify-guards-eagerness 2)

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(include-book "std/osets/primitives" :dir :system)

(defmacro emptyset ()
  nil)

(defun list-to-set (list)
  (cond
   ((consp list)
    (insert (car list) (list-to-set (cdr list))))
   (t
    nil)))

(defthmd setp-list-to-set
  (setp (list-to-set X))
  :hints (("Goal" :in-theory (enable insert))))

(defthm head-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (head X) (head Y)) t)))

(defthm tail-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (tail X) (tail Y)) t)))

(defthm insert-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (insert a X) (insert a Y)) t)))

(defthm sfix-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (sfix X) (sfix Y)) t)))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

(defthm head-insert-empty
  (implies (empty X)
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
           (empty (tail (insert a X)))))

(defthm head-not-whole
  (implies (not (empty X))
           (not (equal (head X) X)))
  :hints(("Goal" :in-theory (enable head empty))))

(deftheory primitives-theory
  '(setp
    empty
    head
    tail
    sfix
    (:definition insert)))

(deftheory primitive-order-theory
  '(<<-irreflexive
    <<-transitive
    <<-asymmetric
    <<-trichotomy
    head-insert
    tail-insert
    head-tail-order
    head-tail-order-contrapositive))

(in-theory (disable primitives-theory
                    primitive-order-theory))

