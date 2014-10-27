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

   This program is distributed in the hope that it will be useful
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.
|#

(in-package "SET")
(include-book "primitives")
(include-book "std/osets/computed-hints" :dir :system)
(include-book "std/osets/membership" :dir :system)
(set-verify-guards-eagerness 2)

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(defthmd open-set-in
  (implies
   (and
    (syntaxp (quotep x))
    (not (empty x)))
   (equal (in a x)
          (or (equal a (head x))
              (in a (tail x))))))

(defun find-not (X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((not (predicate (head X))) (head X))
        (t (find-not (tail X)))))









