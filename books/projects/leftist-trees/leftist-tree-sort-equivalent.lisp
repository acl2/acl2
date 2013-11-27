#|
   Leftist Trees, Version 0.1
   Copyright (C) 2012 by Ben Selfridge <benself@cs.utexas.edu>

   This program is free software; you can redistribute it and/or modify
   it under the terms of Version 2 of the GNU General Public License as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
   02110-1301, USA.
|#

; (certify-book "sorts-equivalent")

(in-package "ACL2")

(include-book "sorting/equisort" :dir :system)
(include-book "sorting/isort" :dir :system)

(include-book "leftist-tree-sort")

(defthm ltree-sort-is-isort
  (implies (true-listp x)
           (equal (ltree-sort x) (isort x)))
  :hints (("Goal" :use (:functional-instance weak-sortfn1-is-sortfn2
                                             (sortfn1 (lambda (x) (ltree-sort x)))
                                             (sortfn2 (lambda (x) (isort x)))))))
