;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

#|

I tried to put the rewrite rules below in the "right" order.  This
helps a little with execution time.

|#
(in-package "ACL2")

(defthm nth-cons-open
  (implies (equal y (cons a b))
	   (equal (nth n y)
		  (if (zp n)
		      a
		    (nth (1- n) b)))))

(defthm open-nth
  (equal (nth n (cons a b))
	 (if (zp n)
	     a
	   (nth (1- n) b))))

(defthm compare-updates
  (implies (and (equal i1 i2)
		(not (equal v1 v2)))
	   (equal (equal (update-nth i1 v1 l1)
			 (update-nth i2 v2 l2))
		  nil)))

(defthm update-nth-cons-open
  (implies (equal y (cons a b))
	   (equal (update-nth n x y)
		  (if (zp n)
		      (cons x b)
		    (cons a (update-nth (1- n) x b))))))

(defthm open-update-nth
  (equal (update-nth n x (cons a b))
	 (if (zp n)
	     (cons x b)
	   (cons a (update-nth (1- n) x b)))))

(defthm nth-update-nth2
  (equal (nth n1 (update-nth n2 v l))
	 (if (equal (nfix n1) (nfix n2))
	     v
	   (nth n1 l))))

(defthm update-nth-update-nth-diff
  (implies
   (not (equal (nfix i1) (nfix i2)))
   (equal (update-nth i1 v1 (update-nth i2 v2 l))
	  (update-nth i2 v2 (update-nth i1 v1 l))))
  :rule-classes ((:rewrite :loop-stopper ((i1 i2)))))

(defthm update-nth-update-nth-same
  (equal (update-nth i v1 (update-nth i v2 l))
	 (update-nth i v1 l)))

(defthm nth-over-if
  (equal (nth n (if a b c))
	 (if a
	     (nth n b)
	   (nth n c))))

(in-theory (disable nth nth-over-if update-nth))
