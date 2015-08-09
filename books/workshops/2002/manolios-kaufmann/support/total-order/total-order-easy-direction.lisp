; Copyright (C) 2001  Georgia Institute of Technology

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by: Panagiotis Manolios who can be reached as follows.

; Email: manolios@cc.gatech.edu

; Postal Mail:
; College of Computing
; CERCS Lab
; Georgia Institute of Technology
; 801 Atlantic Drive
; Atlanta, Georgia 30332-0280 U.S.A.

; Certify with ACL2 version 2.5

(in-package "ACL2")

(defmacro boolp (x)
  `(or (equal ,x t)
       (equal ,x nil)))

(defstub total-order (x y) t)

(defun bad-atom (x)
  (not (or (consp x)
           (acl2-numberp x)
           (symbolp x)
           (characterp x)
           (stringp x))))

(defaxiom boolp-total-order
  (boolp (total-order x y))
  :rule-classes :type-prescription)

(defaxiom total-order-anti-symmetric
  (implies (and (total-order x y)
		(total-order y x))
	   (equal x y))
  :rule-classes :forward-chaining)

(defaxiom total-order-transitive
  (implies (and (total-order x y)
		(total-order y z))
	   (total-order x z)))

(defaxiom total-order-total
  (or (total-order x y)
      (total-order y x))
  :rule-classes nil)

(encapsulate
 ((bad-atom<= (x y) t))
 (local (defun bad-atom<= (x y)
	  (total-order x y)))

 (defthm boolp-bad-atom<=
   (boolp (bad-atom<= x y))
   :rule-classes :type-prescription)

 (defthm bad-atom<=-anti-symmetric
   (implies (and (bad-atom x)
		 (bad-atom y)
		 (bad-atom<= x y)
		 (bad-atom<= y x))
	    (equal x y))
   :hints (("goal" :use total-order-anti-symmetric))
   :rule-classes nil)

 (defthm bad-atom<=-transitive
   (implies (and (bad-atom x)
		 (bad-atom y)
		 (bad-atom z)
		 (bad-atom<= x y)
		 (bad-atom<= y z))
	    (bad-atom<= x z)))

 (defthm bad-atom<=-total
   (implies (and (bad-atom x)
		 (bad-atom y))
	    (or (bad-atom<= x y)
		(bad-atom<= y x)))
   :hints (("goal" :use total-order-total))
   :rule-classes nil))

