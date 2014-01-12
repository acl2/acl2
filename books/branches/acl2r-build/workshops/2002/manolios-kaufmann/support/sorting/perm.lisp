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

(in-package "ACL2")

(defun in (a X)
  (declare (xargs :guard t))
  (cond ((atom X) nil)
	((equal a (car X)) t)
	(t (in a (cdr X)))))

(defun remove-el (a x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
	((equal a (car x)) (cdr x))
	(t (cons (car x) (remove-el a (cdr x))))))

(defun perm (x y)
  (declare (xargs :guard t))
  (cond ((atom x) (atom y))
	(t (and (in (car x) y)
		(perm (cdr x) (remove-el (car x) y))))))

(defthm perm-reflexive
  (perm a a))

(defthm remove-el-swap
 (equal (remove-el a (remove-el b x))
	(remove-el b (remove-el a x))))

(defthm remove-el-in
  (implies (not (equal a b))
	   (equal (in a (remove-el b y))
		  (in a y))))

(local
 (defthm perm-remove
   (implies (perm x y)
	    (perm (remove-el a x) (remove-el a y)))))

(defthm car-perm
  (implies (and (consp x)
		(not (in (car x) y)))
	   (not (perm y x))))

(defthm perm-symmetric
  (implies (perm x y)
	   (perm y x))
  :hints (("Goal"
	   :induct (perm y x))
	  ("Subgoal *1/2''"
	   :use ((:instance perm-remove (a (car y)))))))

(defthm perm-in
  (implies (and (perm x y)
		(in a x))
	   (in a y))
  :rule-classes ((:forward-chaining :trigger-terms ((in a x) (in a y)))))

(defthm perm-transitive
  (implies (and (perm x y) (perm y z))
	   (perm x z)))

(defequiv perm)

(defthm perm-remove-el-app
  (implies (in x y)
	   (equal (remove-el x (append y z))
		  (append (remove-el x y) z))))

(defcong perm perm (append x y) 1)

(defcong perm perm (append x y) 2)

(defcong perm perm (cons x y) 2)

(defcong perm perm (remove-el x y) 2)

(defthm perm-app-cons
  (perm (append x (cons y z))
	(cons y (append x z))))

(defcong perm equal (in x y) 2)
