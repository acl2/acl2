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

(include-book "insertion-sort")

(defun less (x lst)
  (cond ((atom lst) nil)
	((<< (car lst) x)
	 (cons (car lst) (less x (cdr lst))))
	(t (less x (cdr lst)))))

(defun notless (x lst)
  (cond ((atom lst) nil)
	((not (<< (car lst) x))
	 (cons (car lst) (notless x (cdr lst))))
	(t (notless x (cdr lst)))))

(defun qsort (x)
  (cond ((atom x) nil)
	(t (append (qsort (less (car x) (cdr x)))
		   (list (car x))
		   (qsort (notless (car x) (cdr x)))))))

(defun lessp (x lst)
  (cond ((atom lst) t)
	(t (and (<< (car lst) x)
		(lessp x (cdr lst))))))

(defun notlessp (x lst)
  (cond ((atom lst) t)
	(t (and (not (<< (car lst) x))
		(notlessp x (cdr lst))))))

(defthm perm-less-notless
  (perm (append (less x y) (notless x y))
	y))

(defthm perm-qsort
  (perm (qsort x) x))

(defthm lessp-less
 (lessp x (less x lst)))

(defthm notlessp-notless
 (notlessp x (notless x lst)))

(defcong perm equal (lessp x lst) 2)

(defcong perm equal (notlessp x lst) 2)

(defthm lessp-less-qsort
 (lessp x (qsort (less x lst))))

(defthm notlessp-notless-qsort
 (notlessp x (qsort (notless x lst))))

(defthm orderedp-lemma
  (implies (and (orderedp x)
		(orderedp y)
		(lessp z x)
		(notlessp z y))
	   (orderedp (append x (cons z y))))
  :hints (("goal" :in-theory (enable <<))))

(defthm qsort-is-ordered
  (orderedp (qsort x)))

(defthm qsort-main
  (equal (qsort x)
	 (isort x))
  :hints (("goal" :use (:instance main2 (x (qsort x)) (y x)))))

#|
Or we can prove it as follows:

(defthm qsort-main
  (equal (qsort x)
	 (isort x))
  :hints (("goal" :use (:instance main3 (x (qsort x)) (y (isort x))))))

|#