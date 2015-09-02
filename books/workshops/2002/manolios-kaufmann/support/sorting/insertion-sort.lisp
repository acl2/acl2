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

(include-book "perm-order")

(defun insert (a x)
  (if (consp x)
      (if (<<= a (car x))
	  (cons a x)
	(cons (car x) (insert a (cdr x))))
    (list a)))

(defun isort (x)
  (if (consp x)
      (insert (car x) (isort (cdr x)))
    nil))

(defthm ordered-insert
  (implies (orderedp y)
	   (orderedp (insert x y))))

(defthm ordered-sort
  (orderedp (isort x)))

(defthm perm-insert
  (perm (insert x y) (cons x y)))

(defthm perm-sort
  (perm (isort x) x))

(defthm insert-insert
  (equal (insert x (insert y z))
	 (insert y (insert x z)))
    :rule-classes ((:rewrite :loop-stopper ((x y)))))

(defthm insert-in
  (equal (isort (insert x y))
	 (isort (cons x y))))

(defthm insert-sort-remove
  (implies (in x y)
	   (equal (insert x (isort (remove-el x y)))
		  (isort y))))

(defthm sort-canonical
  (implies (and (perm x y)
                ;; Added for mod to ACL2 v2-8 that does better matching for calls of
                ;; equivalence relations against the current context, to avoid a rewriter
                ;; loop in the proof of mail:
                (syntaxp (not (term-order x y))))
	   (equal (isort x)
		  (isort y))))

(defthm main
  (equal (perm x y)
	 (equal (isort x)
		(isort y)))
  :hints (("goal"
	   :use ((:instance perm-sort (x y))
		 (:instance perm-sort))
	   :in-theory (disable perm-sort)))
  :rule-classes nil)

(defthm main2
  (implies (and (orderedp x)
		(perm x y))
	   (equal (isort y)
		  x))
  :rule-classes nil)

(defthm main3
  (implies (and (orderedp x)
		(orderedp y)
		(perm x y))
	   (equal x y))
  :hints (("goal"
	   :use ((:instance main2) (:instance main2 (x y)))))
  :rule-classes nil)
