; Arithmetic-4 Library
; Copyright (C) 2008 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; types.lisp
;;;
;;; The neccesity for these theorems does not arise very often,
;;; but it can be very irritating when they do.  
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "types-helper"))

(local
 (defthm equal-to-iff-1
   (equal (equal (rationalp x) (rationalp y))
	  (iff (rationalp x) (rationalp y)))))

(local
 (defthm equal-to-iff-2
   (equal (equal (integerp x) (integerp y))
	  (iff (integerp x) (integerp y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next two are subsumed by meta-integerp-correct or
;;; meta-rationalp-correct.

;;;(defthm rationalp-+
;;;  (implies (and (rationalp x)
;;;		   (rationalp y))
;;;	      (rationalp (+ x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

;;;(defthm integerp-+
;;;  (implies (and (integerp x)
;;;		   (integerp y))
;;;	      (integerp (+ x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm rationalp-minus
  (implies (acl2-numberp x)
	   (equal (rationalp (- x))
		  (rationalp x))))

(defthm integerp-minus
  (implies (acl2-numberp x)
	   (equal (integerp (- x))
		  (integerp x))))

;;; These next two are subsumed by meta-integerp-correct or
;;; meta-rationalp-correct.

;;;(defthm rationalp-*
;;;  (implies (and (rationalp x)
;;;		(rationalp y))
;;;	   (rationalp (* x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

;;;(defthm integerp-*
;;;  (implies (and (integerp x)
;;;		   (integerp y))
;;;	      (integerp (* x y)))
;;;  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm rationalp-/
  (implies (acl2-numberp x)
	   (equal (rationalp (/ x))
		  (rationalp x))))

(defthm not-integerp-/-1
  (implies (< 1 x)
	   (not (integerp (/ x)))))

(defthm not-integerp-/-2
  (implies (< x -1)
	   (not (integerp (/ x)))))
	   
;;; We do not introduce the case-split unless we are rewriting a goal
;;; literal. 

(defthm integerp-/
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(integerp x))
	   (equal (integerp (/ x))
		  (or (equal x -1)
		      (equal x 0)
		      (equal x 1)))))

(defthm rationalp-x
  (implies (integerp x)
	   (rationalp x))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm acl2-numberp-x
  (implies (rationalp x)
	   (acl2-numberp x))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))
