; Arithmetic-3 Library
; Copyright (C) 2004 Robert Krug <rkrug@cs.utexas.edu>
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
;;; numerator-and-denominator.lisp
;;;
;;;
;;; Some simple facts about numerator and denominator.
;;;
;;; This book should be expanded some day.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Type-set already knows that (numerator x) and (denominator x)
;;; are integers, and that 0 < (denominator x).

(defthm Rational-implies2               ; Redundant, from axioms.lisp
  (implies (rationalp x)
           (equal (* (/ (denominator x)) (numerator x)) x)))

(local (in-theory (enable rewrite-linear-equalities-to-iff)))

(defthm numerator-positive
  (implies (rationalp x)
	   (equal (< 0 (numerator x))
		  (< 0 x)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(< 0 x))
			   (< 0 (numerator x))))
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(<= 0 x))
			   (<= 0 (numerator x))))))

(defthm numerator-negative
  (implies (rationalp x)
	   (equal (< (numerator x) 0)
		  (< x 0)))
  :rule-classes ((:rewrite)
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(< x 0))
			   (< (numerator x) 0)))
		 (:type-prescription
		  :corollary
		  (implies (and (rationalp x)
				(<= x 0))
			   (<= (numerator x) 0)))))

(defthm numerator-minus
   (equal (numerator (- i))
          (- (numerator i))))

(defthm denominator-minus
  (implies (rationalp x)
           (equal (denominator (- x))
                  (denominator x))))

(defthm integerp==>numerator-=-x
  (implies (integerp x)
	   (equal (numerator x)
		  x)))

(defthm integerp==>denominator-=-1
  (implies (integerp x)
           (equal (denominator x)
		  1)))

(defthm equal-denominator-1
  (equal (equal (denominator x) 1)
         (or (integerp x)
             (not (rationalp x)))))

(defthm *-r-denominator-r
  (equal (* r (denominator r))
         (if (rationalp r)
             (numerator r)
           (fix r))))
