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
;;; simple-equalities-and-inequalities-helper.lisp
;;;
;;; This book contains some messy proofs which I want to hide.
;;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../../support/top"))

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
(defun rationalp-guard-fn (args)
  (if (endp (cdr args))
      `((rationalp ,(car args)))
    (cons `(rationalp ,(car args))
          (rationalp-guard-fn (cdr args))))))

(local
(defmacro rationalp-guard (&rest args)
  (if (endp (cdr args))
      `(rationalp ,(car args))
    (cons 'and
          (rationalp-guard-fn args)))))

(local
 (defthm niq-bounds
   (implies (and (integerp i)
		 (<= 0 i)
		 (integerp j)
		 (< 0 j))
	    (and (<= (nonnegative-integer-quotient i j)
		     (/ i j))
		 (< (+ (/ i j) -1)
		    (nonnegative-integer-quotient i j))))
   :hints (("Subgoal *1/1''" :in-theory (enable NORMALIZE-<-/-TO-*-3-3)))
   :rule-classes ((:linear
		   :trigger-terms ((nonnegative-integer-quotient i j))))))

(local
(defthm floor-bounds-1
  (implies (rationalp-guard x y)
	   (and (< (+ (/ x y) -1)
		   (floor x y))
		(<= (floor x y)
		    (/ x y))))
  :rule-classes ((:generalize) 
		 (:linear :trigger-terms ((floor x y))))))

(local
(defthm floor-bounds-2
  (implies (and (rationalp-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y)
		  (/ x y)))
  :rule-classes ((:generalize) 
		 (:linear :trigger-terms ((floor x y))))))

(local
(defthm floor-bounds-3
  (implies (and (rationalp-guard x y)
		(not (integerp (/ x y))))
	   (< (floor x y)
	      (/ x y)))
  :rule-classes ((:generalize) 
		 (:linear :trigger-terms ((floor x y))))))


(local
 (in-theory (disable floor)))

(defthm integerp-<-constant
  (implies (and (syntaxp (rational-constant-p c))
		(rationalp c)
		(not (integerp c))
		(integerp x))
           (equal (< x c)
                  (<= x (floor c 1))))
  :otf-flg t)

(defthm constant-<-integerp
  (implies (and (syntaxp (rational-constant-p c))
                (rationalp c)
		(not (integerp c))
		(integerp x))
           (equal (< c x)
                  (<= (+ 1 (floor c 1)) x)))
  :otf-flg t)

