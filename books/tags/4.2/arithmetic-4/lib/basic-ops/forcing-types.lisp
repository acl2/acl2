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
;;; forcing-types.lisp
;;;
;;; We want to ensure that the arguments to arithmetic functions are
;;; known to be of the appropriate type.  We do this with a ``clever''
;;; use of syntaxp and the introduction of if expressions.  Note that
;;; inside the true branch of the if expression, the syntaxp
;;; hypothesis will fail, while inside the false branch the offending
;;; term has disappeared.  Thus, we do not loop.
;;;
;;; Note: I put the ``clever'' above in scare quotes because trying
;;; to be clever has bitten me in the past.  Cleverness is not
;;; wisdom.
;;;
;;; Remark: The quote marks in the note immediately above are those of
;;; reference, or reification, or some such; not scare quotes.  Quote
;;; marks can be used in many ways.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm default-plus-1
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (+ x y)
		  (if (acl2-numberp x)
		      (+ x y)
		    (if (acl2-numberp y)
			y
		      0)))))

(defthm default-plus-2
  (implies (syntaxp (not (proveably-acl2-numberp 'y `((y . ,y)) mfc state)))
	   (equal (+ x y)
		  (if (acl2-numberp y)
		      (+ x y)
		    (if (acl2-numberp x)
			x
		      0)))))

(defthm default-minus
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (- x)
		  (if (acl2-numberp x)
		      (- x)
		    0))))

(defthm default-times-1
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (* x y)
		  (if (acl2-numberp x)
		      (* x y)
		    0))))

(defthm default-times-2
  (implies (syntaxp (not (proveably-acl2-numberp 'y `((y . ,y)) mfc state)))
	   (equal (* x y)
		  (if (acl2-numberp y)
		      (* x y)
		    0))))

(defthm default-divide
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (/ x)
		  (if (acl2-numberp x)
		      (/ x)
		    0))))

(defthm default-rational-denominator
  (implies (syntaxp (not (proveably-rational 'x `((x . ,x)) mfc state)))
           (equal (denominator x)
		  (if (rationalp x)
		      (denominator x)
		    1))))

(defthm default-rational-numerator
  (implies (syntaxp (not (proveably-rational 'x `((x . ,x)) mfc state)))
           (equal (numerator x)
		  (if (rationalp x)
		      (numerator x)
		    0))))

(defthm default-less-than-1
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
           (equal (< x y)
		  (if (acl2-numberp x)
		      (< x y)
		    (< 0 y)))))

(defthm default-less-than-2
  (implies (syntaxp (not (proveably-acl2-numberp 'y `((y . ,y)) mfc state)))
           (equal (< x y)
		  (if (acl2-numberp y)
		      (< x y)
		    (< x 0)))))

(defthm default-expt-1
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (expt x n)
		  (if (acl2-numberp x)
		      (expt x n)
		    (if (zip n)
		      1
		    0)))))

(defthm default-expt-2
  (implies (syntaxp (not (proveably-integer 'n `((n . ,n)) mfc state)))
	   (equal (expt x n)
		  (if (integerp n)
		      (expt x n)
		    1))))
