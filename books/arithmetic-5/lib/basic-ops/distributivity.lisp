; Arithmetic-5 Library
; Copyright (C) 2009 Robert Krug <rkrug@cs.utexas.edu>
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
;;; distributivity.lisp
;;;
;;; We load this book first in top.lisp, so that the distributivity
;;; rules are considered last by ACL2.  For a simple example of why
;;; this might be desireable, consider:
;;; (equal (* x (/ (+ 1 y)))
;;;        z)
;;; and prefer-positive-exponents-scatter-exponents-equal.  We attempt
;;; to ``undo'' the division by multiplying both sides by (+ 1 y),
;;; resulting in
;;; (equal (* (+ 1 y) x (/ (+ 1 y)))
;;;        (* (+ 1 y) z))
;;; in the hopes that the (+ 1 y) and the (/ (+ 1 y)) will cancel.
;;; But, this would not occur if we distributed the (+ 1 y) over
;;; (* x (/ (+ 1 y))) before normalize-factors-scatter-exponents
;;; had a chance to fire.
;;; 
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Two distributivity rules.  Note that we disable the ``built-in''
;;; rule Distributivity in top.lisp.

(defthm |(* (+ x y) z)|
  (equal (* (+ x y) z)
	 (+ (* x z) (* y z))))

(defthm |(* x (+ y z))|
  (equal (* x (+ y z))
         (+ (* x y) (* x z))))
