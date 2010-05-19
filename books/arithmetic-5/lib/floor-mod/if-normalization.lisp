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
;;; if-normalization.lisp
;;;
;;; We have found it useful to normalize if expressions involving
;;; arithmetic operators.
;;;
;;; See the comments in ../basic-ops/if-normalization.lisp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../basic-ops/building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(floor (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (floor (if a b c) x)
		  (if a (floor b x) (floor c x)))))

(defthm |(floor y (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (floor y (if a b c))
		  (if a (floor y b) (floor y c)))))

(defthm |(mod (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (mod (if a b c) x)
		  (if a (mod b x) (mod c x)))))

(defthm |(mod y (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (mod y (if a b c))
		  (if a (mod y b) (mod y c)))))

(defthm |(logand (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (logand (if a b c) x)
		  (if a (logand b x) (logand c x)))))

(defthm |(logand y (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (logand y (if a b c))
		  (if a (logand y b) (logand y c)))))

(defthm |(lognot (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (lognot (if a b c))
		  (if a (lognot b) (lognot c)))))
