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
;;; I probably shouldn't be calling this normalization, since all we
;;; are really doing is lifting if expressions over certain arithmetic
;;; expressions.  Perhaps in some future cleanup I will rename this
;;; file.
;;;
;;; Note: Some documentation on just how this is useful would be nice.
;;; Where (when) do if expressions get introduced?  Why does this
;;; lifting help?  What fails if this is disabled?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(+ (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (+ (if a b c) x)
		  (if a (+ b x) (+ c x)))))

(defthm |(+ x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (+ x (if a b c))
		  (if a (+ x b) (+ x c)))))

(defthm |(- (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (- (if a b c))
		  (if a (- b) (- c)))))

(defthm |(* (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (* (if a b c) x)
		  (if a (* b x) (* c x)))))

(defthm |(* x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (* x (if a b c))
		  (if a (* x b) (* x c)))))

(defthm |(/ (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (/ (if a b c))
		  (if a (/ b) (/ c)))))

(defthm |(expt (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (expt (if a b c) x)
		  (if a (expt b x) (expt c x)))))

(defthm |(expt x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (expt x (if a b c))
		  (if a (expt x b) (expt x c)))))

(defthm |(equal x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (equal x (if a b c))
		  (if a (equal x b) (equal x c)))))

(defthm |(equal (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (equal (if a b c) x)
		  (if a (equal b x) (equal c x)))))

(defthm |(< x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (< x (if a b c))
		  (if a (< x b) (< x c)))))

(defthm |(< (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (< (if a b c) x)
		  (if a (< b x) (< c x)))))
