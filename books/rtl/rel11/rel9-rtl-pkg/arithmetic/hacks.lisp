; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

;This book contains arithmetic hacks removed from basic.lisp

(defun natp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (<= 0 x)))

(local (include-book "fp2"))

(defthm delta1-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (<= (* y d) (* (- x y) d)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x d) (y+ (- x y)))))))


(defthm delta1-a
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (>= (- x (* y (+ 1 d)))
		 (* (- x y) (- 1 d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance delta1-1)))))

(defthm delta1-b
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (<= (- x (* y (- 1 d)))
		 (* (- x y) (+ 1 d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance delta1-1)))))

(defthm delta2
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= (* x d) 0))
	     (>= (+ x (* y (- 1 d)))
		 (* (+ x y) (- 1 d))))
  :rule-classes ())

(defthm natp-
    (implies (and (natp x)
		  (natp y)
		  (>= x y))
	     (natp (+ x (* -1 y))))
  :hints (("Goal" :in-theory (enable natp))))

;disable, since we intend to keep natp enabled?
(defthmd natp>=0
  (implies (natp x)
           (>= x 0)))
