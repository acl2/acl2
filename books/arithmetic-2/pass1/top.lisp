; Arithmetic-2 Library
; Copyright (C) 1999 Robert Krug <rkrug@cs.utexas.edu>
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

;;
;; top.lisp
;;

;;
;; This book gathers together all the other books in one easy to
;; include package.
;;

(in-package "ACL2")

(include-book "basic-arithmetic")

(include-book "inequalities")

(include-book "expt")

(include-book "prefer-times")

(include-book "mini-theories")

(include-book "numerator-and-denominator")

#| ???
(defthm three
  (implies (rationalp x)
	   (rationalp (expt x y)))
  :rule-classes :type-prescription)

#+:non-standard-analysis
(defthm three-realp
  (implies (realp x)
	   (realp (expt x y)))
  :rule-classes :type-prescription)

(defthm four
  (equal (* x (expt x -1))
	 (if (equal (fix x) 0)
	     0
	     1)))

(defthm five
  (equal (* y x (expt y -1))
	 (if (equal (fix y) 0)
	     0
	     (fix x))))

(defthm six
  (equal (/ x)
	 (expt x -1))
  :hints (("Goal" :expand (expt x -1))))
|#
#| !!!
(defthm seven
  (implies (not (acl2-numberp x))
	   (equal (expt x y)
		  (if (equal (ifix y) 0)
		      1
		      0))))
|#
#| ???
(in-theory (disable expt))
|#
