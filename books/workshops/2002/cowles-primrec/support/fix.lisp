; The ACL2 function FIX satisfies a certain recursive equation.
; Copyright (C) 2001  John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

; Fall 2001.
;  Last modified 26 September 2001.
#|
 To certify in ACL2 Version 2.5:
 (certify-book "fix" 0 nil ; compile-flg
               :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
#|
The ACL2 function FIX is a solution for g1 in the primitive
recursive equation

  (equal (g1 x)
         (if (equal x 0)
             0
             (+ 1 (g1 (- x 1))))).

This is an example, due Manolious and Moore, showing that the
binary function h having a right fixed point is not necessary for
the existence of such a solution.

Here (test x) is (equal x 0),
     (base x) is 0,
     (h x y)  is (+ 1 y), and
     (st x)   is (- x 1).
|#

(in-package "ACL2")

;;FIX is a solution:
(encapsulate
 (((g1 *) => *))

 (local
  (defun
    g1 (x)
    (fix x)))

 (defthm
   g1-def
   (equal (g1 x)
	  (if (equal x 0)
	      0
	      (+ 1 (g1 (- x 1)))))
   :rule-classes nil)
 ) ;; end encapsulate

;;The function (h x y) = (+ 1 y) has NO right fixed point:
(defun
  h (x y)
  (declare (ignore x))
  (+ 1 y))

(defthm
  NO-rt-fixed-pt-for-h
  (not (equal (h x y) y)))
