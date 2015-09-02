; A certain recursive equation renders ACL2 inconsistent.
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
;  Last modified 28 September 2001.
;  Modified May 2002 by Robert Krug to account for v2-7 changes.  See also
;    bad-def1.lisp for an alternate version.
#|
This is an example, due Manolious and Moore, showing there is NO
ACL2 function g that satisfies the recursive equation

 (equal (g n)
        (if (equal n 0)
	    nil
	    (cons nil (g (- n 1))))).

The proof is by contradiction: Adding the above equation as an axiom
allows the proof of NIL, which is ACL2's version of FALSE.

This proof follows the outline of such a proof given by Manolious
and Moore.
|#

(in-package "ACL2")

(defstub
    g (*) => *)

(defaxiom
    g-axiom
    (equal (g n)
	   (if (equal n 0)
	       nil
	       (cons nil (g (- n 1)))))
    :rule-classes nil)

(defthm
    len-cons
    (equal (len (cons x y))(+ 1 (len y))))

(defthm
    len-g->-k
    (implies (and (not (equal n 0))
		  (> (len (g (- n 1)))
		     (- k 1)))
	     (> (len (g n)) k))
    :hints (("Goal"
	     :use g-axiom)))

(set-irrelevant-formals-ok :warn)

(defun
    induct-hint (k n)
    (if (zp k)
	t
        (induct-hint (- k 1)(- n 1))))

(defthm len-g-=-0-==>-n-=-0
  (equal (equal (len (g n)) 0)
         (equal n 0))
  :hints (("Goal" :use g-axiom)))

(defthm
    g-at-neg-input
    (implies (and (< n 0)
		  (integerp k))
	     (> (len (g n)) k))
    :rule-classes nil
    :hints (("goal"
	     :induct (induct-hint k n))))

(defthm
    contradiction!!
    nil
    :rule-classes nil
    :hints (("Goal"
	     :use (:instance
		   g-at-neg-input
		   (n -1)
		   (k (len (g -1)))))))
