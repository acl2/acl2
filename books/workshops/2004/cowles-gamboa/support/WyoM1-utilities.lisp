; The WyoM1 Utility Lemmas
; Copyright (C) 2004  J Strother Moore,
;               University of Texas at Austin

; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; Written by: J Strother Moore
; email:      Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; Modified by: John Cowles
; email:       cowles@uwyo.edu
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.
;==============================================================
; This file is a certified book containing some simple lemmas
; used to make it easier to do proofs about WyoM1 programs.

; Instructions

; To certify this book, you must first have certified your local
; copy of WyoM1.lisp.  Then, copy this book to the same directory on
; which your certified copy of WyoM1.lisp resides and on which you
; have write permission, fire up ACL2 while connected to that
; directory and then execute the following two events.
#|
(include-book "WyoM1")

(certify-book "WyoM1-utilities" 1)
|#
; After certification, the book may be used in an ACL2 session or
; in other books, by writing the form

; (include-book "WyoM1-utilities")

; using the full path name as necessary.

; End of Instructions
;----------------------------------------------------------------
; Every ACL2 book must begin with an in-package form.

; The following was changed from "WyoM1" by Matt K. for ACL2 2.9.3 because
; package names may no longer contain lower case characters.
(in-package "WYO-M1")

; Some Simple Utility Lemmas

; The standard arithmetic lemmas are brought in here.

(include-book "../../../../arithmetic/top")

; Now make stacks and states behave like abstract data types.

(defthm stacks
  (and (equal (top (push x s)) x)
       (equal (pop (push x s)) s)))

(in-theory (disable push top pop))

(defthm binding-bind
  (equal (binding x (bind var val alist))
	 (if (equal x var)
	     val
	     (binding x alist))))

(defthm states
  (and (equal (call-stack (make-state call-stack defs))
	      call-stack)
       (equal (defs (make-state call-stack defs)) defs)
       (equal (pc (make-state
		   (push (make-frame pc locals stack program)
			 call-stack)
		   defs))
	      pc)
       (equal (locals (make-state
		       (push (make-frame pc locals stack program)
			     call-stack)
		       defs))
	      locals)
       (equal (stack (make-state
		      (push (make-frame pc locals stack program)
			    call-stack)
		      defs))
	      stack)
       (equal (program (make-state
			(push (make-frame pc locals stack program)
			      call-stack)
			defs))
	      program)))

(in-theory (disable make-state call-stack defs
		    make-frame pc locals stack program))

; The next block of lemmas force ACL2 to expand certain functions
; in certain common situations, augmenting its heuristics
; controlling expansion.

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (step s) (do-inst (next-inst s) s))))

(in-theory (disable step))

(defthm run-opener
  (and (equal (run s 0) s)
       (implies (and (integerp n)
		     (> n 0))
		(equal (run s n)
		       (run (step s)(+ -1 n))))))

(defthm run-sum
  (implies (and (integerp i)
		(>= i 0)
		(integerp j)
		(>= j 0))
	   (equal (run s (+ i j))
		  (run (run s i) j))))

(in-theory (disable run))
