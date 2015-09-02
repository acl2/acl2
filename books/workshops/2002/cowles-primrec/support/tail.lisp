; Introduction of an arbitrary tail-recursive function.
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
 (certify-book "tail" 0 nil ; compile-flg
               :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
#|
Show for Pete & J's construction, as reported in defpun.lisp, of
tail-recursive f, any constant would do in place of nil in the
definition of f.
|#

(in-package "ACL2")

(defstub
  test (*) => *)

(defstub
  base (*) => *)

(defstub
  st (*) => *)

(defstub
    const () => *)

(defun stn (x n)
  (if (zp n) x (stn (st x) (1- n))))

(defchoose fch (n) (x)
	   (test (stn x n)))

(defun fn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (test x))
      (base x)
      (fn (st x) (1- n))))

;; Here an arbitrary constant, (const), is used in place of nil in
;;  Pete & J's original definition.
(defun f (x)
  (if (test (stn x (fch x)))
      (fn x (fch x))
      (const)))

;;; This proof of generic-tail-recursive-f is a minor
;;;  variation of Pete & J's proof of generic-tail-recursive-f
;;;  in defpun.lisp
(encapsulate
 ()
 (local (defthm test-fch
	    (implies (test x)
		     (test (stn x (fch x))))
            :hints
	    (("goal" :use ((:instance fch (n 0)))))))

;; Not needed for Pete & J's proof of generic-tail-recursive-f.
;;  Also not needed for this proof of generic-tail-recursive-f.
;;(local (defthm test-f-def
;;	 (implies (test x)
;;		  (equal (f x) (base x)))))

 (local (defthm open-stn
	    (implies (and (integerp n) (< 0 n))
		     (equal (stn x n)
			    (stn (st x) (1- n))))))

 (local (defthm +1-1 (equal (+ -1 +1 x) (fix x))))

 (local (defthm st-stn-fch
	    (implies (test (stn (st x) (fch (st x))))
		     (test (stn x (fch x))))
	    :hints
	    (("goal" :use
		     ((:instance fch (n (1+ (nfix (fch (st x))))))
		      (:instance fch (n 1)))))
	    :rule-classes :forward-chaining))

 (local (defthm test-nil-fch
	    (implies (not (test x))
		     (iff (test (stn (st x)
				     (fch (st x))))
			  (test (stn x (fch x)))))
	    :hints
	    (("subgoal 2" :expand (stn x (fch x))
			  :use
			  ((:instance fch (x (st x))
				      (n (+ -1 (fch x)))))))))

 (local (defthm fn-st
	    (implies (and (test (stn x n))
			  (test (stn x m)))
		     (equal (fn x n) (fn x m)))
	    :rule-classes nil))

 (defthm generic-tail-recursive-f
     (equal (f x)
	    (if (test x) (base x) (f (st x))))
     :hints
     (("subgoal 1" :expand (fn x (fch x)))
      ("subgoal 1.2'" :use
		      ((:instance fn-st (x (st x))
				  (n (+ -1 (fch x)))
				  (m (fch (st x)))))))
     :rule-classes nil)
 ) ;; end encapsulate


