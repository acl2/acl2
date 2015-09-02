; Introduction of an arbitrary primitive-recursive function.
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

; Summer 2001.
;  Last modified 20 July 2001.
#|
 To certify in ACL2 Version 2.5:
 (certify-book "primitive" 0 nil ; compile-flg
               :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
#|
In the spirit of Pete & J's work reported in defpun.lisp, their
construction of a function f that satisfies the equation in the
following theorem,

(defthm generic-tail-recursive-f
  (equal (f x)
	 (if (test x) (base x) (f (st x))))),

is extended to a construction of a function f that satisfies
the equation, for certain h's, in the theorem:

(defthm generic-primitive-recursive-f
    (equal (f x)
	   (if (test x) (base x) (h x (f (st x)))))).

Three examples are included below:
  Example 1. Pete & J's cons example (modified).
  Example 2. Naive Factorial
  Example 3. Example with parameters.

 These examples each construct a function using a minor variation
 of the construction outlined in defpun.lisp for tail-recursive
 functions.

As shown by Pete & J, for some h's, such an f does not exist.
Their example, showing such an f need not exist, has
  (test x) = (equal x 0),
  (base x) = nil,
  (h x y$)  = (cons nil y$), and
  (st x)   = (- x 1).

A sufficient (but not necessary) condition on h for the
existence of f is that h have a right fixed point, i.e., there is
some c such that (h x c) = c.

An example, also due to Pete & J, showing that h having a right
fixed point is not necessary for the existence of f has
  (test x) = (equal x 0)
  (base x) = 0
  (h x y$)  = (+ 1 y$), and
  (st x)   = (- x 1).
The ACL2 function fix satisfies the recursive equation in
generic-primitive-recursive-f, for these choices for test, base,
h, and st.  Here (fix x) returns x if x is an ACL2 number and
returns 0 otherwise.

Note:
A function f satisfying the equation
    (equal (f x)
	   (if (test x) (base x) (h x (f (st x)))))).
is called primitive recursive because a recursive equation of
this form is a generalization of the definitions by primitive
recursion studied in computability theory:
    F(x_1,...,x_n, 0)   = k(x_1,...,x_n)
    F(x_1,...,x_n, t+1) = h(t, F(x_1,...,x_n,t), x_1,...,x_n).
|#
;;; This construction of generic-primitive-recursive-f is a
;;;  minor variation of Pete & J's construction of
;;;  generic-tail-recursive-f in defpun.lisp.

(in-package "ACL2")

(defstub
  test (*) => *)

(defstub
  base (*) => *)

(defstub
  st (*) => *)

(defstub
    h-fix () => *)

(encapsulate
 (((h * *) => *))

 (local
  (defun h (x y$)
    (declare (ignore x y$))
    (h-fix)))

 (defthm
   h-fix-is-fixed-point
   (equal (h x (h-fix))(h-fix)))
 ) ;; end encapsulate

(defun stn (x n)
  (if (zp n) x (stn (st x) (1- n))))

(defchoose fch (n) (x)
	   (test (stn x n)))

(defun fn (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (test x))
      (base x)
      (h x (fn (st x) (1- n)))))

(defun f (x)
  (if (test (stn x (fch x)))
      (fn x (fch x))
      (h-fix)))

;;; This proof of generic-primitive-recursive-f is a minor
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
;;  Also not needed for proof of generic-primitive-recursive-f.
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

 (defthm generic-primitive-recursive-f
     (equal (f x)
	    (if (test x) (base x) (h x (f (st x)))))
     :hints
     (("subgoal 2" :expand (fn x (fch x)))
      ("subgoal 2.2'" :use
		      ((:instance fn-st (x (st x))
				  (n (+ -1 (fch x)))
				  (m (fch (st x)))))))
     :rule-classes nil)
 ) ;; end encapsulate

;; Example 1. Pete & J's cons example (modified).
#|
No ACL2 function g satisfies this equation:
(equal (g x)
       (if (equal x 0)
	   nil
	   (cons nil (g (- x 1)))))

The ``problem'' from the point of view of this note is that cons
does not have a right fixed point, so one is provided by the
following:
|#

(defstub
    cons-fix () => *)

(defun
    cons$ (x y)
    (if (equal y (cons-fix))
	(cons-fix)
        (cons x y)))

;; The following equation has an ACL2 solution for g.
#|
(equal (g x)
       (if (equal x 0)
	   nil
	   (cons$ nil (g (- x 1)))))
|#

(encapsulate
 (((g *) => *))

 (set-ignore-ok t)

 (set-irrelevant-formals-ok t)

 (local
  (defun
      g-test (x)
      (equal x 0)))

 (local
  (defun
      g-base (x)
      nil))

 (local
  (defun
      g-st (x)
      (- x 1)))

 (local
  (defun
      g-h-fix ()
      (cons-fix)))

 (local
  (in-theory (disable (:executable-counterpart g-h-fix))))

 (local
  (defun
      g-h (x y$)
      (cons$ nil y$)))

 (local
  (defun
      g-stn (x n)
      (if (zp n) x (g-stn (g-st x) (1- n)))))

 (local
  (defchoose
      g-fch (n) (x)
      (g-test (g-stn x n))))

 (local
  (defun
      g-fn (x n)
      (declare (xargs :measure (nfix n)))
      (if (or (zp n) (g-test x))
	  (g-base x)
	  (g-h x (g-fn (g-st x) (1- n))))))

 (local
  (defun
      g (x)
      (if (g-test (g-stn x (g-fch x)))
	  (g-fn x (g-fch x))
          (g-h-fix))))

 (defthm
   g-def
   (equal (g x)
	  (if (equal x 0)
	      nil
	    (cons$ nil (g (- x 1)))))
   :rule-classes :definition
   :hints (("Goal"
	    :use (:functional-instance
		  generic-primitive-recursive-f
		  (f g)
		  (test g-test)
		  (base g-base)
		  (h-fix g-h-fix)
		  (h g-h)
		  (st g-st)
		  (stn g-stn)
		  (fch g-fch)
		  (fn g-fn)))
	   ("Subgoal 2"
	    :use g-fch)))
 ) ;; end encapsulate

;; Example 2. Naive Factorial
;;  This example illustrates that any fixed point will do:
;;   Multiplication already has a right fixed point, namely 0.
;;   That is (* x 0) = 0.
;;  The following equation has an ACL2 solution for fact.
#|
(equal (fact x)
       (if (equal x 0)
	   1
	   (* x (fact (- x 1)))))
|#
#| Note:
   ACL2 would accept the definition that uses the zero-test idiom
    (zp x) in place of the test (equal x 0):

(defun
    fact (x)
    (if (zp x)
	1
        (* x (fact (- x 1)))))
|#

(encapsulate
 (((fact *) => *))

 (set-ignore-ok t)

 (set-irrelevant-formals-ok t)

 (local
  (defun
      fact-test (x)
      (equal x 0)))

 (local
  (defun
      fact-base (x)
      1))

 (local
  (defun
      fact-st (x)
      (- x 1)))

 (local
  (defun
      fact-h-fix ()
      0))

 (local
  (in-theory (disable (:executable-counterpart fact-h-fix))))

 (local
  (defun
      fact-h (x y$)
      (* x y$)))

 (local
  (defun
      fact-stn (x n)
      (if (zp n) x (fact-stn (fact-st x) (1- n)))))

 (local
  (defchoose
      fact-fch (n) (x)
      (fact-test (fact-stn x n))))

 (local
  (defun
      fact-fn (x n)
      (declare (xargs :measure (nfix n)))
      (if (or (zp n) (fact-test x))
	  (fact-base x)
	  (fact-h x (fact-fn (fact-st x) (1- n))))))

 (local
  (defun
      fact (x)
      (if (fact-test (fact-stn x (fact-fch x)))
	  (fact-fn x (fact-fch x))
          (fact-h-fix))))

 (defthm
   fact-def
   (equal (fact x)
	  (if (equal x 0)
	      1
	      (* x (fact (- x 1)))))
   :rule-classes :definition
   :hints (("Goal"
	    :use (:functional-instance
		  generic-primitive-recursive-f
		  (f fact)
		  (test fact-test)
		  (base fact-base)
		  (h-fix fact-h-fix)
		  (h fact-h)
		  (st fact-st)
		  (stn fact-stn)
		  (fch fact-fch)
		  (fn fact-fn)))
	   ("Subgoal 2"
	    :use fact-fch)))
 ) ;; end encapsulate

;; Example 3. Example with parameters.
;;   A naive version of the recursive equation added to ACL2
;;   by the following definition.
#|
(defun
    k (a b)
    (if (zp b)
        1
        (* a b (k a (- b 1)))))
|#
;; The following equation has an ACL2 solution for k.
#|
(equal (k a b)
       (if (equal b 0)
           1
           (* a b (k a (- b 1)))))
|#
(encapsulate
 (((k * *) => *))

 (set-ignore-ok t)

 (set-irrelevant-formals-ok t)

 (local
  (defun
      k-arity-1-test (x)
      (let ((a (car x))
	    (b (cadr x)))
	   (equal b 0))))

 (local
  (defun
      k-arity-1-base (x)
      (let ((a (car x))
	    (b (cadr x)))
	   1)))

 (local
  (defun
      k-arity-1-st (x)
      (let ((a (car x))
	    (b (cadr x)))
	   (list a (- b 1)))))

 (local
  (defun
      k-arity-1-h-fix ()
      0))

 (local
  (in-theory (disable (:executable-counterpart k-arity-1-h-fix))))

 (local
  (defun
      k-arity-1-h (x y$)
      (let ((a (car x))
	    (b (cadr x)))
      (* a b y$))))

 (local
  (encapsulate
   (((k-arity-1 *) => *))

   (local
    (defun
	k-arity-1-stn (x n)
        (if (zp n) x (k-arity-1-stn (k-arity-1-st x) (1- n)))))

   (local
    (defchoose
	k-arity-1-fch (n) (x)
	(k-arity-1-test (k-arity-1-stn x n))))

   (local
    (defun
	k-arity-1-fn (x n)
        (declare (xargs :measure (nfix n)))
	(if (or (zp n) (k-arity-1-test x))
	    (k-arity-1-base x)
	  (k-arity-1-h x (k-arity-1-fn (k-arity-1-st x)
				       (1- n))))))

   (local
    (defun
	k-arity-1 (x)
        (if (k-arity-1-test (k-arity-1-stn x (k-arity-1-fch x)))
	    (k-arity-1-fn x (k-arity-1-fch x))
            (k-arity-1-h-fix))))

   (defthm
       k-arity-1-def
       (equal (k-arity-1 x)
	      (if (k-arity-1-test x)
		  (k-arity-1-base x)
		(k-arity-1-h x (k-arity-1 (k-arity-1-st x)))))
       :rule-classes nil
       :hints (("Goal"
		:use (:functional-instance
		      generic-primitive-recursive-f
		      (f k-arity-1)
		      (test k-arity-1-test)
		      (base k-arity-1-base)
		      (h-fix k-arity-1-h-fix)
		      (h k-arity-1-h)
		      (st k-arity-1-st)
		      (stn k-arity-1-stn)
		      (fch k-arity-1-fch)
		      (fn k-arity-1-fn)))
	       ("Subgoal 2"
		:use k-arity-1-fch)))
   ) ;; end encapsulate
  ) ;; end local

 (local
  (defun
      k (a b)
      (k-arity-1 (list a b))))

 (defthm
     k-def
     (equal (k a b)
	    (if (equal b 0)
		1
	        (* a b (k a (- b 1)))))
     :rule-classes :definition
     :hints (("Goal"
	      :use (:instance
		    k-arity-1-def
		    (x (list a b))))))
 ) ;; end encapsulate

