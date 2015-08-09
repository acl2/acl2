; Introduction of a function satisfying a slightly altered version
;  of the Ackermann recursive equation.
; Copyright (C) 2001  John R. Cowles, University of Wyoming

;  Original Peter version of the Ackermann recursive equation:

;        (equal (f x1 x2)
;               (if (equal x1 0)
;                   (+ x2 1)
;                   (if (equal x2 0)
;                       (f (- x1 1) 1)
;                       (f (- x1 1)(f x1 (- x2 1))))))

;  Construction based on flat domains in ACL2.

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
;  Modified 28 December 2001.
;  Last modified 2 March 2002.

#|
 To certify (originally in ACL2 Version 2.6):
 (defpkg
     "FLAT" (union-eq
	     *acl2-exports*
	     *common-lisp-symbols-from-main-lisp-package*))

 (certify-book "flat-ackermann" 1 nil ; compile-flg
	       :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
(in-package "FLAT")
(include-book "flat")

#| We want a function that satisfies the original Peter version of
    the Ackermann recursive equation:
(equal (f x1 x2)
       (if (equal x1 0)
	   (+ x2 1)
	   (if (equal x2 0)
	       (f (- x1 1) 1)
	       (f (- x1 1)(f x1 (- x2 1))))))
|#

(defun
    <def= (x y)
    (or (eq x 'undef$)
	(equal x y)))

(defmacro
  sq-if (test then else)
  "Sequential version of IF."
   `(if (eq ,test 'undef$)
        'undef$
        (if ,test ,then ,else)))

(defmacro
    lt-st-equal (x y)
    "Left-strict version of equal."
    `(if (eq ,x 'undef$)
	 'undef$
         (equal ,x ,y)))

(defmacro
    lt-st-+ (x y)
    "Left-strict version of (binary) +."
    `(if (eq ,x 'undef$)
	 'undef$
         (+ ,x ,y)))

#| Our heuristics say it should be possible to get this:
(equal (f x1 x2)
       (if (equal x1 0)
	   (+ x2 1)
	   (sq-if (lt-st-equal x2 0)
		  (f (- x1 1) 1)
		  (f (- x1 1)(f x1 (- x2 1))))))
|#
#| Our heuristics are too primitive:
   In fact we can get define a function f that satisfies:
(equal (f x1 x2)
       (if (equal x1 0)
	   (lt-st-+ x2 1)
	   (sq-if (lt-st-equal x2 0)
		  (f (- x1 1) 1)
		  (f (- x1 1)(f x1 (- x2 1))))))

 Recall that we wanted a function that satisfies the original
  Peter version of the Ackermann recursive equation:
(equal (f x1 x2)
       (if (equal x1 0)
	   (+ x2 1)
	   (if (equal x2 0)
	       (f (- x1 1) 1)
	       (f (- x1 1)(f x1 (- x2 1))))))

 ACL2 can then prove the following, which is close to what we
 had hoped for:

(implies (not (equal x2 'undef$))
	 (equal (f x1 x2)
		(if (equal x1 0)
		    (+ x2 1)
		    (if (equal x2 0)
			(f (- x1 1) 1)
		        (f (- x1 1)(f x1 (- x2 1)))))))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Add some basic arithmetic facts:

(local
 (defthm
   commutativity-2-of-+
   (equal (+ x y z)
	  (+ y x z))))

(local
 (defthm
   associate-constants-left-+
   (implies (and (syntaxp (quotep x))
		 (syntaxp (quotep y)))
	    (equal (+ x (+ y z))
		   (+ (+ x y) z)))))

(local
 (defthm
   minus-inverse-+-a
   (implies (acl2-numberp y)
	    (equal (+ (- x) x y)
		   y))))

(local
 (defthm
   minus-inverse-+-b
   (implies (acl2-numberp y)
	    (equal (+ x (- x) y)
		   y))))

#| Preliminary test for suitability of definition:
(defun
    f21-chain (i x1 x2)
    (if (zp i)
	'undef$
        (if (equal x1 0)
	    (lt-st-+ x2 1)
            (sq-if (lt-st-equal x2 0)
		   (f21-chain (- i 1)(- x1 1) 1)
		   (f21-chain (- i 1)(- x1 1)
			      (f21-chain (- i 1) x1
					 (- x2 1)))))))

(thm
 (<def= (f21-chain i x1 x2)
	(f21-chain (+ 1 i) x1 x2)))
|#
#| Unary version of what we want:
(equal f1 (x)
       (let ((x1 (car x))
	     (x2 (cadr x)))
	    (if (equal x1 0)
		(lt-st-+ x2 1)
	        (sq-if (lt-st-equal x2 0)
		       (f1 (list (- x1 1) 1))
		       (f1 (list (- x1 1)
				 (f1 (list x1 (- x2 1)))))))))

Heuristics suggest that second list should be right strict.
|#

(defmacro
    rt-st-list (x y)
    "Right-strict version of (binary) list."
    `(if (eq ,y 'undef$)
	 'undef$
         (list ,x ,y)))

(defun
    f1-chain (i x)
    (if (zp i)
	'undef$
        (if (eq x 'undef$)  ;; Ensure f1 is strict and
	    'undef$         ;;  thus a monotonic function.
            (let ((x1 (car x))
		  (x2 (cadr x)))
	         (if (equal x1 0)
		     (lt-st-+ x2 1)
		     (sq-if (lt-st-equal x2 0)
			    (f1-chain (- i 1)
				      (list (- x1 1) 1))
			    (f1-chain
			     (- i 1)
			     (rt-st-list (- x1 1)
					 (f1-chain (- i 1)
						   (list
						    x1
						    (- x2 1))))
			     )))))))

(defthm
    base-of-f1-chain=undef$
    (implies (zp i)
	     (equal (f1-chain i x)
		    'undef$)))

(defthm
    f1-chain-is-<def=-chain
    (implies (and (integerp i)
		  (>= i 0))
	     (<def= (f1-chain i x)
		    (f1-chain (+ 1 i) x))))

;; Choose an ``index'' for definition of lub of f1-chain:

(defchoose
    lub-f1-chain-i i (x)
    (not (equal (f1-chain i x)
		'undef$)))

(defthm
    lub-f1-chain-i-rewrite
    (implies (equal (f1-chain (lub-f1-chain-i x) x)
		    'undef$)
	     (equal (f1-chain i x) 'undef$))
    :hints (("Goal"
	     :use lub-f1-chain-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-f1-chain-nat-i (x)
    (nfix (lub-f1-chain-i x)))

(in-theory (disable (:executable-counterpart
		     lub-f1-chain-nat-i)))

;; Define the least upper bound of f-chain:

(defun
    lub-f1-chain (x)
    (f1-chain (lub-f1-chain-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-f1-chain)))

(defthm
    lub-f1-chain-is-upper-bound
    (<def= (f1-chain i x)
	   (lub-f1-chain x))
    :hints (("Goal"
             :by
	     (:functional-instance
	      lub-$bottom$-based-chain-is-upper-bound
	      ($<=$ <def=)
	      ($bottom$ (lambda () 'undef$))
	      ($bottom$-based-chain f1-chain)
	      (lub-$bottom$-based-chain lub-f1-chain)
	      (lub-$bottom$-based-chain-nat-i lub-f1-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-f1-chain-i)))
	    ("Subgoal 2" ; changed after v4-3 from "Subgoal 3", for tau system
	     :use f1-chain-is-<def=-chain)))

(defthm
    f1-chain-is-<def=-chain-f
    (implies (and (>= i (lub-f1-chain-nat-i x))
		  (integerp i))
	     (equal (lub-f1-chain x)
		    (f1-chain i x)))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      $bottom$-based-chain-is-$<=$-chain-f
	      ($<=$ <def=)
	      ($bottom$ (lambda () 'undef$))
	      ($bottom$-based-chain f1-chain)
	      (lub-$bottom$-based-chain lub-f1-chain)
	      (lub-$bottom$-based-chain-nat-i lub-f1-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-f1-chain-i)))))

(defun
    f1 (x)
    (lub-f1-chain x))

(in-theory (disable (:executable-counterpart f1)))

(defthm
    f1-is-strict
    (equal (f1 'undef$) 'undef$))

(defun
    g1-chain (i x)
    (f1-chain (+ 1 i) x))

(defun
    ub-g1-chain (x)
  (if (eq x 'undef$)
      'undef$
      (let ((x1 (car x))
	    (x2 (cadr x)))
	   (if (equal x1 0)
	       (lt-st-+ x2 1)
	       (sq-if (lt-st-equal x2 0)
		      (f1 (list (- x1 1) 1))
		      (f1 (rt-st-list (- x1 1)
				      (f1 (list x1 (- x2 1))))
			  ))))))

(defthm
    g1-chain-<def=-ub-g1-chain
    (implies (and (integerp i)
		  (>= i 0))
	     (<def= (g1-chain i x)
		    (ub-g1-chain x)))
; fcd/Satriani v3.7 Moore - used to be Subgoal 8
    :hints (("Subgoal 2"
	     :in-theory (disable lub-f1-chain-is-upper-bound)
	     :use (:instance
		   lub-f1-chain-is-upper-bound
		   (x (list (- (car x) 1) 1))))
; fcd/Satriani v3.7 Moore - used to be Subgoal 3
	    ("Subgoal 6"
	     :in-theory (disable lub-f1-chain-is-upper-bound)
	     :use ((:instance
		    lub-f1-chain-is-upper-bound
		    (x (list (car x)(- (cadr x) 1))))
		   (:instance
		    lub-f1-chain-is-upper-bound
		    (x (list (- (car x) 1)
			     (f1-chain i (list (car x)
					       (- (cadr x) 1)))))
		    )))))

(defun
    Skolem-f1 (x)
    (max (lub-f1-chain-nat-i (list (- (car x) 1) 1))
	 (max (lub-f1-chain-nat-i (list (car x)(- (cadr x) 1)))
	      (lub-f1-chain-nat-i (rt-st-list (- (car x) 1)
					(f1 (list
					     (car x)
					     (- (cadr x) 1)))
					)))))

(defthm
    ub-g1-chain-=-g1-chain-Skolem-f1
    (equal (ub-g1-chain x)
	   (g1-chain (Skolem-f1 x) x))
  :hints (("Goal"
	   :use ((:instance
		  f1-chain-is-<def=-chain-f
		  (x (list (- (car x) 1) 1))
		  (i (Skolem-f1 x)))
		 (:instance
		  f1-chain-is-<def=-chain-f
		  (x (list (car x)(- (cadr x) 1)))
		  (i (Skolem-f1 x)))
		 (:instance
		  f1-chain-is-<def=-chain-f
		  (x (rt-st-list (- (car x) 1)
				 (f1 (list
				      (car x)
				      (- (cadr x) 1)))))
		  (i (Skolem-f1 x)))))))

(defthm
    lub-f1-chain=ub-g1-chain
    (equal (lub-f1-chain x)(ub-g1-chain x))
    :rule-classes nil
    :hints (("Goal"
             :by
             (:functional-instance
	      lub-$chain$=ub-shifted-$chain$
	      ($<=$ <def=)
	      ($bottom$ (lambda () 'undef$))
	      ($chain$ f1-chain)
	      (lub-$chain$ lub-f1-chain)
	      (lub-$chain$-i lub-f1-chain-i)
	      (lub-$chain$-nat-i lub-f1-chain-nat-i)
	      ($f$ Skolem-f1)
	      (shifted-$chain$ g1-chain)
	      (ub-shifted-$chain$ ub-g1-chain)))
	    ("Subgoal 4" ; changed after v4-3 from "Subgoal 5", for tau system
	     :use g1-chain-<def=-ub-g1-chain)
	    ("Subgoal 3" ; changed after v4-3 from "Subgoal 4", for tau system
	     :use f1-chain-is-<def=-chain)
	    ))

(defthm
    f1-def
    (equal (f1 x)
	   (if (eq x 'undef$)
	       'undef$
	       (let ((x1 (car x))
		     (x2 (cadr x)))
		    (if (equal x1 0)
			(lt-st-+ x2 1)
		        (sq-if (lt-st-equal x2 0)
			       (f1 (list (- x1 1) 1))
			       (f1 (rt-st-list (- x1 1)
					       (f1 (list x1
							 (- x2 1))
						   ))
				   ))))))
    :hints (("Goal"
	     :in-theory (disable ;;lub-f1-chain
				 ub-g1-chain-=-g1-chain-Skolem-f1)
	     :use lub-f1-chain=ub-g1-chain)))

(defun
    f (x1 x2)
    (f1 (list x1 x2)))

(defthm
    f-def
    (equal (f x1 x2)
	   (if (equal x1 0)
	       (lt-st-+ x2 1)
	       (sq-if (lt-st-equal x2 0)
		      (f (- x1 1) 1)
		      (f (- x1 1)(f x1 (- x2 1))))))
    :hints (("Goal"
	     :use (:instance
		   f1-def
		   (x (list x1 x2))))))

;  Recall the original Peter version of the Ackermann recursive
;   equation:

;        (equal (f x1 x2)
;               (if (equal x1 0)
;                   (+ x2 1)
;                   (if (equal x2 0)
;                       (f (- x1 1) 1)
;                       (f (- x1 1)(f x1 (- x2 1))))))

(in-theory (disable f f-def))

(defthm
  Peter-version-f-def
  (implies (not (equal x2 'undef$))
	   (equal (f x1 x2)
		  (if (equal x1 0)
		      (+ x2 1)
		      (if (equal x2 0)
			  (f (- x1 1) 1)
			  (f (- x1 1)(f x1 (- x2 1)))))))
  :hints (("Goal"
	   :use f-def)))
