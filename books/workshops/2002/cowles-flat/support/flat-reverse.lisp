; Introduction of a function satisfying a slightly altered version
;  of the Ashcroft recursive equation for reverse.
; Copyright (C) 2001  John R. Cowles, University of Wyoming

;  Original Ashcroft recursive equation for reverse:

;  (equal (f x)
;         (if (equal x nil)
;             x
;             (if (equal (cdr x) nil)
;                 x
;                 (let* ((a (car x))
;                        (b (f (cdr x)))
;                        (c (car b))
;                        (y (f (cdr b))))
;                       (cons c (f (cons a y)))))))

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
;  Last modified 28 December 2001.

#|
 To certify (originally in ACL2 Version 2.6):
 (defpkg
     "FLAT" (union-eq
	      *acl2-exports*
	      *common-lisp-symbols-from-main-lisp-package*))

 (certify-book "flat-reverse" 1 nil ; compile-flg
	       :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
(in-package "FLAT")
(include-book "flat")

#| We want a function that satisfies Ashcroft's recursive
    equation for reverse:

(equal (f x)
       (if (equal x nil)
	   x
	   (if (equal (cdr x) nil)
	       x
	       (let* ((a (car x))
		      (b (f (cdr x)))
		      (c (car b))
		      (y (f (cdr b))))
		     (cons c (f (cons a y)))))))
|#


#||

[Jared]: fool make_cert_help into allowing more memory for this book.

(set-max-mem (* 6 (expt 2 30)))

||#

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
    st-car (x)
    "Strict version of car."
    `(if (eq ,x 'undef$)
	 'undef$
         (car ,x)))

(defmacro
    st-cdr (x)
    "Strict version of cdr."
    `(if (eq ,x 'undef$)
	 'undef$
         (cdr ,x)))

(defmacro
    rt-st-cons (x y)
    "Right-strict version of cons."
    `(if (eq ,y 'undef$)
	 'undef$
         (cons ,x ,y)))

(defmacro
    st-cons (x y)
    "Strict version of cons."
    `(cond ((eq ,x 'undef$) 'undef$)
	   ((eq ,y 'undef$) 'undef$)
	   (t (cons ,x ,y))))

#| Our heuristics say it should be possible to get this:

(equal (f x)
       (if (equal x nil)
	   x
	   (sq-if (lt-st-equal (st-cdr x) nil)
		  x
		  (let* ((a (car x))
			 (b (f (cdr x)))
			 (c (st-car b))
			 (y (f (st-cdr b))))
		        (st-cons c (f (rt-st-cons a y)))))))
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

(defun
    f-chain (i x)
    (if (zp i)
	'undef$
        (if (equal x nil)
	    x
	    (sq-if (lt-st-equal (st-cdr x) nil)
		   x
		   (let* ((a (car x))
			  (b (f-chain (- i 1)(cdr x)))
			  (c (st-car b))
			  (y (f-chain (- i 1)(st-cdr b))))
		         (st-cons c (f-chain (- i 1)
					     (rt-st-cons a y))))))
	))

(defthm
    base-of-f-chain=undef$
    (implies (zp i)
	     (equal (f-chain i x)
		    'undef$)))

(defthm
    f-chain-is-<def=-chain
    (implies (and (integerp i)
		  (>= i 0))
	     (<def= (f-chain i x)
		    (f-chain (+ 1 i) x))))

;; Choose an ``index'' for definition of lub of f-chain:

(defchoose
    lub-f-chain-i i (x)
    (not (equal (f-chain i x)
		'undef$)))

(defthm
    lub-f-chain-i-rewrite
    (implies (equal (f-chain (lub-f-chain-i x) x)
		    'undef$)
	     (equal (f-chain i x) 'undef$))
    :hints (("Goal"
	     :use lub-f-chain-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-f-chain-nat-i (x)
    (nfix (lub-f-chain-i x)))

(in-theory (disable (:executable-counterpart
		     lub-f-chain-nat-i)))

;; Define the least upper bound of f-chain:

(defun
    lub-f-chain (x)
    (f-chain (lub-f-chain-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-f-chain)))

(defthm
    lub-f-chain-is-upper-bound
    (<def= (f-chain i x)
	   (lub-f-chain x))
    :hints (("Goal"
             :by
	     (:functional-instance
	      lub-$bottom$-based-chain-is-upper-bound
	      ($<=$ <def=)
	      ($bottom$ (lambda () 'undef$))
	      ($bottom$-based-chain f-chain)
	      (lub-$bottom$-based-chain lub-f-chain)
	      (lub-$bottom$-based-chain-nat-i lub-f-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-f-chain-i)))

	    ("Subgoal 2" ; changed after v4-3 from "Subgoal 3", for tau system
	     :use f-chain-is-<def=-chain)))

(defthm
    f-chain-is-<def=-chain-f
    (implies (and (>= i (lub-f-chain-nat-i x))
		  (integerp i))
	     (equal (lub-f-chain x)
		    (f-chain i x)))
    :hints (("Goal"
             :by
	     (:functional-instance
	      $bottom$-based-chain-is-$<=$-chain-f
	      ($<=$ <def=)
	      ($bottom$ (lambda () 'undef$))
	      ($bottom$-based-chain f-chain)
	      (lub-$bottom$-based-chain lub-f-chain)
	      (lub-$bottom$-based-chain-nat-i lub-f-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-f-chain-i)))))

(defun
    f (x)
    (lub-f-chain x))

(in-theory (disable (:executable-counterpart f)))

(defun
    g-chain (i x)
    (f-chain (+ 1 i) x))

(defun
    ub-g-chain (x)
    (if (equal x nil)
	x
        (sq-if (lt-st-equal (st-cdr x) nil)
	       x
	       (let* ((a (car x))
		      (b (f (cdr x)))
		      (c (st-car b))
		      (y (f (st-cdr b))))
		     (st-cons c (f (rt-st-cons a y)))))))

(defthm
    g-chain-<def=-ub-g-chain
    (implies (and (integerp i)
		  (>= i 0))
	     (<def= (g-chain i x)
		    (ub-g-chain x)))
    :hints (("Subgoal 2"
	     :in-theory (disable lub-f-chain-is-upper-bound)
	     :use ((:instance
		    lub-f-chain-is-upper-bound
		    (x (rt-st-cons (car x)
				   (f (st-cdr (f (cdr x)))))))
		   (:instance
		    lub-f-chain-is-upper-bound
		    (x (st-cdr (f (cdr x)))))
		   (:instance
		    lub-f-chain-is-upper-bound
		    (x (cdr x)))))))

(defun
    Skolem-f (x)
    (max (lub-f-chain-nat-i (cdr x))
	 (max (lub-f-chain-nat-i (st-cdr (f (cdr x))))
	      (lub-f-chain-nat-i (rt-st-cons
				  (car x)
				  (f (st-cdr (f (cdr x)))))))))

(defthm
    ub-g-chain-=-g-chain-Skolem-f
    (equal (ub-g-chain x)
	   (g-chain (Skolem-f x) x))
    :hints (("Goal"
	     :use ((:instance
		    f-chain-is-<def=-chain-f
		    (x (cdr x))
		    (i (Skolem-f x)))
		   (:instance
		    f-chain-is-<def=-chain-f
		    (x (st-cdr (f (cdr x))))
		    (i (Skolem-f x)))
		   (:instance
		    f-chain-is-<def=-chain-f
		    (x (rt-st-cons
			(car x)
			(f (st-cdr (f (cdr x))))))
		    (i (Skolem-f x)))))))

(defthm
    lub-f-chain=ub-g-chain
    (equal (lub-f-chain x)(ub-g-chain x))
    :rule-classes nil
    :hints (("Goal"
             :by
	     (:functional-instance
	      lub-$chain$=ub-shifted-$chain$
	      ($<=$ <def=)
	      ($bottom$ (lambda () 'undef$))
	      ($chain$ f-chain)
	      (lub-$chain$ lub-f-chain)
	      (lub-$chain$-i lub-f-chain-i)
	      (lub-$chain$-nat-i lub-f-chain-nat-i)
	      ($f$ Skolem-f)
	      (shifted-$chain$ g-chain)
	      (ub-shifted-$chain$ ub-g-chain)))
	    ("Subgoal 4" ; changed after v4-3 from "Subgoal 5", for tau system
	     :use g-chain-<def=-ub-g-chain)
	    ("Subgoal 3" ; changed after v4-3 from "Subgoal 4", for tau system
	     :use f-chain-is-<def=-chain)
	    ))

(defthm
    f-def
    (equal (f x)
	   (if (equal x nil)
	       x
	       (sq-if (lt-st-equal (st-cdr x) nil)
		      x
		      (let* ((a (car x))
			     (b (f (cdr x)))
			     (c (st-car b))
			     (y (f (st-cdr b))))
		            (st-cons c (f (rt-st-cons a y)))))))
    :hints (("Goal"
	     :in-theory (disable ub-g-chain-=-g-chain-Skolem-f)
	     :use lub-f-chain=ub-g-chain)))

#| Recall the original Ashcroft version of a recursive equation
    for reverse:

(equal (f x)
       (if (equal x nil)
	   x
	   (if (equal (cdr x) nil)
	       x
	       (let* ((a (car x))
		      (b (f (cdr x)))
		      (c (car b))
		      (y (f (cdr b))))
		     (cons c (f (cons a y)))))))
|#

(in-theory (disable f f-def))

(defthm
  f=Ashcroft-def
  (implies (and (true-listp x)
		(true-listp (f (cdr x)))
		(not (equal (car (f (cdr x))) 'undef$))
		(not (equal (f (cdr (f (cdr x)))) 'undef$))
		(not (equal (f (cons (car x)(f (cdr (f (cdr x))))))
			    'undef$)))
	   (equal (f x)
		  (if (equal x nil)
		      x
		      (if (equal (cdr x) nil)
			  x
			  (let* ((a (car x))
				 (b (f (cdr x)))
				 (c (car b))
				 (y (f (cdr b))))
			        (cons c (f (cons a y))))))))
 :hints (("Goal"
	  :use f-def)))
