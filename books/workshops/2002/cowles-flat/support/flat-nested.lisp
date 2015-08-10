; Introduction of an arbitrary nested-recursive function.
;  Construction based on flat domains in ACL2.
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
;  Last modified 20 December 2001.
#|
 To certify (originally in ACL2 Version 2.6):
 (defpkg
     "FLAT" (union-eq
	      *acl2-exports*
	      *common-lisp-symbols-from-main-lisp-package*))

 (certify-book "flat-nested" 1 nil ; compile-flg
	       :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
(in-package "FLAT")
(include-book "flat")
#|
A construction based on flat domains in ACL2, as introduced in
flat.lisp, of a function f that satisfies the equation, for
strict functions (test x), in the following theorem,

(defthm generic-nested-recursive-f
    (equal (f x)
	   (sq-if (test x) (base x) (f (f (st x)))))).
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proceed with the construction:

(defmacro
  sq-if (test then else)
  "Sequential version of IF."
   `(if (equal ,test ($bottom$))
        ($bottom$)
        (if ,test ,then ,else)))

(encapsulate
 (((test *) => *))

 (local
  (defun
      test (x)
      (declare (ignore x))
      ($bottom$)))

 (defthm
     test-is-strict
     (equal (test ($bottom$))($bottom$)))
 ) ;; end encapsulate

(defstub
  base (*) => *)

(defstub
  st (*) => *)

(defun
    f-chain (i x)
    (if (zp i)
	($bottom$)
        (sq-if (test x)
	       (base x)
	       (f-chain (- i 1)(f-chain (- i 1)(st x))))))

(defthm
    base-of-f-chain=$bottom$
    (implies (zp i)
	     (equal (f-chain i x)
		    ($bottom$))))

(defthm
    f-chain-is-$<=$-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (f-chain i x)
		   (f-chain (+ 1 i) x))))

;; Choose an ``index'' for definition of lub of f-chain:

(defchoose
    lub-f-chain-i i (x)
    (not (equal (f-chain i x)
		($bottom$))))

(defthm
    lub-f-chain-i-rewrite
    (implies (equal (f-chain (lub-f-chain-i x) x)
		    ($bottom$))
	     (equal (f-chain i x) ($bottom$)))
    :hints (("Goal"
	     :use lub-f-chain-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-f-chain-nat-i (x)
    (nfix (lub-f-chain-i x)))

;; Define the least upper bound of f-chain:

(defun
    lub-f-chain (x)
    (f-chain (lub-f-chain-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-f-chain)))

(defthm
    lub-f-chain-is-upper-bound
    ($<=$ (f-chain i x)
	  (lub-f-chain x))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      lub-$bottom$-based-chain-is-upper-bound
	      ($bottom$-based-chain f-chain)
	      (lub-$bottom$-based-chain lub-f-chain)
	      (lub-$bottom$-based-chain-nat-i lub-f-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-f-chain-i)))
	    ("Subgoal 2"
	     :use f-chain-is-$<=$-chain)))

(defthm
    f-chain-is-$<=$-chain-f
    (implies (and (>= i (lub-f-chain-nat-i x))
		  (integerp i))
	     (equal (lub-f-chain x)
		    (f-chain i x)))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      $bottom$-based-chain-is-$<=$-chain-f
	      ($bottom$-based-chain f-chain)
	      (lub-$bottom$-based-chain lub-f-chain)
	      (lub-$bottom$-based-chain-nat-i lub-f-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-f-chain-i)))))

(defun
    f (x)
    (lub-f-chain x))

(defun
    g-chain (i x)
    (f-chain (+ 1 i) x))

(defun
    ub-g-chain (x)
    (sq-if (test x)
	   (base x)
	   (f (f (st x)))))

(defthm
    g-chain-$<=$-ub-g-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (g-chain i x)
		   (ub-g-chain x)))
    :hints (("Subgoal 2"
	     :in-theory (disable lub-f-chain-is-upper-bound)
	     :use ((:instance
		    lub-f-chain-is-upper-bound
		    (x (st x)))
		   (:instance
		    lub-f-chain-is-upper-bound
		    (x (f (st x))))))))

(defun
    Skolem-f (x)
    (max (lub-f-chain-nat-i (st x))
	 (lub-f-chain-nat-i (f (st x)))))

(defthm
    ub-g-chain-=-g-chain-Skolem-f
    (equal (ub-g-chain x)
	   (g-chain (Skolem-f x) x))
  :hints (("Goal"
	   :use ((:instance
		  f-chain-is-$<=$-chain-f
		  (x (st x))
		  (i (Skolem-f x)))
		 (:instance
		  f-chain-is-$<=$-chain-f
		  (x (f (st x)))
		  (i (Skolem-f x)))))))

(defthm
    lub-f-chain=ub-g-chain
    (equal (lub-f-chain x)(ub-g-chain x))
    :rule-classes nil
    :hints (("Goal"
	     :by
	     (:functional-instance
	      lub-$chain$=ub-shifted-$chain$
	      ($chain$ f-chain)
	      (lub-$chain$ lub-f-chain)
	      (lub-$chain$-i lub-f-chain-i)
	      (lub-$chain$-nat-i lub-f-chain-nat-i)
	      ($f$ Skolem-f)
	      (shifted-$chain$ g-chain)
	      (ub-shifted-$chain$ ub-g-chain)))
	    ("Subgoal 5"
	     :use g-chain-$<=$-ub-g-chain)
	    ("Subgoal 4"
	     :use f-chain-is-$<=$-chain)
	    ))

(defthm
    generic-nested-recursive-f
    (equal (f x)
	   (sq-if (test x)
		  (base x)
		  (f (f (st x)))))
    :hints (("Goal"
	     :in-theory (disable lub-f-chain
				 ub-g-chain-=-g-chain-Skolem-f)
	     :use lub-f-chain=ub-g-chain)))
