; Introduction of the partial function Z defined by
;     (Z x) <== (if (equal x 0)
;                   0
;                   (* (Z (- x 1))(Z (+ x 1)))).
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
;  Last modified 28 December 2001.
#|
 To certify (originally in ACL2 Version 2.6):
 (defpkg
     "FLAT" (union-eq
	      *acl2-exports*
	      *common-lisp-symbols-from-main-lisp-package*))

 (certify-book "flat-z" 1 nil ; compile-flg
	       :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
(in-package "FLAT")
(include-book "flat")
#|
A construction based on flat domains in ACL2, as introduced in
flat.lisp, of a function Z that satisfies the equation,

           (equal (Z x)
	          (if (equal x 0)
	              0
	              (* (Z (- x 1))(Z (+ x 1)))).
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

;; Zero plays the part of ($bottom$)

(defun
    $0<=$ (x y)
    (or (equal x 0)
	(equal x y)))

(defun
    Z-chain (i x)
    (if (zp i)
	0
        (if (equal x 0)
	    0
	    (* (Z-chain (- i 1)(- x 1))
	       (Z-chain (- i 1)(+ x 1))))))

(defthm
    base-of-Z-chain=0
    (implies (zp i)
	     (equal (Z-chain i x)
		    0)))

(defthm
    Z-chain-is-$0<=$-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($0<=$ (Z-chain i x)
		    (Z-chain (+ 1 i) x))))

;; Choose an ``index'' for definition of lub of Z-chain:

(defchoose
    lub-Z-chain-i i (x)
    (not (equal (Z-chain i x)
		0)))

(defthm
    lub-Z-chain-i-rewrite
    (implies (equal (Z-chain (lub-Z-chain-i x) x)
		    0)
	     (equal (Z-chain i x) 0))
    :hints (("Goal"
	     :use lub-Z-chain-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-Z-chain-nat-i (x)
    (nfix (lub-Z-chain-i x)))

;; Define the least upper bound of f-chain:

(defun
    lub-Z-chain (x)
    (Z-chain (lub-Z-chain-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-Z-chain)))

(defthm
    lub-Z-chain-is-upper-bound
    ($0<=$ (Z-chain i x)
	   (lub-Z-chain x))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      lub-$bottom$-based-chain-is-upper-bound
	      ($bottom$ (lambda () 0))
	      ($<=$ $0<=$)
	      ($bottom$-based-chain Z-chain)
	      (lub-$bottom$-based-chain lub-Z-chain)
	      (lub-$bottom$-based-chain-nat-i lub-Z-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-Z-chain-i)))
	    ("Subgoal 2"
	     :use Z-chain-is-$0<=$-chain)))

(defthm
    Z-chain-is-$0<=$-chain-f
    (implies (and (>= i (lub-Z-chain-nat-i x))
		  (integerp i))
	     (equal (lub-Z-chain x)
		    (Z-chain i x)))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      $bottom$-based-chain-is-$<=$-chain-f
	      ($bottom$ (lambda () 0))
	      ($<=$ $0<=$)
	      ($bottom$-based-chain Z-chain)
	      (lub-$bottom$-based-chain lub-Z-chain)
	      (lub-$bottom$-based-chain-nat-i lub-Z-chain-nat-i)
	      (lub-$bottom$-based-chain-i lub-Z-chain-i)))))

(defun
    Z (x)
    (lub-Z-chain x))

(defun
    g-chain (i x)
    (Z-chain (+ 1 i) x))

(defun
    ub-g-chain (x)
    (if (equal x 0)
	0
        (* (Z (- x 1))
	   (Z (+ x 1)))))

(defthm
    g-chain-$0<=$-ub-g-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($0<=$ (g-chain i x)
		    (ub-g-chain x)))
    :hints (("Subgoal 2"
	     :in-theory (disable lub-Z-chain-is-upper-bound)
	     :use ((:instance
		    lub-Z-chain-is-upper-bound
		    (x (- x 1)))
		   (:instance
		    lub-Z-chain-is-upper-bound
		    (x (+ x 1)))))))

(defun
    Skolem-Z (x)
    (max (lub-Z-chain-nat-i (- x 1))
	 (lub-Z-chain-nat-i (+ x 1))))

(defthm
    ub-g-chain-=-g-chain-Skolem-Z
    (equal (ub-g-chain x)
	   (g-chain (Skolem-Z x) x))
  :hints (("Goal"
	   :use ((:instance
		  Z-chain-is-$0<=$-chain-f
		  (x (- x 1))
		  (i (Skolem-Z x)))
		 (:instance
		  Z-chain-is-$0<=$-chain-f
		  (x (+ x 1))
		  (i (Skolem-Z x)))))))

(defthm
    lub-Z-chain=ub-g-chain
    (equal (lub-Z-chain x)(ub-g-chain x))
    :rule-classes nil
    :hints (("Goal"
	     :by
	     (:functional-instance
	      lub-$chain$=ub-shifted-$chain$
	      ($bottom$ (lambda () 0))
	      ($<=$ $0<=$)
	      ($chain$ Z-chain)
	      (lub-$chain$ lub-Z-chain)
	      (lub-$chain$-i lub-Z-chain-i)
	      (lub-$chain$-nat-i lub-Z-chain-nat-i)
	      ($f$ Skolem-Z)
	      (shifted-$chain$ g-chain)
	      (ub-shifted-$chain$ ub-g-chain)))
	    ("Subgoal 5"
	     :use g-chain-$0<=$-ub-g-chain)
	    ("Subgoal 4"
	     :use Z-chain-is-$0<=$-chain)
	    ))

(defthm
    Z-axiom
    (equal (Z x)
	   (if (equal x 0)
	       0
	       (* (Z (- x 1))
		  (Z (+ x 1)))))
    :hints (("Goal"
	     :in-theory (disable lub-Z-chain
				 ub-g-chain-=-g-chain-Skolem-Z)
	     :use lub-Z-chain=ub-g-chain)))
