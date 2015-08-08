; The ACL2 FLat Domain Book.
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

 (certify-book "flat"
               1
               nil ; compile-flg
	       :defaxioms-okp nil
	       :skip-proofs-okp nil)
|#
(in-package "FLAT")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Formalize a flat domain:

;; Impose a partial order on ACL2 data:
;;  Specify a least element, ($bottom$), in this
;;   partial order.  Thus ($bottom$) is strictly
;;   less than any other ACL2 datum.
;;  No other data items are related by this strict
;;   partial order.  Hence, the name ``flat'' comes
;;   from the standard graph of this order:

;;   ACL2 flat data:    o   o .... o   o
;;                       \  |      |  /
;;                        \ |      | /
;;                         ($bottom$)

;;   Items (represented by nodes) related by this
;;    strict partial order are connected by edges.
;;  In what follows, the reflexive closure, of this
;;   strict partial order, is denoted by $<=$.
;; ACL2 is used to verify that $<=$ is a reflexive
;;  partial order:
(defstub
  $bottom$ () => *)

(defun
  $<=$ (x y)
  (or (equal x ($bottom$))
      (equal x y)))

;; $<=$ is a reflexive partial order on the ACL2
;; universe:
#|
(thm ;; Reflexive
 ($<=$ x x))

(thm ;; Antisymmetric
 (implies (and ($<=$ x y)
	       ($<=$ y x))
	  (equal x y)))

(thm ;; Transitive
 (implies (and ($<=$ x y)
	       ($<=$ y z))
	  ($<=$ x z)))
|#
;; For each positive integer, n, the partial order
;;  $<=$ is extended elementwise to functions with
;;  n arguments, x_1,...,x_n:
;;  For functions $f$ and $g$,
;;     ($<=$ $f$ $g$) iff (for all x_1,...,x_n)
;;                        ($<=$ ($f$ x_1 ... x_n)
;;                              ($g$ x_1 ... x_n)).
;;
;;  Extended this way, $<=$ is a reflexive partial
;;  order on functions, with n arguments, with a
;;  least element, $bottom-n$. $Bottom-n$ is the
;;  constant function, with n arguments, that always
;;  returns the constant ($bottom$).
;; ACL2 is used to verify the above claims about
;;  about n-ary functions for n = 1.
#|
(defstub
    $f$ (*) => *)

(thm ;; Reflexive
 ($<=$ ($f$ x)($f$ x)))

(defun
  $bottom-1$ (x)
  (declare (ignore x))
  ($bottom$))

(thm ;; Least unary function.
 ($<=$ ($bottom-1$ x)
       ($f$ x)))
:ubt :x-1
(encapsulate
 ;; Antisymmetric:
 ;;  For functions $f$ and $g$,
 ;;   (implies (and ($<=$ $f$ $g$)
 ;;                 ($<=$ $g$ $f$))
 ;;            (equal $f$ $g$)))
 ((($f$ *) => *)
  (($g$ *) => *))

 (local
  (defun
      $f$ (x)
      (declare (ignore x))
      ($bottom$)))

 (local
  (defun
      $g$ (x)
      (declare (ignore x))
      ($bottom$)))

 (defthm
     $f$-$<=$-$g$
     ($<=$ ($f$ x)($g$ x))
     :rule-classes nil)

 (defthm
     $g$-$<=$-$f$
     ($<=$ ($g$ x)($f$ x))
     :rule-classes nil)
 ) ;; end encapsulate

(thm ;; Antisymmetric:
 (equal ($f$ x)($g$ x))
 :hints (("Goal"
	  :use ($f$-$<=$-$g$
		$g$-$<=$-$f$))))
:ubt :x
(encapsulate
 ;; Transitive:
 ;;  For functions $f$, $g$, and $h$,
 ;;   (implies (and ($<=$ $f$ $g$)
 ;;                 ($<=$ $g$ $h$))
 ;;            (equal $f$ $h$)))
 ((($f$ *) => *)
  (($g$ *) => *)
  (($h$ *) => *))

 (local
  (defun
      $f$ (x)
      (declare (ignore x))
      ($bottom$)))

 (local
  (defun
      $g$ (x)
      (declare (ignore x))
      ($bottom$)))

 (local
  (defun
      $h$ (x)
      (declare (ignore x))
      ($bottom$)))

 (defthm
     $f$-$<=$-$g$
     ($<=$ ($f$ x)($g$ x))
     :rule-classes nil)

 (defthm
     $g$-$<=$-$h$
     ($<=$ ($g$ x)($h$ x))
     :rule-classes nil)
 ) ;; end encapsulate

(thm ;; Transitive:
 ($<=$ ($f$ x)($h$ x))
 :hints (("Goal"
	  :use ($f$-$<=$-$g$
		$g$-$<=$-$h$))))
:ubt :x
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize functions $f$1 and $f$2 such that ($<=$ $f$1 $f$2).
;;  Prove some theorems about $f$1 $f$2.

(encapsulate
 ((($f$1 *) => *)
  (($f$2 *) => *))

 (local
  (defun
      $f$1 (x)
      (declare (ignore x))
      ($bottom$)))

 (local
  (defun
      $f$2 (x)
      (declare (ignore x))
      ($bottom$)))

 (defthm
     $f$1-$<=$-$f$2
     ($<=$ ($f$1 x)($f$2 x))
     :rule-classes nil)
 ) ;; end encapsulate

(defthm
    $f$1-$<=$-$f$2-a
    (implies (equal ($f$2 x) ($bottom$))
	     (equal ($f$1 x) ($bottom$)))
    :hints (("Goal"
	     :use $f$1-$<=$-$f$2)))

(defthm
    $f$1-$<=$-$f$2-b
    (implies (not (equal ($f$1 x) ($bottom$)))
	     (equal ($f$2 x)($f$1 x)))
    :hints (("Goal"
	     :use $f$1-$<=$-$f$2)))

(defthm
    $f$1-$<=$-$f$2-c
    (implies (and (equal ($f$1 x) y)
		  (not (equal y ($bottom$))))
	     (equal ($f$2 x)($f$1 x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize various situations involving unary
;;  functions indexed by nonnegative integers:
;;          f_0, f_1, ..., f_i, ... .
;; Indexed functions are formalized in ACL2 by
;;  treating the index as an argument to the
;;  function.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize a $<=$ upper-bound of an indexed set
;;  of functions:

(encapsulate
 (((f$1 * *) => *)
  ((ub-f$1 *) => *))

 (local
  (defun
      f$1 (i x)
      (declare (ignore i x))
      ($bottom$)))

 (local
  (defun
      ub-f$1 (x)
      (declare (ignore x))
      ($bottom$)))

 (defthm
     f$1-$<=$-ub-f$1
     ($<=$ (f$1 i x)(ub-f$1 x))
     :rule-classes nil)
 ) ;; end encapsulate

(defthm
    f$1-$<=$-ub-f$1-a
    (implies (equal (ub-f$1 x)($bottom$))
	     (equal (f$1 i x)($bottom$)))
    :hints (("Goal"
	     :use f$1-$<=$-ub-f$1)))

(defthm
    f$1-$<=$-ub-f$1-b
    (implies (not (equal (f$1 i x)($bottom$)))
	     (equal (ub-f$1 x)(f$1 i x)))
    :hints (("Goal"
	     :use f$1-$<=$-ub-f$1)))

(defthm
    f$1-$<=$-ub-f$1-c
    (implies (and (equal (f$1 i x) y)
		  (not (equal y ($bottom$))))
	     (equal (ub-f$1 x)(f$1 i x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize a $<=$-chain of functions with
;;  ($bottom$) base:

(encapsulate
 ((($bottom$-based-chain * *) => *))

 (local
  (defun
      $bottom$-based-chain (i x)
      (declare (ignore i x))
      ($bottom$)))

 (defthm
     base-of-$bottom$-based-chain=$bottom$
     (implies (zp i)
	      (equal ($bottom$-based-chain i x)
		     ($bottom$))))

 (defthm
     $bottom$-based-chain-is-$<=$-chain
     (implies (and (integerp i)
		   (>= i 0))
	      ($<=$ ($bottom$-based-chain i x)
		    ($bottom$-based-chain (+ 1 i)
					  x))))
 ) ;; end encapsulate

(defthm
    $bottom$-based-chain-i>0
    (implies (not (equal ($bottom$-based-chain i x)
			 ($bottom$)))
	     (> i 0))
    :rule-classes (:forward-chaining
		   :rewrite))

(defun
    induct-nat (x)
    (if (zp x)
	t
        (induct-nat (- x 1))))

(defthm
    $bottom$-based-chain-is-$<=$-chain-a
    (implies (and (integerp j)
		  (>= j 0))
	     ($<=$ ($bottom$-based-chain i x)
		   ($bottom$-based-chain (+ i j) x)))
    :hints (("Goal"
	     :induct (induct-nat j))
    	    ("Subgoal *1/2"
	     :use (:instance
		   $bottom$-based-chain-is-$<=$-chain
		   (i (+ -1 i j))))))

(defthm
    $bottom$-based-chain-is-$<=$-chain-b
    (implies (and (equal ($bottom$-based-chain
			  (+ i j)
			  x)
			 ($bottom$))
		  (integerp j)
		  (>= j 0))
	     (equal ($bottom$-based-chain i x)
		    ($bottom$)))
    :hints (("Goal"
	     :use
	     $bottom$-based-chain-is-$<=$-chain-a)))

(defthm
    $bottom$-based-chain-is-$<=$-chain-c
    (implies (and (integerp j)
		  (>= j 0)
		  (not (equal
			($bottom$-based-chain i x)
			($bottom$))))
	     (equal ($bottom$-based-chain (+ i j) x)
		    ($bottom$-based-chain i x)))
    :hints (("Goal"
	     :in-theory
	     (disable
	      $bottom$-based-chain-is-$<=$-chain-a)
	     :use
	     $bottom$-based-chain-is-$<=$-chain-a)))

(defthm
    $bottom$-based-chain-is-$<=$-chain-d
    (implies (and (not (equal
			($bottom$-based-chain i x)
			($bottom$)))
		  (integerp i)
	          (integerp j)
		  (>= j i))
	     (equal ($bottom$-based-chain i x)
		    ($bottom$-based-chain j x)))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory
	     (disable
	      $bottom$-based-chain-is-$<=$-chain-c)
	     :use
	     (:instance
	      $bottom$-based-chain-is-$<=$-chain-c
	      (j (- j i))))))

(defthm
    $bottom$-based-chain-is-$<=$-chain-e
    (implies (and (not (equal
			($bottom$-based-chain i x)
			($bottom$)))
		  (not (equal
			($bottom$-based-chain j x)
			($bottom$))))
	     (equal ($bottom$-based-chain i x)
		    ($bottom$-based-chain j x)))
    :rule-classes nil
    :hints (("Goal"
	     :use
	     ($bottom$-based-chain-is-$<=$-chain-d
	      (:instance
	       $bottom$-based-chain-is-$<=$-chain-d
	       (i j)
	       (j i))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Choose an ``index'' for definition of lub of
;;  $bottom$-based-chain:

(defchoose
    lub-$bottom$-based-chain-i i (x)
    (not (equal ($bottom$-based-chain i x)
		($bottom$))))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-$bottom$-based-chain-nat-i (x)
    (nfix (lub-$bottom$-based-chain-i x)))

(defthm
    lub-$bottom$-based-chain-nat-i-rewrite
    (implies (equal
	      ($bottom$-based-chain
	       (lub-$bottom$-based-chain-nat-i x)
	       x)
	      ($bottom$))
	     (equal
	      ($bottom$-based-chain i x)($bottom$)))
    :hints (("Goal"
	     :use lub-$bottom$-based-chain-i)))

(in-theory (disable
	    lub-$bottom$-based-chain-nat-i
	    (:executable-counterpart
	     lub-$bottom$-based-chain-nat-i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the least upper bound of
;;  $bottom$-based-chain:

(defun
    lub-$bottom$-based-chain (x)
    ($bottom$-based-chain
     (lub-$bottom$-based-chain-nat-i x)
     x))

(in-theory (disable (:executable-counterpart
		     lub-$bottom$-based-chain)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lub-$bottom$-based-chain is upper bound of
;;  $bottom$-based-chain:

(defthm
    lub-$bottom$-based-chain-is-upper-bound
    ($<=$ ($bottom$-based-chain i x)
	  (lub-$bottom$-based-chain x))
    :hints (("Goal"
	     :use
	     (:instance
	      $bottom$-based-chain-is-$<=$-chain-e
	      (j (lub-$bottom$-based-chain-nat-i x))
	      ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Show lub-$bottom$-based-chain is LEAST upper bound
;;  of $bottom$-based-chain:

;;  Axiomatize an upper bound of
;;   $bottom$-based-chain:

(encapsulate
 (((ub-$bottom$-based-chain *) => *))

 (local
  (defun
      ub-$bottom$-based-chain (x)
      (lub-$bottom$-based-chain x)))

 (defthm
     ub-$bottom$-based-chain-is-upper-bound
     ($<=$ ($bottom$-based-chain i x)
	   (ub-$bottom$-based-chain x)))
 ) ;; end encapsulate

(defthm
    lub-$bottom$-based-chain-is-LEAST-upper-bound
    ($<=$ (lub-$bottom$-based-chain x)
	  (ub-$bottom$-based-chain x))
    :hints (("Goal"
	     :in-theory
	     (disable
	      ub-$bottom$-based-chain-is-upper-bound)
	     :use
	     (:instance
	      ub-$bottom$-based-chain-is-upper-bound
	      (i (lub-$bottom$-based-chain-nat-i x))
	      ))))

(defthm
    $bottom$-based-chain-is-$<=$-chain-f
    (implies (and
	      (>= i
		  (lub-$bottom$-based-chain-nat-i x))
	      (integerp i))
	     (equal
	      (lub-$bottom$-based-chain x)
	      ($bottom$-based-chain i x)))
    :hints (("Goal"
	     :use
	     (:instance
	      $bottom$-based-chain-is-$<=$-chain-d
	      (i (lub-$bottom$-based-chain-nat-i x))
	      (j i)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize a $<=$-chain of functions (possibly
;;  without $bottom$ base):

(encapsulate
 (((chain$ * *) => *))

 (local
  (defun
      chain$ (i x)
      (declare (ignore i x))
      ($bottom$)))

 (defthm
     chain$-is-$<=$-chain
     (implies (and (integerp i)
		   (>= i 0))
	      ($<=$ (chain$ i x)
		    (chain$ (+ 1 i)  x))))
 ) ;; end encapsulate

;; Extend chain$ by adding an $bottom$ base:

(defun
    chain$+$bottom$-base (i x)
    (if (zp i)
	($bottom$)
        (chain$ (- i 1) x)))

;; Choose an ``index'' for definition of lub of
;;  chain$:

(defchoose
    lub-chain$-i i (x)
    (not (equal (chain$+$bottom$-base i x)
		($bottom$))))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-chain$-nat-i (x)
    (nfix (lub-chain$-i x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the least upper bound of chain$:

(defun
    lub-chain$ (x)
    (chain$+$bottom$-base (lub-chain$-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-chain$)))

;; lub-chain$ is upper bound of chain$+$bottom$-base:

(defthm
    lub-chain$-is-upper-bound-chain$+$bottom$-base
    ($<=$ (chain$+$bottom$-base i x)(lub-chain$ x))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      lub-$bottom$-based-chain-is-upper-bound
	      ($bottom$-based-chain
	       chain$+$bottom$-base)
	      (lub-$bottom$-based-chain lub-chain$)
	      (lub-$bottom$-based-chain-nat-i
	       lub-chain$-nat-i)
	      (lub-$bottom$-based-chain-i
	       lub-chain$-i)))
	    ("Subgoal 3"
	     :use lub-chain$-i)
	    ("Subgoal 2"
	     :use (:instance
		   chain$-is-$<=$-chain
		   (i (- i 1))))))

;; lub-chain$ is upper bound of chain$:

(defthm
    lub-chain$-is-upper-bound
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (chain$ i x)(lub-chain$ x)))
    :hints
    (("Goal"
      :in-theory
      (disable
       lub-chain$-is-upper-bound-chain$+$bottom$-base)
      :use
      (:instance
       lub-chain$-is-upper-bound-chain$+$bottom$-base
       (i (+ i 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Show lub-chain$ is LEAST upper bound of chain$:

;;  Axiomatize an upper bound of chain$:

(encapsulate
 (((ub-chain$ *) => *))

 (local
  (defun
      ub-chain$ (x)
      (lub-chain$ x)))

 (defthm
     ub-chain$-is-upper-bound
     (implies (and (integerp i)
		   (>= i 0))
	      ($<=$ (chain$ i x)(ub-chain$ x)))
     :hints (("Goal"
	      :in-theory
	      (disable $<=$ lub-chain$))))
 ) ;; end encapsulate

(defthm
    lub-chain$-is-LEAST-upper-bound
    ($<=$ (lub-chain$ x)(ub-chain$ x))
    :hints (("Goal"
	     :in-theory
	     (disable ub-chain$-is-upper-bound)
	     :use (:instance
		   ub-chain$-is-upper-bound
		   (i (- (lub-chain$-nat-i x) 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ($Bottom$-based-chain (+ i 1) x) is a chain with
;;  same lub as ($bottom$-based-chain i x):

(encapsulate
 (((shifted$-chain * *) => *))

 (local
  (defun
      shifted$-chain (i x)
      ($bottom$-based-chain (+ i 1) x)))

 (defthm
     shifted$-chain-rewrite
     (implies (and (integerp i)
		   (>= i 0))
	      (equal (shifted$-chain i x)
		     ($bottom$-based-chain (+ 1 i)
					 x))))
 ) ;; end encapsulate

(defthm
    shifted$-chain-is-$<=$-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (shifted$-chain i x)
		   (shifted$-chain (+ 1 i)  x)))
    :hints (("Goal"
	     :use
	     (:instance
	      $bottom$-based-chain-is-$<=$-chain
	      (i (+ i 1))))))

;; Extend shifted$-chain by adding an $bottom$ base:

(defun
    shifted$-chain+$bottom$-base (i x)
    (if (zp i)
	($bottom$)
        (shifted$-chain (- i 1) x)))

;; Choose an ``index'' for definition of lub of
;;  shifted$-chain:

(defchoose
    lub-shifted$-chain-i i (x)
    (not (equal (shifted$-chain+$bottom$-base i x)
		($bottom$))))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-shifted$-chain-nat-i (x)
    (nfix (lub-shifted$-chain-i x)))

;; Define the least upper bound of shifted-chain:

(defun
    lub-shifted$-chain (x)
    (shifted$-chain+$bottom$-base
     (lub-shifted$-chain-nat-i x)
     x))

(in-theory (disable (:executable-counterpart
		     lub-shifted$-chain)))

(defthm
    lub-shifted$-chain-is-upper-bound
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (shifted$-chain i x)
		   (lub-shifted$-chain x)))
    :hints (("Goal"
	     :by (:functional-instance
		  lub-chain$-is-upper-bound
		  (chain$ shifted$-chain)
		  (chain$+$bottom$-base
		   shifted$-chain+$bottom$-base)
		  (lub-chain$ lub-shifted$-chain)
		  (lub-chain$-nat-i
		   lub-shifted$-chain-nat-i)
		  (lub-chain$-i
		   lub-shifted$-chain-i)))
	    ("Subgoal 3"
	     :use lub-shifted$-chain-i)
	    ("Subgoal 1"
	     :use (:instance
		   $bottom$-based-chain-is-$<=$-chain
		   (i (+ i 1))))))

(defthm
  lub-shifted$-chain-is-upper-bound-of-$bottom$-based-chain-lemma
  (implies (and (integerp i)
		(> i 0))
	   ($<=$ ($bottom$-based-chain i x)
		 (lub-shifted$-chain x)))
    :hints (("Goal"
	     :use (:instance
		   lub-shifted$-chain-is-upper-bound
		   (i (- i 1))))))

(defthm
    $<=$-$bottom$
    ($<=$ ($bottom$) x))

(defthm
  lub-shifted$-chain-is-upper-bound-of-$bottom$-based-chain
    ($<=$ ($bottom$-based-chain i x)
	  (lub-shifted$-chain x))
    :hints (("Goal"
	     :in-theory
	     (disable $<=$ lub-shifted$-chain)
	     :cases ((zp i)))))

(defthm
    lub-$bottom$-based-chain-is-upper-bound-of-shifted$-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (shifted$-chain i x)
		   (lub-$bottom$-based-chain x)))
    :hints (("Goal"
	     :in-theory
	     (disable $<=$
		      lub-$bottom$-based-chain))))

(defthm
    lub-$bottom$-based-chain-$<=$-lub-shifted$-chain
    ($<=$ (lub-$bottom$-based-chain x)
	  (lub-shifted$-chain x))
    :hints (("Goal"
	     :by
	     (:functional-instance
	      lub-$bottom$-based-chain-is-LEAST-upper-bound
	      (ub-$bottom$-based-chain
	       lub-shifted$-chain)))))

(defthm
    lub-shifted$-chain-$<=$-lub-$bottom$-based-chain
    ($<=$ (lub-shifted$-chain x)
	  (lub-$bottom$-based-chain x))
    :hints (("Goal"
	     :in-theory
	     (disable $<=$
		      lub-$bottom$-based-chain)
	     :by (:functional-instance
		  lub-chain$-is-LEAST-upper-bound
		  (ub-chain$
		   lub-$bottom$-based-chain)
		  (chain$ shifted$-chain)
		  (chain$+$bottom$-base
		   shifted$-chain+$bottom$-base)
		  (lub-chain$ lub-shifted$-chain)
		  (lub-chain$-nat-i
		   lub-shifted$-chain-nat-i)
		  (lub-chain$-i
		   lub-shifted$-chain-i)))
	    ("Subgoal 2"
	     :use lub-shifted$-chain-i)))

(defthm
    lub-shifted$-chain-=-lub-$bottom$-based-chain
    (equal (lub-shifted$-chain x)
	   (lub-$bottom$-based-chain x))
    :hints (("Goal"
	     :in-theory
	     (disable lub-shifted$-chain
		      lub-$bottom$-based-chain)
	     :use (:instance
		   (:theorem
		    (implies (and ($<=$ x y)
				  ($<=$ y x))
			     (equal x y)))
		   (x (lub-$bottom$-based-chain x))
		   (y (lub-shifted$-chain x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize a function ($f$ x) and a $<=$-chain,
;;  ($chain$ i x), of functions with $bottom$ base
;;  such that the shifted version of the chain,
;;  (shifted-$chain$ i x), has an upper bound,
;;  (ub-shifted-$chain$ x), with the property that
;;  for all x, (equal (ub-shifted-$chain$ x)
;;                    (shifted-$chain$ ($f$ x) x)):

(encapsulate
 ((($chain$ * *) => *)
  (($f$ *) => *)
  ((shifted-$chain$ * *) => *)
  ((ub-shifted-$chain$ *) => *))

 (local
  (defun
      $chain$ (i x)
      (declare (ignore i x))
      ($bottom$)))

 (defthm
     base-of-$chain$=$bottom$
     (implies (zp i)
	      (equal ($chain$ i x)
		     ($bottom$))))

 (defthm
     $chain$-is-$<=$-chain
     (implies (and (integerp i)
		   (>= i 0))
	      ($<=$ ($chain$ i x)
		    ($chain$ (+ 1 i) x))))

 (local
  (defun
      shifted-$chain$ (i x)
      ($chain$ (+ 1 i) x)))

 (defthm
     shifted-$chain$=$chain$
     (implies (and (integerp i)
		   (>= i 0))
	      (equal (shifted-$chain$ i x)
		     ($chain$ (+ 1 i) x))))

 (local
  (defun
      ub-shifted-$chain$ (x)
      (declare (ignore x))
      ($bottom$)))

  (defthm
      shifted-$chain$-$<=$-ub-shifted-$chain$
      (implies (and (integerp i)
		    (>= i 0))
	       ($<=$ (shifted-$chain$ i x)
		     (ub-shifted-$chain$ x))))

  (local
   (defun
       $f$ (x)
       (declare (ignore x))
       0))

  (defthm
      nat-$f$
      (and (integerp ($f$ x))
	   (>= ($f$ x) 0))
      :rule-classes :type-prescription)

  (defthm
      ub-shifted-$chain$-=-shifted-$chain$-$f$
      (equal (ub-shifted-$chain$ x)
	     (shifted-$chain$ ($f$ x) x)))
 ) ;; end encapsulate

(defthm
    shifted-$chain$-is-$<=$-chain
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (shifted-$chain$ i x)
		   (shifted-$chain$ (+ 1 i) x)))
    :hints (("Goal"
	     :use (:instance
		   $chain$-is-$<=$-chain
		   (i (+ 1 i))))))

;; Choose an ``index'' for definition of lub of
;;  $chain$:

(defchoose
    lub-$chain$-i i (x)
    (not (equal ($chain$ i x)
		($bottom$))))

(defthm
    lub-$chain$-i-rewrite
    (implies (equal ($chain$ (lub-$chain$-i x) x)
		    ($bottom$))
	     (equal ($chain$ i x) ($bottom$)))
    :hints (("Goal"
	     :use lub-$chain$-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-$chain$-nat-i (x)
    (nfix (lub-$chain$-i x)))

;; Define the least upper bound of $chain$:

(defun
    lub-$chain$ (x)
    ($chain$ (lub-$chain$-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-$chain$)))

;; Extend shifted-$chain$ by adding an $bottom$ base:

(defun
    shifted-$chain$+$bottom$-base (i x)
    (if (zp i)
	($bottom$)
        (shifted-$chain$ (- i 1) x)))

(defthm
    shifted-$chain$+$bottom$-base-rewrite
    (and (implies (zp i)
		  (equal
		   (shifted-$chain$+$bottom$-base i
						  x)
		   ($bottom$)))
	 (implies (not (zp i))
		  (equal
		   (shifted-$chain$+$bottom$-base i
						  x)
		   (shifted-$chain$ (- i 1) x)))))

;; Choose an ``index'' for definition of lub of
;;  shifted-$chain$:

(defchoose
    lub-shifted-$chain$-i i (x)
    (not (equal (shifted-$chain$+$bottom$-base i x)
		($bottom$))))

(defthm
    lub-shifted-$chain$-i-rewrite
    (implies (equal (shifted-$chain$+$bottom$-base
		     (lub-shifted-$chain$-i x) x)
		    ($bottom$))
	     (equal (shifted-$chain$+$bottom$-base i
						   x)
		    ($bottom$)))
    :hints (("Goal"
	     :use lub-shifted-$chain$-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-shifted-$chain$-nat-i (x)
    (nfix (lub-shifted-$chain$-i x)))

;; Define the least upper bound of shifted-$chain$:

(defun
    lub-shifted-$chain$ (x)
    (shifted-$chain$+$bottom$-base
     (lub-shifted-$chain$-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-shifted-$chain$)))

(defthm
    lub-shifted-$chain$-=-lub-$chain$
    (equal (lub-shifted-$chain$ x)(lub-$chain$ x))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory
	     (disable $<=$
		      shifted-$chain$+$bottom$-base)
	     :by
	     (:functional-instance
	      lub-shifted$-chain-=-lub-$bottom$-based-chain
	      (lub-shifted$-chain
	       lub-shifted-$chain$)
	      (lub-$bottom$-based-chain lub-$chain$)
	      ($bottom$-based-chain $chain$)
	      (lub-$bottom$-based-chain-i
	       lub-$chain$-i)
	      (lub-$bottom$-based-chain-nat-i
	       lub-$chain$-nat-i)
	      (shifted$-chain shifted-$chain$)
	      (shifted$-chain+$bottom$-base
	       shifted-$chain$+$bottom$-base)
	      (lub-shifted$-chain-i
	       lub-shifted-$chain$-i)
	      (lub-shifted$-chain-nat-i
	       lub-shifted-$chain$-nat-i)))))

(defthm
    lub-shifted-$chain$-$<=$-ub-shifted-$chain$
    ($<=$ (lub-shifted-$chain$ x)
	  (ub-shifted-$chain$ x))
    :hints (("Goal"
	     :in-theory
	     (disable
	      $<=$ shifted-$chain$=$chain$
	      shifted-$chain$+$bottom$-base
	      ub-shifted-$chain$-=-shifted-$chain$-$f$)
	     :by (:functional-instance
		  lub-chain$-is-LEAST-upper-bound
		  (ub-chain$ ub-shifted-$chain$)
		  (chain$ shifted-$chain$)
		  (chain$+$bottom$-base
		   shifted-$chain$+$bottom$-base)
		  (lub-chain$ lub-shifted-$chain$)
		  (lub-chain$-nat-i
		   lub-shifted-$chain$-nat-i)
		  (lub-chain$-i
		   lub-shifted-$chain$-i)))))

(defthm
    lub-shifted-$chain$-is-upper-bound
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (shifted-$chain$ i x)
		   (lub-shifted-$chain$ x)))
    :hints (("Goal"
	     :in-theory
	     (disable shifted-$chain$+$bottom$-base)
	     :by (:functional-instance
		  lub-shifted$-chain-is-upper-bound
		  (shifted$-chain shifted-$chain$)
		  (shifted$-chain+$bottom$-base
		   shifted-$chain$+$bottom$-base)
		  (lub-shifted$-chain
		   lub-shifted-$chain$)
		  (lub-shifted$-chain-i
		   lub-shifted-$chain$-i)
		  (lub-shifted$-chain-nat-i
		   lub-shifted-$chain$-nat-i)
		  ($bottom$-based-chain $chain$)))))

(defthm
    ub-shifted-$chain$-$<=$-lub-shifted-$chain$
    ($<=$ (ub-shifted-$chain$ x)
	  (lub-shifted-$chain$ x))
    :hints (("Goal"
	     :in-theory
	     (disable $<=$ shifted-$chain$=$chain$
		      lub-shifted-$chain$))))

(defthm
    ub-shifted-$chain$=lub-shifted-$chain$
    (equal (ub-shifted-$chain$ x)
	   (lub-shifted-$chain$ x))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable lub-shifted-$chain$)
	     :use (:instance
		   (:theorem
		    (implies (and ($<=$ x y)
				  ($<=$ y x))
			     (equal x y)))
		   (x (ub-shifted-$chain$ x))
		   (y (lub-shifted-$chain$ x))))))

(defthm
    lub-$chain$=ub-shifted-$chain$
    (equal (lub-$chain$ x)(ub-shifted-$chain$ x))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable lub-$chain$
				 lub-shifted-$chain$)
	     :use
	     (ub-shifted-$chain$=lub-shifted-$chain$
	      lub-shifted-$chain$-=-lub-$chain$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; An unary function f is said to be monotonic (with
;;  respect to $<=$) just in case for all x and y,
;;  ($<=$ x y) implies ($<=$ (f x)(f y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Axiomatize a $<=$-chain of monotonic functions:

(encapsulate
 (((mono-chain$ * *) => *))

 (local
  (defun
      mono-chain$ (i x)
      (declare (ignore i x))
      ($bottom$)))

 (defthm
     mono-chain$-is-$<=$-chain
     (implies (and (integerp i)
		   (>= i 0))
	      ($<=$ (mono-chain$ i x)
		    (mono-chain$ (+ 1 i)  x))))

 (defthm
     mono-chain$-is-chain-of-monotonic-functions
     (implies ($<=$ x y)
	      ($<=$ (mono-chain$ i x)
		    (mono-chain$ i y))))
 ) ;; end encapsulate

;; Monotonic unary functions either preserve
;;  ($bottom$) or are constant.  Functions that
;;  preserve ($bottom$) are called strict.

(defthm
  mono-chain$-is-chain-of-monotonic-functions-a
  (or (equal (mono-chain$ i ($bottom$))($bottom$))
      (equal (mono-chain$ i x)
	     (mono-chain$ i ($bottom$))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (disable
     mono-chain$-is-chain-of-monotonic-functions)
    :use
    (:instance
     mono-chain$-is-chain-of-monotonic-functions
     (x ($bottom$))
     (y x)))))

;; Extend mono-chain$ by adding an $bottom$ base:

(defun
    mono-chain$+$bottom$-base (i x)
    (if (zp i)
	($bottom$)
        (mono-chain$ (- i 1) x)))

;; Choose an ``index'' for definition of lub of
;;  mono-chain$:

(defchoose
    lub-mono-chain$-i i (x)
    (not (equal (mono-chain$+$bottom$-base i x)
		($bottom$))))

(defthm
  lub-mono-chain$-i-rewrite
  (implies (equal (mono-chain$+$bottom$-base
		   (lub-mono-chain$-i x)
		   x)
		  ($bottom$))
	   (equal (mono-chain$+$bottom$-base i x)
		  ($bottom$)))
    :hints (("Goal"
	     :use lub-mono-chain$-i)))

;; Make sure the chosen index is a nonneg. integer:

(defun
    lub-mono-chain$-nat-i (x)
    (nfix (lub-mono-chain$-i x)))

;; Define the least upper bound of mono-chain$:

(defun
    lub-mono-chain$ (x)
    (mono-chain$+$bottom$-base
     (lub-mono-chain$-nat-i x) x))

(in-theory (disable (:executable-counterpart
		     lub-mono-chain$)))

;; lub-mono-chain$ is upper bound of mono-chain$:

(defthm
    lub-mono-chain$-is-upper-bound
    (implies (and (integerp i)
		  (>= i 0))
	     ($<=$ (mono-chain$ i x)
		   (lub-mono-chain$ x)))
    :hints
    (("Goal"
      :in-theory (disable $<=$)
      :by (:functional-instance
	   lub-chain$-is-upper-bound
	   (chain$ mono-chain$)
	   (lub-chain$ lub-mono-chain$)
	   (chain$+$bottom$-base
	    mono-chain$+$bottom$-base)
	   (lub-chain$-i lub-mono-chain$-i)
	   (lub-chain$-nat-i lub-mono-chain$-nat-i)))
     ("Subgoal 3"
      :in-theory (disable mono-chain$+$bottom$-base)
      )))

;; Show lub-mono-chain$ is LEAST upper bound of
;;   mono-chain$:

;;  Axiomatize an upper bound of mono-chain$:

(encapsulate
 (((ub-mono-chain$ *) => *))

 (local
  (defun
      ub-mono-chain$ (x)
      (lub-mono-chain$ x)))

 (defthm
     ub-mono-chain$-is-upper-bound
     (implies (and (integerp i)
		   (>= i 0))
	      ($<=$ (mono-chain$ i x)
		    (ub-mono-chain$ x)))
     :hints (("Goal"
	      :in-theory
	      (disable $<=$ lub-mono-chain$))))
 ) ;; end encapsulate

(defthm
    lub-mono-chain$-is-LEAST-upper-bound
    ($<=$ (lub-mono-chain$ x)(ub-mono-chain$ x))
    :hints
    (("Goal"
      :in-theory (disable $<=$)
      :by (:functional-instance
	   lub-chain$-is-LEAST-upper-bound
	   (chain$ mono-chain$)
	   (lub-chain$ lub-mono-chain$)
	   (ub-chain$ ub-mono-chain$)
	   (chain$+$bottom$-base
	    mono-chain$+$bottom$-base)
	   (lub-chain$-i lub-mono-chain$-i)
	   (lub-chain$-nat-i lub-mono-chain$-nat-i)))
     ("Subgoal 2"
      :in-theory (disable mono-chain$+$bottom$-base)
      )))

(defthm
  mono-chain$+$bottom$-base-is-$<=$-chain
  (implies (and (integerp i)
		(>= i 0))
	   ($<=$ (mono-chain$+$bottom$-base i x)
		 (mono-chain$+$bottom$-base (+ 1 i)
					    x)))
  :hints (("Goal"
	   :in-theory (disable $<=$)
	   :use (:instance
		 mono-chain$-is-$<=$-chain
		 (i (+ -1 i))))))

(defthm
  mono-chain$+$bottom$-base=$bottom$
  (implies (zp i)
	   (equal (mono-chain$+$bottom$-base i x)
		  ($bottom$))))

(defthm
    mono-chain$+$bottom$-base-is-$<=$-chain-e
    (implies (and (not (equal
			(mono-chain$+$bottom$-base i
						   x)
			($bottom$)))
		  (not (equal
			(mono-chain$+$bottom$-base j
						   x)
			($bottom$))))
	     (equal (mono-chain$+$bottom$-base i x)
		    (mono-chain$+$bottom$-base j x)))
    :rule-classes nil
    :hints (("Goal"
	     :in-theory (disable
			 $<=$
			 mono-chain$+$bottom$-base)
	     :by
	     (:functional-instance
	      $bottom$-based-chain-is-$<=$-chain-e
	      ($bottom$-based-chain
	       mono-chain$+$bottom$-base)))))

(defthm
  mono-chain$+$bottom$-base-is-chain-of-monotonic-fns
  (or (equal (mono-chain$+$bottom$-base i ($bottom$))
	     ($bottom$))
      (equal (mono-chain$+$bottom$-base i x)
	     (mono-chain$+$bottom$-base i
					($bottom$))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (:instance
     mono-chain$-is-chain-of-monotonic-functions-a
     (i (+ -1 i))))))

;; lub-mono-chain$ is a monotonic function:

(defthm
    lub-mono-chain$-is-monotonic
    (implies ($<=$ x y)
	     ($<=$ (lub-mono-chain$ x)
		   (lub-mono-chain$ y)))
    :hints
    (("Goal"
      :in-theory
      (disable mono-chain$+$bottom$-base)
      :use
      ((:instance
	mono-chain$+$bottom$-base-is-chain-of-monotonic-fns
	(i (lub-mono-chain$-nat-i ($bottom$)))
	(x y))
       (:instance
	mono-chain$+$bottom$-base-is-$<=$-chain-e
	(i (lub-mono-chain$-nat-i ($bottom$)))
	(j (lub-mono-chain$-nat-i y))
	(x y))))))
