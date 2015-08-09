; ACL2 book for Knuth's Generalized 91 Recursion.
; Copyright (C) 1999  John R. Cowles, University of Wyoming

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

;; This book is a descendent of the NQTHM events reported in:
;;  J.R. Cowles, Meeting a Challenge of Knuth,
;;  Internal Note 286, Computational Logic, Inc., 1993.
;;  ftp://ftp.cs.utexas.edu/pub/boyer/cli-notes/note-286.txt.
;; The NQTHM events were completed during 1990-91 at Computational
;; Logic, Inc. of Austin, Texas, while the author was on sabbatical leave
;; from the University of Wyoming.

;; This book mechanically verifies results, over an arbitrary Archimedean
;; ordered field, that generalize results that were first mechanically
;; verified, using  NQTHM, over the ring of integers. Additional results,
;; about termination of the recursion, with no analogue in the NQTHM
;; events are also included.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; In the paper; Textbook Examples of Recursion, Artificial Intelligence and
;; Mathematical Theory of Computation: Papers in Honor of John McCarthy,
;; edited by Vladimir Lifschitz, Academic Press, 1991; Donald E. Knuth of
;; Stanford University gives the following generalization of McCarthy's 91
;; function:

;; Let a be a real, let b and d be positive reals, and let c be a
;; positive integer.

;; Define K( x ) by

;;   K( x ) <== if  x > a  then  x - b
;;                         else  K( ... K( x+d ) ... ).

;; Here the else-clause in this definition has c applications of the
;; function K.

;; When a = 100, b = 10, c = 2, and d = 11, the definition specializes
;; to McCarthy's original 91 function:

;;   K( x ) <== if  x > 100  then  x - 10
;;                           else  K( K( x+11 ) ).

;; Knuth calls the first definition of K given above, the generalized
;; 91 recursion scheme with parameters ( a,b,c,d ).

;; Knuth proves the following theorem and asks for a proof by computer:

;; Theorem 1. The generalized 91 recursion with parameters ( a,b,c,d )
;;            defines a total function on the integers if and only if
;;            (c-1)b < d.  In such a case the values of K( x ) also
;;            satisfy the much simpler recurrence

;;            K( x )  =  if  x > a  then  x - b
;;                                  else  K( x+d-(c-1)b ).

;; Knuth proves the following.

;; 1. If (c-1)b >= d, then the recursion in the generalized 91 recursion
;;    does not always terminate.

;; 2. If (c-1)b < d, then the recursion always terminates.

;; 3. Any total function that satisfies the generalized 91 recursion must
;;    also satisfy the simpler recursion.

;; Here is a corollary to the results verified in this book.

;; 0. For all choices of the parameters a,b,c,d; with a real, b and d positive
;;    reals, and c a positive integer; there are total functions over the reals
;;    that satisfy the generalized 91 recursion.

;; 1. If (c-1)b >= d, then there are MANY total functions over reals that
;;    satisfy the the generalized 91 recursion. It follows from this that
;;    the recursion cannot always terminate.

;; 2, If (c-1)b < d, then the recursion always terminates. It follows
;;    that there is only one total function over the reals that
;;    satisfies the generalized 91 recursion. The uniqueness of this
;;    function is separately verified.

;; 3. Any total function that satisfies the generalized 91 recursion must
;;    also satisfy the simpler recursion.

;; The results verified in this book generalize the corollary just stated by
;; replacing the ordered field of all reals with an arbitrary ordered
;; Archimedean field. An Archimedean ordered field is an ordered field in
;; which every field element is bounded above by some positive integer.
;; (See the ACL2 Archimedean Ordered Fields book for more details.) The
;; The Reals are an Archimedean ordered field, so results valid for all
;; Archimedean fields are also valid for the Reals.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Use an ACL2 Arithmetic Book.

(include-book "../../../arithmetic/top-with-meta")
(include-book "../../../ordinals/e0-ordinal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Use the Achimedean Fields Book.

(include-book "aof")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Develop a small, but useful, theory of iterated applications
;   of a function with a single input argument.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Introduce a new function F of one argument with no constraints.

(defstub
  F (x) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Recursively define what it means to iterate applications of F.

(defun
  Iter-F (i x)
  (declare (xargs :guard (and (integerp i)
			      (>= i 0))))
  (if (zp i)
      x
      (F (Iter-F (- i 1) x))))


(defthm
  Iter-F=F
  (equal (Iter-F 1 x)
	 (F x))
  :hints (("Goal"
	   :expand (Iter-F 1 x))))

(defthm
  Compose-Iter-F
  (equal (Iter-F i (Iter-F j x))
	 (iter-F (+ (nfix i)
		    (nfix j))
		 x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an "abstract Knuth" function, G, of one argument that will be used
; later to help witness the existence of functions that satisfy the defining
; recursion of the generalized 91 function. The abstraction is obtained by
; temporarily considering the complex expression, d-(c-1)b, as a single value.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Introduce new constants (ie., functions with no arguments)
; a1, b1, e1, and e2 with the indicated constraints

(encapsulate
 ((a1 () aofp)
  (b1 () aofp)
  (e1 () aofp)
  (e2 () aofp))

 (local
  (defun
    a1 () 1))
 (local
  (defun
    b1 () 1))
 (local
  (defun
    e1 () 1))
 (local
  (defun
    e2 () 1))

 (defthm
   a1-type
   (aofp (a1)))

 (defthm
   b1-type
   (and (aofp (b1))
	(>=_a (b1) 0)))

 (defthm
   e1-type
   (aofp (e1)))

 (defthm
   e2-type
   (aofp (e2)))

 (defthm
   a1->=_a-e2
   (>=_a (a1)(e2)))
 ) ; end encapsulate


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define the "abstract Knuth" function, G.

(defthm
  G-lemma-1
  (IMPLIES (AND (aofp x)
		(aofp y)
		(>=_a x 0)
		(>_a y 0))
	   (< (LEAST-NAT-BOUND-LOOP
	       0
	       (-_a (/_a x y)
		    (/_a y y)))
	      (LEAST-NAT-BOUND-LOOP
	       0
	       (/_a x y))))
  :hints (("Goal"
	   :use ((:instance
		  Least-nat-bound-is-increasing-1
		  (x1 (-_a (/_a x y)(/_a y y)))
		  (x2 (/_a x y))))
           :in-theory (disable LEAST-NAT-BOUND-LOOP
                               LEAST-NAT-BOUND-IS-INCREASING-1))))

(defthm
  G-lemma-2
  (IMPLIES
   (AND (AOFP X)
	(aofp y)
	(aofp z)
	(>=_a y X)
	(>_a z 0)
	(>=_a y x))
   (<
    (LEAST-NAT-BOUND-LOOP
     0
     (+_A (/_A y z)
	  (+_A (-_A (/_A z z))
	       (-_A (*_A (/_A z) X)))))
    (LEAST-NAT-BOUND-LOOP
     0
     (+_A (/_A y z)
	  (-_A (*_A (/_A z) X))))))
  :hints (("Goal"
	   :use (:instance
		 Least-nat-bound-is-increasing-1
		 (x1 (+_A (/_A y z)
			  (+_A (-_A (/_A z z))
			       (-_A (*_A (/_A z) X)))))
		 (x2 (+_A (/_A y z)
			  (-_A (*_A (/_A z) X)))))
           :in-theory (disable LEAST-NAT-BOUND-LOOP
                               LEAST-NAT-BOUND-IS-INCREASING-1))))

(defun
  G (x)
  (declare (xargs :guard (aofp x)
		  :measure
		  (let ((x (afix x)))
		       (cond ((>_a x (a1))
			      0)
			     ((>_a (e1) 0)
			      (Least-nat-bound
			       (/_a (-_a (a1) x)
				    (e1))))
			     (t 0)))))
  (let ((x (afix x)))
       (cond ((>_a x (a1))
	      (-_a x (b1)))
	     ((>_a (e1) 0)
	      (G (+_a x (e1))))
	     (t
	      (e2)))))

(defun
  Iter-G (i x)
  (declare (xargs :guard
		  (and (aofp x)
		       (integerp i)
		       (>= i 0))
		  :verify-guards nil))
  (if (zp i)
      x
      (G (Iter-G (- i 1) x))))

(defthm
  Type-of-Iter-G
  (implies (aofp x)
	   (aofp (Iter-G i x))))

(verify-guards Iter-G)

(defthm
  Iter-G=G
  (equal (Iter-G 1 x)
	 (G x))
  :hints (("Goal"
	   :use
	   (:functional-instance
	    Iter-F=F
	    (Iter-F Iter-G)
	    (F G)))))

(defun
  Induct-on-pos-int (n)
  (if (and (integerp n)
	   (> n 1))
      (Induct-on-pos-int (- n 1))
      t))

(defthm
  Iter-G-e1+x=Iter-G-x
  (implies (and (integerp i)
		(< 0 i)
		(aofp x)
		(<_a 0 (e1))
		(>=_a (a1) x))
	   (equal (Iter-G i (+_a (e1) x))
		  (Iter-G i x))))

(in-theory (disable Extension-Laws))

(in-theory (enable Reverse-Extension-Laws))

(defthm
  Iter-G-x+n*e1=Iter-G-x+n-1*e1
  (implies (and (integerp n)
		(< 1 n)
		(integerp i)
		(< 0 i)
		(aofp x)
		(<_a 0 (e1))
		(>=_a (a1)
		      (+_a x (*_a (e1) (+ -1 n)))))
	   (equal (Iter-G i (+_a x (*_a (e1) n)))
		  (Iter-G i
			  (+_a x (*_a (e1) (+ -1 n))))))
  :hints (("Goal"
	   :in-theory (disable Iter-G-e1+x=Iter-G-x)
	   :use (:instance
		 Iter-G-e1+x=Iter-G-x
		 (x (+_a x (*_a (e1) (+ -1 n))))))))

(in-theory (disable Reverse-Extension-Laws))

(in-theory (enable Extension-Laws))

(defthm
  Iter-G-n*e1+x=Iter-G-x
  (implies (and (integerp i)
		(> i 0)
		(integerp n)
		(> n 0)
		(aofp x)
		(>_a (e1) 0)
		(<=_a (+_a x (*_a (e1)(- n 1)))
		      (a1)))
	   (equal (Iter-G i (+_a x (*_a (e1) n)))
		  (Iter-G i x)))
  :hints (("Goal"
	   :induct (Induct-on-pos-int n))))

(defthm
  E1-pos-not-zero
  (implies (>_a (e1) 0)
	   (not (equal (e1) 0)))
  :rule-classes :forward-chaining)

(defthm
  Inequality-1
  (implies (and (aofp x)
		(<=_a x (a1))
		(>_a (e1) 0))
	   (<=_a (+_a x (*_a (e1)(- (least-nat-bound-loop
				     0 (/_a (-_a (a1) x)
					    (e1)))
				    1)))
		 (a1)))
 :rule-classes nil
 :hints (("Goal"
	  :in-theory (disable
		      Least-nat-bound-loop-is-LEAST-bound)
	  :use (:instance
		Least-nat-bound-loop-is-LEAST-bound
		(i 0)(x (/_a (-_a (a1) x)
			     (e1)))))))

(defthm
  Inequality-2
  (<=_a (a1)(+_a (a1)(b1)))
  :hints (("Goal"
	   :in-theory (disable +_a-Compatibility-of-<=_a
			       <_a-cancellation-laws-for-+_a)
	   :use (:instance
		 +_a-Compatibility-of-<=_a
		 (x1 (a1))(x2 (a1))
		 (y1 0)(y2 (b1))))))

(defthm
  Iter-G_i-1_x-b1+e1*n=Iter-G_i-1_x-b1
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(<=_a x (a1))
		(>_a (e1) 0))
	   (equal (Iter-G (- i 1)
			  (+_a x
			       (-_a (b1))
			       (*_a (e1)(Least-nat-bound
					 (/_a (-_a (a1) x)
					      (e1))))))
		  (Iter-G (- i 1)(-_a x (b1)))))
  :hints (("Goal"
	   :use (Inequality-1
		 (:instance
		  Iter-G-n*e1+x=Iter-G-x
		  (i (- i 1))
		  (x (-_a x (b1)))
		  (n (Least-nat-bound (/_a (-_a (a1) x)
					   (e1)))))))))

(defthm
  Iter-G_i-1_x-b1=Iter-G_i_x-when-a1>=x&e1>0
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(<=_a x (a1))
		(>_a (e1) 0))
	   (equal (Iter-G (- i 1)(-_a x (b1)))
		  (Iter-G i x)))
  :hints (("Goal"
	   :use Iter-G_i-1_x-b1+e1*n=Iter-G_i-1_x-b1)))

(defthm
  Iter-G_i-1_x-b1=Iter-G_i_x-when-a1>=x
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(<=_a x (a1)))
	   (equal (Iter-G (- i 1)(-_a x (b1)))
		  (Iter-G i x)))
  :hints (("Goal"
	   :use Iter-G_i-1_x-b1=Iter-G_i_x-when-a1>=x&e1>0
	   )))

(defthm
  Iter-G_i-1_x-b1=Iter-G_i_x
  (implies (and (integerp i)
		(> i 1)
		(aofp x))
	   (equal (Iter-G (- i 1)(-_a x (b1)))
		  (Iter-G i x)))
  :hints (("Goal"
	   :use Iter-G_i-1_x-b1=Iter-G_i_x-when-a1>=x)))

(in-theory (disable Extension-Laws))

(in-theory (enable Reverse-Extension-Laws))

(defthm
  Equality-1
  (implies (and (aofp x)
		(rationalp j))
	   (equal
	    (+_A X
		 (-_A (*_A (B1) (+ -1 J))))
	    (+_A (B1)
		 (+_A X (-_A (*_A (B1) J)))))))

(in-theory (disable Reverse-Extension-Laws))

(in-theory (enable Extension-Laws))

(defthm
  Iter-G_i-j_x-jb1=Iter-G_i_x
  (implies (and (integerp i)
		(integerp j)
		(> j 0)
		(> i j)
		(aofp x))
	   (equal (Iter-G (- i j)(-_a x (*_a j (b1))))
		  (Iter-G i x)))
  :hints (("Goal"
	   :induct (induct-on-pos-int j))
	  ("Subgoal *1/2"
	   :use Iter-G_i-1_x-b1=Iter-G_i_x)
	  ("Subgoal *1/1"
	   :use (:instance
		 Iter-G_i-1_x-b1=Iter-G_i_x
		 (i (+ 1 i (- j)))
		 (x (+_a (b1) x (-_a (*_a (b1) j))))))))

(defthm
  G_x-_i-1_b1=Iter-G_i_x-when-i>1
  (implies (and (integerp i)
		(> i 1)
		(aofp x))
	   (equal (G (-_a x (*_a (- i 1)(b1))))
		  (Iter-G i x)))
  :hints (("Goal"
	   :use (:instance
		 Iter-G_i-j_x-jb1=Iter-G_i_x
		 (j (- i 1))))))

(defthm
  G_x-_i-1_b1=Iter-G_i_x
  (implies (and (integerp i)
		(> i 0)
		(aofp x))
	   (equal (G (-_a x (*_a (- i 1)(b1))))
		  (Iter-G i x)))
  :hints (("Goal"
	   :use G_x-_i-1_b1=Iter-G_i_x-when-i>1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; For all choices of the parameters a,b,c,d from an Archimedean field, with
; b and d positive, and c a positive integer there are total fumctions, called
; here K1 and K2, over the Archimedean field that satisfy the generalized 91
; recursion.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Introduce new constants (ie., functions with no arguments)
;  A, B, C, and D with the indicated constaints.

(encapsulate
 ((a () a)
  (b () a)
  (c () i)
  (d () a))

 (local
  (defun
    a () 1))
 (local
  (defun
    b () 1))
 (local
  (defun
    c () 1))
 (local
  (defun
    d () 1))

 (defthm
   a-type
   (aofp (a)))

 (defthm
   b-type
   (and (aofp (b))
	(>_a (b) 0)))

 (defthm
   c-type
   (and (integerp (c))
	(> (c) 0))
   :rule-classes
   :type-prescription)

 (defthm
   d-type
   (and (aofp (d))
	(>_a (d) 0)))
 ) ; end encapsulate

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define two functions K1 and K2 that will be shown to  satisfy the
; generalized 91 recursion scheme with parameters ( (A),(B),(C),(D) ).

(defun
  e ()
  (declare (xargs :guard t))
  (-_a (d)(*_a (-_a (c) 1)(b))))

(in-theory (disable (e)))

(defthm
  type-of-e
  (aofp (e)))

(in-theory (disable e))

(defun
  K1 (x)
  (declare (xargs :guard (aofp x)
		  :measure
		  (let ((x (afix x)))
		       (cond ((>_a x (a))
			      0)
			     ((>_a (e) 0)
			      (Least-nat-bound
			       (/_a (-_a (a) x)
				    (e))))
			     (t 0)))))
  (let ((x  (afix x)))
       (cond ((>_a x (a))
	      (-_a x (b)))
	     ((>_a (e) 0)
	      (K1 (+_a (e) x)))
	     (t (a)))))

(defun
  K2 (x)
  (declare (xargs :guard (aofp x)
		  :measure
		  (let ((x (afix x)))
		       (cond ((>_a x (a))
			      0)
			     ((>_a (e) 0)
			      (Least-nat-bound
			       (/_a (-_a (a) x)
				    (e))))
			     (t 0)))))
  (let ((x  (afix x)))
       (cond ((>_a x (a))
	      (-_a x (b)))
	     ((>_a (e) 0)
	      (K2 (+_a (e) x)))
	     (t (-_a (a)(b))))))

(defun
  Iter-K1 (i x)
  (declare (xargs :guard
		  (and (aofp x)
		       (integerp i)
		       (>= i 0))
		  :verify-guards nil))
  (if (zp i)
      x
      (K1 (Iter-K1 (- i 1) x))))

(defthm
  Type-of-Iter-K1
  (implies (aofp x)
	   (aofp (Iter-K1 i x))))

(verify-guards Iter-K1)

(defun
  Iter-K2 (i x)
  (declare (xargs :guard
		  (and (aofp x)
		       (integerp i)
		       (>= i 0))
		  :verify-guards nil))
  (if (zp i)
      x
      (K2 (Iter-K2 (- i 1) x))))

(defthm
  Type-of-Iter-K2
  (implies (aofp x)
	   (aofp (Iter-K2 i x))))

(verify-guards Iter-K2)

(defthm
  K1_x-_i-1_b=Iter-K1_i_x
  (implies (and (integerp i)
		(> i 0)
		(aofp x))
	   (equal (K1 (-_a x (*_a (- i 1)(b))))
		  (Iter-K1 i x)))
  :hints (("Goal"
	   :use (:functional-instance
		 G_x-_i-1_b1=Iter-G_i_x
		 (G K1)
		 (iter-G iter-K1)
		 (a1 a)(b1 b)(e1 e)(e2 a)))))

(defthm
  Inequality-2a
  (<=_a (a)(+_a (a)(b)))
  :hints (("Goal"
	   :in-theory (disable +_a-Compatibility-of-<=_a
			       <_a-cancellation-laws-for-+_a)
	   :use (:instance
		 +_a-Compatibility-of-<=_a
		 (x1 (a))(x2 (a))
		 (y1 0)(y2 (b))))))

(defthm
  K2_x-_i-1_b=Iter-K2_i_x
  (implies (and (integerp i)
		(> i 0)
		(aofp x))
	   (equal (K2 (-_a x (*_a (- i 1)(b))))
		  (Iter-K2 i x)))
  :hints (("Goal"
	   :use (:functional-instance
		 G_x-_i-1_b1=Iter-G_i_x
		 (G K2)
		 (iter-G iter-K2)
		 (a1 a)(b1 b)(e1 e)(e2 (lambda ()
					 (-_a (a)(b))))))))

(defthm
  K1_x+e=Iter-K1_x+d
  (implies (aofp x)
	   (equal (K1 (+_a x (e)))
		  (Iter-K1 (c)(+_a x (d)))))
  :hints (("Goal"
	   :use  (:instance
		  K1_x-_i-1_b=Iter-K1_i_x
		  (i (c))
		  (x (+_a x (d))))
	   :in-theory (enable e))))

(defthm
  K2_x+e=Iter-K2_x+d
  (implies (aofp x)
	   (equal (K2 (+_a x (e)))
		  (Iter-K2 (c)(+_a x (d)))))
  :hints (("Goal"
	   :use  (:instance
		  K2_x-_i-1_b=Iter-K2_i_x
		  (i (c))
		  (x (+_a x (d))))
	   :in-theory (enable e))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The two functions K1 and K2 satisfy the generalized 91 recursion scheme
; with parameters ( (A),(B),(C),(D) ):

(defthm
  Inequality-3
  (implies (and (aofp x)
		(<=_a x (a))
		(<=_a (e) 0))
	   (<=_a (+_a (e) x) (a)))
  :hints (("Goal"
	   :in-theory (disable +_a-Compatibility-of-<=_a
			       <_a-cancellation-laws-for-+_a)
	   :use (:instance
		 +_a-Compatibility-of-<=_a
		 (x1 x)(x2 (a))
		 (y1 (e))(y2 0)))))

(defthm
  K1-satisfies-Gen-91-Recursion
  (implies (aofp x)
	   (equal (K1 x)
		  (if (>_a x (a))
		      (-_a x (b))
		      (Iter-K1 (c)(+_a x (d))))))
  :hints (("Goal"
	   :use K1_x+e=Iter-K1_x+d)))

(defthm
  K2-satisfies-Gen-91-Recursion
  (implies (aofp x)
	   (equal (K2 x)
		  (if (>_a x (a))
		      (-_a x (b))
		      (Iter-K2 (c)(+_a x (d))))))
  :hints (("Goal"
	   :use K2_x+e=Iter-K2_x+d)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; So now that it has been verified that the two functions K1 and K2 satisfy
; the generalized 91 recursion scheme with parameters ( (A),(B),(C),(D) ), it
; is now verified that the two functions are, indeed, distinct when
; (D) <= (B)[(C)-1].

(in-theory (disable
	    K1-satisfies-Gen-91-Recursion
	    K2-satisfies-Gen-91-Recursion))

(defthm
  Inequality-2b
  (<_a (a)(+_a (a)(b)))
  :hints (("Goal"
	   :use (:instance
		 <_a-cancellation-laws-for-+_a
		 (x (a))(y 0)(z (b))))))

(defthm
  Inequality-2c
  (>_a (a) (-_a (a)(b))))

(defthm
  Inequality-2d
  (not (equal (a) (-_a (a)(b))))
  :hints (("Goal"
	   :in-theory (disable Inequality-2c)
	   :use Inequality-2c)))

(defthm
  K1&K2-are-not-equal-functions
  (implies (and (aofp x)
		(<=_a x (a))
		(<=_a (e) 0))
	   (not (equal (K1 x)
		       (K2 x)))))

(defthm
  K&K1-are-not-equal-functions-version-2
  (implies (<=_a (e) 0)
	   (not (equal (K1 (a))
		       (K2 (a))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Verify that any function that satisfies the simpler recurrence given in
; Knuth's Theorem, is in fact equal to K1, provided (B)[(C) - 1] < (D):

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Introduce a new function G1 of one argument that satisfies
; the simpler recurrence.

(encapsulate
 ((G1 (x) a))

 (local
  (defun
    G1 (x)
    (K1 x)))

 (defthm
   G1-satisfies-simple-recursion
   (implies (aofp x)
	    (equal (G1 x)
		   (if (>_a x (a))
		       (-_a x (b))
		       (G1 (+_a (e) x)))))
   :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Verify that G1, which satisfies the simpler recurrence,
; is in fact equal to K1, provided (B)[(C) - 1] < (D):

(defthm
  G1-when-x>a
  (implies (and (aofp x)
		(>_a x (a)))
	   (equal (G1 x)
		  (-_a x (b))))
  :hints (("Goal"
	   :use G1-satisfies-simple-recursion)))

(defthm
  G1-when-x<=a
  (implies (and (aofp x)
		(<=_a x (a)))
	   (equal (G1 (+_a (e) x))
		  (G1 x)))
  :hints (("Goal"
	   :use G1-satisfies-simple-recursion)))

(defthm
  G1=K1-when-e>0
  (implies (and (aofp x)
		(>_a (e) 0))
	   (equal (G1 x)(K1 x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Verify that any total function that satisfies the generalized 91 recursion
; must also satisfy the simpler recursion.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Introduce a new function K of one argument that satisfies the general 91
; recursion with parameters ( (A),(B),(C),(D) ).

(encapsulate
 ((K (x) a)
  (Iter-K (i x) a))

 (local
  (defun
    K (x)
    (K1 x)))

 (local
  (defun
    Iter-K (i x)
    (Iter-K1 i x)))

 (defthm
   K-satisfies-Gen-91-Recursion
   (implies (aofp x)
	    (equal (K x)
		   (if (>_a x (a))
		       (-_a x (b))
		       (Iter-K (c)(+_a x (d))))))
   :rule-classes nil
   :hints (("Goal"
	    :use K1-satisfies-Gen-91-Recursion)))

 (defthm
   Def-Iter-K
   (equal (Iter-K i x)
	  (if (zp i)
	      x
	      (K (Iter-K (- i 1) x))))
   :rule-classes :definition))

(defthm
  K-when-x>a
  (implies (and (aofp x)
		(>_a x (a)))
	   (equal (K x)(-_a x (b))))
  :hints (("Goal"
	   :use K-satisfies-Gen-91-Recursion)))

(defthm
  K-when-x<=a
  (implies (and (aofp x)
		(<=_a x (a)))
	   (equal (K x)
		  (Iter-K (c)(+_a (d) x))))
  :hints (("Goal"
	   :use K-satisfies-Gen-91-Recursion)))

(defthm
  Iter-K=K
  (equal (Iter-K 1 x)(K x))
  :hints (("Goal"
	   :use (:functional-instance
		 Iter-F=F
		 (F K)(Iter-F Iter-K)))))

(defthm
  Compose-Iter-K
  (equal (Iter-K i (Iter-K j x))
	 (iter-K (+ (nfix i)
		    (nfix j))
		 x))
  :hints (("Goal"
	   :use (:functional-instance
		 Compose-Iter-F
		 (F K)(Iter-F Iter-K)))))

(defthm
  K-satisfies-simple-recursion-when-c=1
  (implies (and (aofp x)
		(equal (c) 1))
	   (equal (K x)
		  (if (>_a x (a))
		      (-_a x (b))
		      (K (+_a (e) x)))))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (enable e))))

(defthm
  Iter-K_i_x=Iter_K_i-1_x-b-when-x>a
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(>_a x (a)))
	   (equal (Iter-K i x)
		  (iter-K (- i 1)(-_a x (b)))))
  :hints (("Goal"
	   :use (:instance
		 Compose-Iter-K
		 (i (- i 1))
		 (j 1)))))

(defthm
  Iter-K_1+i_x=Iter-K_i_K_x
  (implies (and (integerp i)
		(> i 0))
	   (equal (Iter-K (+ 1 i) x)
		  (Iter-K i (K x))))
  :hints (("Goal"
	   :use (:instance
		 Compose-Iter-K
		 (j 1)))))

(defthm
  Iter-K_i_K_x=Iter-K_c+i_d+x
  (implies (and (integerp i)
		(> i 0)
		(aofp x)
		(<=_a x (a)))
	   (equal (Iter-K i (K x))
		  (Iter-K (+_a (c) i)
			  (+_a (d) x)))))

(in-theory (disable Extension-Laws))

(in-theory (enable Reverse-Extension-Laws))

(defthm
  Equality-2
  (implies (and (aofp x)
		(integerp n))
	   (equal (+_a (d)
		       (+_a x (*_a (d)(+ -1 n))))
		  (+_a x (*_a (d) n)))))

(in-theory (disable Reverse-Extension-Laws))

(in-theory (enable Extension-Laws))

(defthm
  Iter-K_1_x=Iter-K_1+n_c-1_x+nd-induction-step-part-1
  (implies (and (integerp n)
		(> (* (- n 1)(- (c) 1)) 0)
		(aofp x)
		(<=_a (+_a x (*_a (- n 1)(d)))
		      (a)))
	   (equal (Iter-K (+ 1 (* (+ -1 n)(+ (c) -1)))
			  (+_a x (*_a (+ -1 n)(d))))
		  (Iter-K (+ 1 (* n (- (c) 1)))
			  (+_a x (*_a n (d))))))
  :hints (("Goal"
	   :use (:instance
		 Iter-K_1+i_x=Iter-K_i_K_x
		 (i (* (+ -1 n)(+ (c) -1)))
		 (x (+_a x (*_a (+ -1 n)(d))))))))

(defthm
  n-1*c-1>0
  (implies (and (integerp n)
		(> n 0)
		(not (equal n 1))
		(> (c) 1))
	   (> (* (- n 1)(- (c) 1))
	      0))
  :rule-classes nil
  :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (and (rationalp x)
				(> x 0)
				(rationalp y)
				(> y 0))
			   (> (* x y) 0)))
		 (x (- n 1))(y (- (c) 1))))))

(in-theory (disable Extension-Laws))

(in-theory (enable Reverse-Extension-Laws))

(defthm
  Inequality-4
  (implies (and (integerp n)
		(aofp x))
	   (equal (<_A (A)
		       (+_A X (*_A (D) (+ -1 N))))
		  (<_A (+_A (A) (D))
		       (+_A X (*_A (D) N))))))

(in-theory (disable Reverse-Extension-Laws))

(in-theory (enable Extension-Laws))

(defthm
  Iter-K_1_x=Iter-K_1+n_c-1_x+nd-induction-step-part-2
  (implies (and (integerp n)
		(> n 1)
		(> (c) 1)
		(aofp x)
		(>=_a (+_a (a)(d))
		      (+_a x (*_a n (d))))
		(equal (Iter-K 1 x)
		       (Iter-K (+ (- (c)) 2 (- n) (* (c) n))
			       (+_a x (*_a (d)(+ -1 n))))))
	   (equal (Iter-K 1 x)
		  (Iter-K (+ 1 (* n (- (c) 1)))
			  (+_a x (*_a n (d))))))
  :hints
  (("Goal"
    :use
    (Iter-K_1_x=Iter-K_1+n_c-1_x+nd-induction-step-part-1
     n-1*c-1>0))))

(defthm
  Iter-K_1_x=Iter-K_1+n_c-1_x+nd-induction-step
  (implies (and (integerp n)
		(< 1 n)
		(equal (Iter-K 1 x)
		       (Iter-K (+ (- (c)) 2 (- n) (* (c) n))
			       (+_a x (*_a (d)(+ -1 n)))))
		(< 1 (c))
		(aofp x)
		(<=_a (+_a x (*_a (d) n))
		      (+_a (a) (d))))
	   (equal (Iter-K 1 x)
		  (Iter-K (+ 1 (- n) (* (c) n))
			  (+_a x (*_a (d) n)))))
  :hints
  (("Goal"
    :use
    Iter-K_1_x=Iter-K_1+n_c-1_x+nd-induction-step-part-2)))

(defthm
  Iter-K_1_x=Iter-K_1+n_c-1_x+nd-base-step
  (implies (and (> (c) 1)
		(aofp x)
		(>=_a (+_a (a)(d))
		      (+_a (d) x)))
	   (equal (Iter-K 1 x)
		  (Iter-K (c)(+_a (d) x)))))

(defthm
  Iter-K_1_x=Iter-K_1+n_c-1_x+nd
  (implies (and (integerp n)
		(> n 0)
		(aofp x)
		(> (c) 1)
		(>=_a (+_a (a)(d))
		      (+_a x (*_a n (d)))))
	   (equal (Iter-K 1 x)
		  (Iter-K (+ 1 (* n (- (c) 1)))
			  (+_a x (*_a n (d))))))
  :hints (("Goal"
	   :induct (induct-on-pos-int n)
	   :in-theory (disable ITER-K=K
			       DEF-ITER-K
			       ITER-K_1+I_X=ITER-K_I_K_X))))

(defthm
  Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-1
  (implies (and (integerp i)
		(> i 1))
	   (equal (Iter-K i x)
		  (Iter-K (- i 1)(Iter-K 1 x))))
  :hints (("Goal"
	   :in-theory (disable Iter-K=K))))

(defthm
  Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-2
  (implies (and (integerp n)
		(> n 0)
		(aofp x)
		(> (c) 1)
		(>=_a (+_a (a)(d))
		      (+_a x (*_a n (d)))))
	   (equal (Iter-K (+ -1 i)
			  (Iter-K 1 x))
		  (Iter-K (+ -1 i)
			  (Iter-K (+ 1 (* n (- (c) 1)))
				  (+_a x (*_a n (d)))))))
  :hints (("Goal"
	   :in-theory (disable COMPOSE-ITER-K
			       ITER-K=K))))

(defthm
  Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-3
  (implies (and (integerp n)
		(> n 0)
		(integerp i)
		(> i 1)
		(aofp x)
		(> (c) 1))
	   (equal (Iter-K (+ -1 i)
			  (Iter-K (+ 1 (* n (+ -1 (c))))
				  (+_a x (*_a n (d)))))
		  (Iter-K (+ i (* n (- (c) 1)))
			  (+_a x (*_a n (d))))))
  :hints (("Goal"
	   :use (:instance
		 (:theorem
		  (implies (>= x 0)
			   (> (+ x 1) 0)))
		 (x (+ (- n)(* (c) n)))))))

(defthm
  Iter-K_i_x=Iter-K_i+n_c-1_x+nd
  (implies (and (integerp n)
		(> n 0)
		(integerp i)
		(> i 1)
		(> (c) 1)
		(aofp x)
		(>=_a (+_a (a)(d))
		      (+_a x (*_a n (d)))))
	   (equal (Iter-K i x)
		  (Iter-K (+ i (* n (- (c) 1)))
			  (+_a x (*_a n (d))))))
  :hints (("Goal"
	   :use (Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-2
		 Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-3)
	   :in-theory
	   (disable ITER-K=K
		    COMPOSE-ITER-K
		    DEF-ITER-K
		    Iter-K_1_x=Iter-K_1+n_c-1_x+nd
		    ;Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-2
		    ;Iter-K_i_x=Iter-K_i+n_c-1_x+nd-step-3
		    ))))

(defthm
  Inequality-a
  (implies (and (aofp d)
		(>_a d 0)
		(aofp a)
		(aofp x)
		(<=_a x a))
	   (>=_a (/_a (-_a a x) d)
		 (- (Least-nat-bound (/_a (-_a a x) d))
		    1)))
  :hints (("Goal"
	   :use ((:instance
		  Least-nat-bound-loop-is-LEAST-bound
		  (i 0)
		  (x (/_a (-_a a x) d)))
		 (:instance
		  (:theorem
		   (implies (and (aofp r)
				 (>=_a r 0))
			    (>_a (+_a 1 r) 0)))
		  (r (/_a (-_a a x) d)))))))

(defthm
  Inequality-b-lemma
  (implies (and (aofp r)
		(aofp d)
		(>_a d 0)
		(aofp n)
		(>=_a (/_a r d) (-_a n 1)))
	   (>=_a (+_a r d)(*_a n d)))
  :hints (("Goal"
	   :use (:instance
		 <_a-Cancellation-Laws-for-*_a
		 (x d)(z (-_a n 1))(y (/_a r d))))))

(defthm
  Inequality-b
  (implies (and (aofp d)
		(>_a d 0)
		(aofp a)
		(aofp x)
		(<=_a x a))
	   (>=_a (+_a a d)
		 (+_a x
		      (*_a (Least-nat-bound (/_a
					     (-_a a x)
					     d))
			   d))))
  :hints (("Goal"
	   :use (Inequality-a
		 (:instance
		  <_a-Cancellation-Laws-for-+_a
		  (y (+_A A D (-_A X)))
		  (z (*_A D
			  (LEAST-NAT-BOUND-LOOP
			   0
			   (-_A (/_A A d)
                                (/_A X d))))))
		 (:instance
		  Inequality-b-lemma
		  (r (-_a a x))
		  (n (Least-nat-bound (/_a (-_a a x) d))
		     ))))))

(defthm
  Iter-K_i_x=Iter-K_i-1+n_c-1_x+nd-b-step-1
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(> (c) 1)
		(<=_a x (a)))
	   (equal (Iter-K i x)
		  (Iter-K (+ i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (+_a x
			     (*_a (Least-nat-bound
				   (/_a (-_a (a) x)(d)))
				  (d))))))
  :hints (("Goal"
	   :in-theory
	   (disable ITER-K_1_X=ITER-K_1+N_C-1_X+ND-BASE-STEP
		    ITER-K_I_X=ITER-K_I+N_C-1_X+ND-STEP-1)
	   :use ((:instance
		  Iter-K_i_x=Iter-K_i+n_c-1_x+nd
		  (n (Least-nat-bound (/_a (-_a (a) x)(d)))))
		 (:instance
		  Inequality-b
		  (a (a))(d (d)))))))

(defthm
  Inequality-c-lemma
  (implies (and (integerp i)
		(> i 1)
		(integerp n)
		(>= n 0))
	   (> (+ i (* n (- (c) 1)))
	      1)))

(defthm
  Inequality-c
  (implies (and (aofp x)
		(integerp i)
		(> i 1))
	   (> (+ i (* (Least-nat-bound (/_a (-_a (a) x)(d)))
		      (- (c) 1)))
	      1))
  :hints (("Goal"
	   :use (:instance
		 Inequality-c-lemma
		 (n (Least-nat-bound (/_a (-_a (a) x)(d))))))))

(defthm
  Iter-K_i_x=Iter-K_i-1+n_c-1_x+nd-b-step-2
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(> (c) 1)
		(<=_a x (a)))
	   (equal (Iter-K (+ i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (+_a x
			       (*_a (Least-nat-bound
				     (/_a (-_a (a) x)(d)))
				    (d))))
		  (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (K (+_a x
				  (*_a (Least-nat-bound
					(/_a (-_a (a) x)(d)))
				       (d)))))))
  :hints (("Goal"
	   :in-theory (disable DEF-ITER-K
			       Least-nat-bound)
	   :use ((:instance
		  Compose-Iter-K
		  (i (+ -1 i
			(* (Least-nat-bound
			    (/_a (-_a (a) x)(d)))
			   (- (c) 1))))
		  (j 1)
		  (x (+_a x
			  (*_a (Least-nat-bound
				(/_a (-_a (a) x)(d)))
			       (d)))))))
	  ("Subgoal 2"
	   :use inequality-c)))

(defthm
  Inequality-e-lemma
  (implies (and (aofp a)
		(aofp d)
		(aofp x)
		(>_a d 0))
	   (<_a (-_a a x)
		 (*_a d
		      (Least-nat-bound (/_a
					(-_a a x)
					d)))))
  :hints (("Goal"
	   :in-theory (disable <_a-Cancellation-Laws-for-*_a
			        LEAST-NAT-BOUND-IS-A-BOUND)
	   :use ((:instance
		   LEAST-NAT-BOUND-IS-A-BOUND
		   (i 0)(x (/_a (-_a a x) d)))
		 (:instance
		  <_a-Cancellation-Laws-for-*_a
		  (y (/_a (-_a a x) d))
		  (z (Least-nat-bound (/_a (-_a a x) d)))
		  (x d))))))

(defthm
  Inequality-e
  (implies (and (aofp a)
		(aofp d)
		(aofp x)
		(>_a d 0))
	   (<_a a (+_a x (*_a d
			      (Least-nat-bound (/_a
						(-_a a x)
						d))))))
  :hints (("Goal"
	   :use Inequality-e-lemma)))

(defthm
  Iter-K_i_x=Iter-K_i-1+n_c-1_x+nd-b-step-3
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(> (c) 1)
		(<=_a x (a)))
	   (equal (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (K (+_a x
				  (*_a (Least-nat-bound
					(/_a (-_a (a) x)(d)))
				       (d)))))
		  (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (-_a (+_a x
				    (*_a (Least-nat-bound
					  (/_a (-_a (a) x)
					       (d)))
					 (d)))
			       (b)))))
  :hints (("Goal"
	   :use (:instance
		 Inequality-e
		 (a (a))(d (d))))))

(defthm
  Iter-K_i_x=Iter-K_i-1+n_c-1_x+nd-b
  (implies (and (integerp i)
		(> i 1)
		(aofp x)
		(> (c) 1)
		(<=_a x (a)))
	   (equal (Iter-K i x)
		  (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (-_a (+_a x
				    (*_a (Least-nat-bound
					  (/_a (-_a (a) x)
					       (d)))
					 (d)))
			       (b)))))
  :hints (("Goal"
	   :use (Iter-K_i_x=Iter-K_i-1+n_c-1_x+nd-b-step-2
		 Iter-K_i_x=Iter-K_i-1+n_c-1_x+nd-b-step-3
		 ))))

(defthm
  Inequality-f
  (<_a (+_A (A) (D))
       (+_A (A) (+_A (B) (D))))
  :hints (("Goal"
	   :use (:instance
		 compatibility-laws
		 (x (d))(y 0)(z (b))))))

(defthm
  Iter-K_i-1_x-b=Iter-K_i-1+n_c-1_x+nd-b-when-i=2
  (implies (and (equal i 2)
		(> (c) 1)
		(aofp x)
		(<=_a x (a)))
	   (equal (Iter-K (+ -1 i)
			  (+_a x (-_a (b))))
		  (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (-_a (+_a x (*_a
				       (Least-nat-bound
					(/_a (-_a (a) x)(d)))
				       (d)))
			       (b)))))
  :hints (("Goal"
	   :in-theory
	   (disable
	    ITER-K_1_X=ITER-K_1+N_C-1_X+ND-BASE-STEP
	    ITER-K_I_X=ITER-K_I+N_C-1_X+ND-STEP-1
	    ITER-K=K
	    COMPOSE-ITER-K
	    DEF-ITER-K
	    )
	   :use ((:instance
		  transitivity-of-<_a
		  (x (+_A (A) (D)))
		  (y (+_A (A) (+_A (B) (D))))
		  (z (+_A X
			  (*_A
			   (D)
			   (Least-nat-bound (/_a (-_a (a) x)
						 (d)))))))
		 (:instance
		  Iter-K_1_x=Iter-K_1+n_c-1_x+nd
		  (x (-_a x (b)))
		  (n (Least-nat-bound
		      (/_a (-_a (a) x)(d)))))
		 (:instance
		  Inequality-b
		  (a (a))(d (d)))))))

(defthm
  Iter-K_i-1_x-b=Iter-K_i-1+n_c-1_x+nd-b-when-i>2
  (implies (and (integerp i)
		(> i 2)
		(> (c) 1)
		(aofp x)
		(<=_a x (a)))
	   (equal (Iter-K (+ -1 i)
			  (+_a x (-_a (b))))
		  (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (-_a (+_a x (*_a
				       (Least-nat-bound
					(/_a (-_a (a) x)(d)))
				       (d)))
			       (b)))))
  :hints (("Goal"
	   :in-theory
	   (disable
	    ITER-K_I_X=ITER-K_I+N_C-1_X+ND-STEP-1
	    ITER-K_I_X=ITER-K_I-1+N_C-1_X+ND-B
	    ITER-K_I_X=ITER-K_I-1+N_C-1_X+ND-B-STEP-1
	    ITER-K_I_X=ITER_K_I-1_X-B-WHEN-X>A
	    DEF-ITER-K)
	   :use ((:instance
		  Iter-K_i_x=Iter-K_i+n_c-1_x+nd
		  (i (- i 1))
		  (x (-_a x (b)))
		  (n (Least-nat-bound
		      (/_a (-_a (a) x)(d)))))
		 (:instance
		  Inequality-b
		  (a (a))(d (d)))))))

(defthm
  Iter-K_i-1_x-b=Iter-K_i-1+n_c-1_x+nd-b
  (implies (and (integerp i)
		(> i 1)
		(> (c) 1)
		(aofp x)
		(<=_a x (a)))
	   (equal (Iter-K (+ -1 i)
			  (+_a x (-_a (b))))
		  (Iter-K (+ -1 i
			     (* (Least-nat-bound
				 (/_a (-_a (a) x)(d)))
				(- (c) 1)))
			  (-_a (+_a x (*_a
				       (Least-nat-bound
					(/_a (-_a (a) x)(d)))
				       (d)))
			       (b)))))
  :hints (("Goal"
	   :in-theory
	   (disable ITER-K_I_X=ITER-K_I+N_C-1_X+ND-STEP-1
		    ITER-K_1_X=ITER-K_1+N_C-1_X+ND-BASE-STEP
		    ITER-K_1+I_X=ITER-K_I_K_X
		    K-WHEN-X<=A
		    ITER-K=K)
	   :use
	   (Iter-K_i-1_x-b=Iter-K_i-1+n_c-1_x+nd-b-when-i=2
	    Iter-K_i-1_x-b=Iter-K_i-1+n_c-1_x+nd-b-when-i>2)
	   )))

(defthm
  Iter-K_i_x=Iter-K_i-1_x-b-when-x<=a
  (implies (and (integerp i)
		(> i 1)
		(> (c) 1)
		(aofp x)
		(<=_a x (a)))
	   (equal (Iter-K i x)
		  (Iter-K (- i 1)
			  (-_a x (b)))))
  :hints (("Goal"
	   :use
	   Iter-K_i-1_x-b=Iter-K_i-1+n_c-1_x+nd-b)))

(defthm
  Iter-K_i_x=Iter-K_i-1_x-b
  (implies (and (integerp i)
		(> i 1)
		(> (c) 1)
		(aofp x))
	   (equal (Iter-K i x)
		  (Iter-K (- i 1)
			  (-_a x (b)))))
  :hints (("Goal"
	   :in-theory (disable
		       ITER-K_I_X=ITER-K_I-1+N_C-1_X+ND-B-STEP-1
		       ITER-K_I_X=ITER-K_I-1+N_C-1_X+ND-B
		       ITER-K_I_X=ITER-K_I-1_X-B-WHEN-X<=A
		       ITER-K_I_X=ITER-K_I+N_C-1_X+ND-STEP-1)
	   :use Iter-K_i_x=Iter-K_i-1_x-b-when-x<=a)))

(in-theory (disable Extension-Laws))

(in-theory (enable Reverse-Extension-Laws))

(defthm
  Equality-a
  (implies (and (aofp x)
		(rationalp j))
	   (EQUAL
	    (+_A (-_A (B))(+_A X (-_A (*_A (B) (+ -1 J)))))
	    (+_A X (-_A (*_A (B) J))))))

(in-theory (disable Reverse-Extension-Laws))

(in-theory (enable Extension-Laws))

(defthm
  Iter-K_i_x=Iter-K_i-j_i-jb
  (implies (and (integerp i)
		(> i 1)
		(> (c) 1)
		(> i j)
		(integerp j)
		(> j 0)
		(aofp x))
	   (equal (Iter-K i x)
		  (Iter-K (- i j)
			  (-_a x (*_a (b) j)))))
  :hints (("Goal"
	   :induct (induct-on-pos-int j))))

(defthm
  Iter-K_c_x=Iter-K_x-_c-1_b
  (implies (and (> (c) 1)
		(aofp x))
	   (equal (Iter-K (c) x)
		  (K (-_a x (*_a (b)(- (c) 1))))))
  :hints (("Goal"
	   :use (:instance
		 Iter-K_i_x=Iter-K_i-j_i-jb
		 (i (c))(j (- (c) 1))))))

(defthm
  K_x=K_x+d-_c-1_b
  (implies (and (> (c) 1)
		(aofp x)
		(<=_a x (a)))
	   (equal (K x)
		  (K (+_a x (e)))))
  :hints (("Goal"
	   :in-theory (enable e))))

(defthm
  K-satisfies-simple-rec-when-c>1
  (implies (and (> (c) 1)
		(aofp x))
	   (equal (K x)
		  (if (>_a x (a))
		      (-_a x (b))
		      (K (+_a x (e)))))))

(defthm
  K-satisfies-simple-rec
  (implies (aofp x)
	   (equal (K x)
		  (if (>_a x (a))
		      (-_a x (b))
		      (K (+_a x (e))))))
  :hints (("Goal"
	   :in-theory (disable
		       K-satisfies-simple-rec-when-c>1
		       K_X=K_X+D-_C-1_B
		       ITER-K_C_X=ITER-K_X-_C-1_B
		       ITER-K_I_X=ITER-K_I-J_I-JB
		       ITER-K_I_X=ITER-K_I-1_X-B
		       ITER-K_I_X=ITER-K_I+N_C-1_X+ND-STEP-1
		       ;H-WHEN-X>A
		       ;H-WHEN-X<=A
		       )
	   :use (K-satisfies-simple-recursion-when-c=1
		 K-satisfies-simple-rec-when-c>1
		 ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Verify that any function such as K, that satisfies the generalized
;; 91 recursion, is in fact equal to K1, provided (B)[(C) - 1] < (D):

(defthm
  K=K1-when-b_c-1<d
  (implies (and (aofp x)
		(>_a (e) 0))
	   (equal (K x)
		  (K1 x)))
  :hints (("Goal"
	   :in-theory
	   (disable K-satisfies-simple-rec-when-c>1
		    K-satisfies-simple-rec
		    K-WHEN-X<=A
		    ;H-WHEN-X>A
		    )
	   :use (:functional-instance
		 G1=K1-when-e>0
		 (G1 K)))
	  ("Goal'"
	   :use K-satisfies-simple-rec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Finally, verify that the recursion halts for any function such as K, that
;; satisfies the generalized 91 recursion, provided (B)[(C) - 1] < (D):
;;
;; The recursive calls occur for X <= (A):
;;
;;   K(X) = Iter-K( (C), X + (D) ) = K(...K(X + (D))...).
;;
;; So K is recursively called, first on X + (D), then on K(X + (D)),
;; then on Iter-K( 2, X+(D) ),..., and finally on Iter-K( (C)-1, X+(D)).
;;
;; An ordinal measure is used to demonstrate termination. The
;; demonstration incurs the following proof obligations for each X and
;; each integer i, such that 0 < i < (C):
;;
;;  1.  Measure(X) is an ordinal less than epsilon_0.
;;
;;  2.  If X <= (A), then measure(X + (D)) < measure(X).
;;
;;  3.  If X <= (A), then measure(Iter-K( i, X+(D) )) < measure(X).

(defun
    measure(x)
    (let ((x (afix x)))
         (cond ((>_a x (a))
		0)
	       ((>_a (e) 0)
		(Least-nat-bound (/_a (-_a (a) x)
				      (e))))
	       (t 0))))

(defthm
    Proof-obligation-1
    (E0-ordinalp(measure x)))

(defthm
    Measure>=0
    (>= (measure x) 0)
    :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Life without linear arithmetic for <_a is HARD:

(defthm
    e-<=_a-d
    (<=_a (e)(d))
    :hints (("Goal"
	     :in-theory (enable e)
	     :use (:instance
		   +_a-Compatibility-of-<=_a
		   (x1 0)
		   (x2 (*_a (b)(-_a (c) 1)))
		   (y1 (e))
		   (y2 (e))))))

(defthm
    Pos-not-zero-rewrite
    (implies (and (aofp x)
		  (>_a x 0))
	     (not (equal x 0))))

(defthm
    Inequality-i
    (implies (and (aofp x)
		  (aofp y)
		  (>=_a y (+_a x (e))))
	     (>=_a (+_a (a)(-_a y (+_a x (e))))
		   (a)))
    :hints (("Goal"
	     :use (:instance
		   +_a-Compatibility-of-<=_a
		   (x1 (a))(x2 (a))
		   (y1 0)(y2 (-_a y (+_a x (e))))))))

(defthm
    Inequality-ii
    (implies (and (>_a (e) 0)
		  (aofp x)
		  (aofp y)
		  (>=_a y (+_a x (e))))
	     (>=_a (-_a (/_a (-_a (a) x)(e)) 1)
		   (/_a (-_a (a) y)(e))))
    :hints (("Goal"
	     :use Inequality-i)))

(defthm
    Measure-inequality
    (implies (and (>_a (e) 0)
		  (aofp x)
		  (<=_a x (a))
		  (aofp y)
		  (>=_a y (+_a x (e))))
	     (< (measure y)
		(measure x)))
    :hints (("Goal"
	     :use ((:instance
		    Least-nat-bound-is-increasing-2
		    (x1 (/_a (-_a (a) y)(e)))
		    (x2 (/_a (-_a (a) x)(e))))
		   Inequality-ii))))

(in-theory (disable measure))

(defthm
    Proof-obligation-2
    (implies (and (>_a (e) 0)
		  (aofp x)
		  (<=_a x (a)))
	     (< (measure (+_a x (d)))
		(measure x))))

(defun
    ei (i)
    (if (and (integerp i)
	     (< 0 i)
	     (<= i (c)))
	(-_a (d)(*_a (- i 1)(b)))
        (e)))

(defthm
    Aofp-ei
    (aofp (ei i)))

(in-theory (disable extension-laws))
(in-theory (enable e reverse-extension-laws))

(defthm
    e-<=_a-ei
    (<=_a (e)(ei i))
    :hints (("Goal"
	     :use (:instance
		   +_a-Compatibility-of-<=_a
		   (x1 (d))(x2 (d))
		   (y1 (+_a (-_a (*_a (b)(c)))
			    (*_A (b) I)))
		   (y2 0)))))

(in-theory (disable e reverse-extension-laws))
(in-theory (enable extension-laws))

(defthm
    ei-=-e
    (implies (>= i (c))
	     (equal (ei i) (e)))
    :hints (("Goal"
	     :in-theory (enable e))))

(in-theory (disable extension-laws))
(in-theory (enable reverse-extension-laws))

(defthm
    Distributivity-aofp-rationalp
    (implies (and (aofp x)
		  (rationalp y)
		  (rationalp z))
	     (equal (*_a x (+ y z))
		    (+_a (*_a x y)(*_a x z)))))

(in-theory (disable reverse-extension-laws))
(in-theory (enable extension-laws))

(in-theory (disable Distributivity-aofp-rationalp))

(defthm
    Equality-i
    (implies (and (integerp i)
		  (< 0 i)
		  (< i (c)))
	     (equal (-_a (ei i)
			 (b))
		    (ei (+ i 1))))
  :hints (("Subgoal 1'"
	   :in-theory (enable Distributivity-aofp-rationalp))))

(in-theory (disable ei))

(in-theory (disable K-when-x<=a
		    K_x=K_x+d-_c-1_b
		    K-satisfies-simple-rec-when-c>1
		    K-satisfies-simple-rec
		    K=K1-when-b_c-1<d))

(defthm
    K-satisfies-simple-rec-rewrite
    (implies (and (aofp x)
		  (<=_a x (a)))
	     (equal (K (+_a (e) x))
		    (K x)))
  :hints (("Goal"
	   :use K-satisfies-simple-rec)))

(defthm
    Aofp-K
    (implies (and (>_a (e) 0)
		  (aofp x))
	     (aofp (K x)))
    :hints (("Goal"
	     :induct (K1 x))))

(defun
    Induct-hint (x i)
    (declare (xargs :measure (measure (+_a x (ei i)))))
    (if (aofp x)
	(cond ((>_a (+_a x (ei i))(a))
	       t)
	      ((>_a (e) 0)
	       (Induct-hint (+_a x (e)) i))
	      (t t))
        t))

(defthm
    Inequality-iii
    (implies (and (>_a (e) 0)
		  (aofp x))
	     (>_a (+_a (e) x) x))
    :hints (("Goal"
	     :use (:instance
		   compatibility-laws
		   (y 0)(z (e))))))

(defthm
    Inequality-iv
    (implies (and (>_a (e) 0)
		  (aofp x)
		  (integerp i)
		  (< 0 i)
		  (< i (c)))
	     (<=_a (+_a (e) x)
		   (K (+_a x (ei i)))))
    :hints (("Goal"
	     :induct (Induct-hint x i))))

(defthm
    measure-inequality-i
    (implies (and (>_a (e) 0)
		  (aofp x)
		  (<=_a x (a))
		  (integerp i)
		  (< 0 i)
		  (< i (c)))
	     (< (measure (K (+_a x (ei i))))
		(measure x))))

(in-theory (enable ei))

(defthm
    Equality-ii
    (implies (and (aofp x)
		  (integerp i)
		  (< 1 i)
		  (< i (c)))
	     (equal (Iter-K i (+_a (d) x))
		    (K (+_a x (ei i)))))
    :hints (("Goal"
	     :use (:instance
		   Iter-K_i_x=Iter-K_i-j_i-jb
		   (j (- i 1))(x (+_a x (d)))))))

(defthm
    Equality-iii
    (implies (and (aofp x)
		  (integerp i)
		  (< 0 i)
		  (< i (c)))
	     (equal (Iter-K i (+_a (d) x))
		    (K (+_a x (ei i)))))
  :hints (("Goal"
	   :in-theory (disable (:executable-counterpart ei))
	   :cases ((< 1 i)))))

(in-theory (disable ei))

(defthm
    Proof-obligation-3
    (implies (and (>_a (e) 0)
		  (aofp x)
		  (<=_a x (a))
		  (integerp i)
		  (< 0 i)
		  (< i (c)))
	     (< (measure (Iter-K i (+_a x (d))))
		(measure x))))
