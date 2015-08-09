; Arithmetic-5 Library, Robert Krug
; This file Copyright (C) 1998  John R. Cowles, University of Wyoming
; License:
; As described in the LICENSE file at the top level of the arithmetic-5
; library.
; (Note from Matt Kaufmann:
; John Cowles has granted explicit permission for this license in an
; email to me on 8/5/2013.)

; ACL2 Arithmetic Nonnegative Integer Mod and Gcd book.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

#| Summer 1997
     Last modified 30 June 1998

      Depends on the Arithmetic Equalities book
             and the Arithmetic Inequalities book.

   Disabled theorems:
     Divisor-<=
     Linear-combination-for-nonneg-int-gcd

This book is used to prove all the axioms in the
     Arithmetic Rationals-with-axioms book
     [All the axioms in that book are
      now theorems in the book
      Rationals-with-axioms-proved]

   To certify in Arithmetic Book directory:

      (certify-book "mod-gcd")

|#

(in-package "ACL2")


(local (include-book "basic-arithmetic"))
(local (include-book "inequalities"))
(local (include-book "prefer-times"))
(local (include-book "non-linear"))

;;;;;;;;;;;;;;;;;;;;
;; Nonneg-int-mod ;;
;;;;;;;;;;;;;;;;;;;;

(defun
  nonneg-int-mod ( n d )
  (declare (xargs :guard (and (integerp n)
			      (>= n 0)
			      (integerp d)
			      (< 0 d))))
  (if (zp d)
      (nfix n)
      (if (< (nfix n) d)
	  (nfix n)
	(nonneg-int-mod (- n d) d))))

(defthm
  Nonneg-int-mod-<-divisor
  (implies (and (integerp d)
		(< 0 d))
	   (< (nonneg-int-mod n d) d))
  :rule-classes :linear)

(defthm
  Nonneg-int-mod-nonnegative-integer-quotient
  (equal (+ (nonneg-int-mod n d)
	    (* (nfix d)(nonnegative-integer-quotient n d)))
	 (nfix n))
  :rule-classes ((:elim
		  :corollary
		  (implies (and
			    (integerp n)
			    (integerp d)
			    (>= n 0)
			    (>= d 0))
			   (equal
			    (+
			     (nonneg-int-mod n d)
			     (* d
				(nonnegative-integer-quotient n
							      d)))
			    n)))))

(defthm
  Nonneg-int-mod-0
  (equal (nonneg-int-mod 0 d) 0)
  :hints (("Goal"
	   :use (:instance
		 Nonneg-int-mod-nonnegative-integer-quotient
		 (n 0)))))

(local
 (defun
   induct-on-nonneg-int ( j )
   (if (zp j)
       t
       (induct-on-nonneg-int (- j 1)))))

(defthm hack
    (equal (* -1 x)
           (- x)))

(defthm
  Nonneg-int-mod-+-*
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(>= x 0)
		(< x n)
		(>= j 0))
	   (equal (nonneg-int-mod (+ x (* j n)) n)
		  x))
     :hints (("Goal"
	      :induct (induct-on-nonneg-int j))))

(defthm
  Nonneg-int-mod-+-*-nonneg-int-mod
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(>= j 0)
		(< 0 n)
		(>= x 0))
	   (equal (nonneg-int-mod (+ x (* j n)) n)
		  (nonneg-int-mod x n))))

(defthm
  Nonneg-int-mod-+-*-nonneg-int-mod-1
  (implies (and (integerp j)
		(integerp k)
		(integerp n)
		(integerp x)
		(>= j 0)
		(>= k 0)
		(< 0 n)
		(>= x 0)
		(equal (nonneg-int-mod k n) 0))
	   (equal (nonneg-int-mod (+ x (* j k)) n)
		  (nonneg-int-mod x n)))
    :hints (("Goal"
	     :in-theory (disable Nonneg-int-mod-+-*-nonneg-int-mod)
	     :use (:instance
		   Nonneg-int-mod-+-*-nonneg-int-mod
		   (j (* j (nonnegative-integer-quotient k n))))
	     )))

(defthm
  Divisor-nonnegative-integer-quotient
  (implies (equal (nonneg-int-mod n d) 0)
	   (equal (* (nfix d)
		     (nonnegative-integer-quotient n d))
		  (nfix n)))
  :rule-classes nil)

(defthm
  Left-nonneg-int-mod-*
  (implies (and (integerp j)
		(integerp n)
		(>= n 0))
	   (equal (nonneg-int-mod (* j n) n) 0))
  :hints (("Goal"
	   :induct (induct-on-nonneg-int j))))

(defthm
  Right-nonneg-int-mod-*
  (implies (and (integerp j)
		(integerp n)
		(>= n 0))
	   (equal (nonneg-int-mod (* n j) n) 0)))

(defthm
  Nonneg-int-mod-*-0
  (implies (and (integerp j)
		(integerp y)
		(>= j 0)
		(equal (nonneg-int-mod j n) 0))
	   (equal (nonneg-int-mod (* j y) n) 0))
  :hints (("Goal"
	   :in-theory (disable Right-nonneg-int-mod-*)
	   :use ((:instance
		  Right-nonneg-int-mod-*
		  (j (* y (nonnegative-integer-quotient j n)))))
	   )))

(defthm
  Nonneg-Int-mod-+-0
  (implies (and (integerp x)
		(>= x 0)
		(>= y 0)
		(equal (nonneg-int-mod x n) 0)
		(equal (nonneg-int-mod y n) 0))
	   (equal (nonneg-int-mod (+ x y) n) 0)))

(defthm
  Nonneg-Int-mod-minus-0
  (implies (and (integerp x)
		(integerp y)
		(>= y 0)
		(equal (nonneg-int-mod x n) 0)
		(equal (nonneg-int-mod y n) 0))
	   (equal (nonneg-int-mod (- x y) n) 0))
  :hints (("Goal"
	   :in-theory (disable Right-nonneg-int-mod-*)
	   :use (:instance
		 Right-nonneg-int-mod-*
		 (j (- (nonnegative-integer-quotient x n)
		       (nonnegative-integer-quotient y n)))))))

(defthm
  Linear-combination-nonneg-int-mod
  (implies (and (integerp a)
		(integerp b)
		(integerp x)
		(integerp y)
		(>= a 0)
		(>= b 0)
		(equal (nonneg-int-mod a n) 0)
		(equal (nonneg-int-mod b n) 0))
	   (equal (nonneg-int-mod (+ (* a x)(* b y)) n) 0))
  :hints (("Goal"
	   :in-theory (disable Nonneg-Int-mod-minus-0)
	   :use ((:instance
		  Nonneg-Int-mod-minus-0
		  (x (* a x))
		  (y (* b (- y))))
		 (:instance
		  Nonneg-int-mod-*-0
		  (j b)
		  (y (- y)))
		 (:instance
		  Nonneg-Int-mod-minus-0
		  (x (* b y))
		  (y (* a (- x))))
		 (:instance
		  Nonneg-int-mod-*-0
		  (j a)
		  (y (- x)))))))

(defthm
  Divisor-<=
  (implies (and (integerp n)
		(> n 0)
		(equal (nonneg-int-mod n d) 0))
	   (<= d n)))

(in-theory (disable Divisor-<=))

(defthm
  Nonneg-int-mod-1
  (equal (nonneg-int-mod n 1) 0))

;;;;;;;;;;;;;;;;;;;;
;; Nonneg-int-gcd ;;
;;;;;;;;;;;;;;;;;;;;

(defun
  nonneg-int-gcd ( x y )
  (declare (xargs :guard (and (integerp x)
			      (>= x 0)
			      (integerp y)
			      (>= y 0))))
  (if (zp y)
      (nfix x)
      (nonneg-int-gcd y (nonneg-int-mod x y))))

(defthm
  Nonneg-int-gcd->-0
  (implies (or (and (integerp d)
		    (> d 0))
	       (and (integerp n)
		    (> n 0)))
	   (> (nonneg-int-gcd n d) 0))
  :rule-classes :type-prescription)

(defthm
    Nonneg-int-gcd-is-COMMON-divisor
    (and (equal (nonneg-int-mod x (nonneg-int-gcd x y))
		0)
	 (equal (nonneg-int-mod y (nonneg-int-gcd x y))
		0)))

(mutual-recursion
 (defun
     nonneg-int-gcd-multiplier1 ( x y )
     (declare (xargs :guard (and (integerp x)
				 (integerp y)
				 (>= x 0)
				 (>= y 0))))
     (if (zp y)
	 1
         (nonneg-int-gcd-multiplier2 y (nonneg-int-mod x y))))

  (defun
     nonneg-int-gcd-multiplier2 ( x y )
     (declare (xargs :guard (and (integerp x)
				 (integerp y)
				 (>= x 0)
				 (>= y 0))))
     (if (zp y)
	 0
         (+ (nonneg-int-gcd-multiplier1 y (nonneg-int-mod x y))
	    (- (* (nonneg-int-gcd-multiplier2 y
					      (nonneg-int-mod x y))
		  (nonnegative-integer-quotient x y)))))))

(defthm
    Linear-combination-for-nonneg-int-gcd
    (equal (nonneg-int-gcd x y)
	   (+ (* (nfix x)
		 (nonneg-int-gcd-multiplier1 x y))
	      (* (nfix y)
		 (nonneg-int-gcd-multiplier2 x y)))))

(in-theory (disable Linear-combination-for-nonneg-int-gcd))

(defthm
  Nonneg-int-gcd-is-LARGEST-common-divisor-mod
  (implies (and (equal (nonneg-int-mod x d) 0)
		(equal (nonneg-int-mod y d) 0))
	   (equal (nonneg-int-mod (nonneg-int-gcd x y) d)
		  0))
  :hints (("Goal"
	   :in-theory
	   (enable Linear-combination-for-nonneg-int-gcd))))

(defthm
  Nonneg-int-gcd-is-LARGEST-common-divisor-<=
  (implies (and (or (and (integerp x)
			 (> x 0))
		    (and (integerp y)
			 (> y 0)))
		(equal (nonneg-int-mod x d) 0)
		(equal (nonneg-int-mod y d) 0))
	   (<= d (nonneg-int-gcd x y)))
  :hints (("Goal"
	   :in-theory (enable Divisor-<=))))

(defthm
  Nonnegative-integer-quotient-gcd
  (implies (and (integerp x)
		(integerp y)
		(>= x 0)
		(>= y 0))
	   (and (equal (* (nonneg-int-gcd x y)
			  (nonnegative-integer-quotient
			   x
			   (nonneg-int-gcd x y)))
		       x)
		(equal (* (nonneg-int-gcd x y)
			  (nonnegative-integer-quotient
			   y
			   (nonneg-int-gcd x y)))
		       y)))
  :hints (("Goal"
	   :use ((:instance
		  Divisor-nonnegative-integer-quotient
		  (n x)
		  (d (nonneg-int-gcd x y)))
		 (:instance
		  Divisor-nonnegative-integer-quotient
		  (n y)
		  (d (nonneg-int-gcd x y)))))))

(defthm
  Linear-combination-gcd=1
  (implies (and (integerp x)
		(equal (nonneg-int-gcd y z) 1))
	   (equal (+ (* x y (nonneg-int-gcd-multiplier1 y z))
		     (* x z (nonneg-int-gcd-multiplier2 y z)))
		  x)))

(defthm
  Divisor-of-product-divides-factor
  (implies (and (equal (nonneg-int-mod (* x y) z) 0)
		(equal (nonneg-int-gcd y z) 1)
		(integerp x)
		(integerp y)
		(>= x 0)
		(>= y 0))
	   (equal (nonneg-int-mod x z) 0))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Linear-combination-nonneg-int-mod
		  (a (* x y))
		  (b z)
		  (n z)
		  (x (nonneg-int-gcd-multiplier1 y z))
		  (y (* x (nonneg-int-gcd-multiplier2 y z))))))))

(defthm
  Nonneg-int-mod-abs-+-*
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(<= 0 n))
	   (equal (nonneg-int-mod (abs (+ x (* j n)))
				  (nonneg-int-gcd (abs x) n))
		  0))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(<= 0 n)
				(<= (+ x (* j n)) 0)
				(<= x 0))
			   (equal
			    (nonneg-int-mod (+ (- x)(- (* j n)))
					    (nonneg-int-gcd (- x)
							    n))
			    0))
		  :hints (("Goal"
			   :cases ((< (+ x (* j n)) 0)))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(<= 0 n)
				(<= 0 (+ x (* j n)))
				(<= x 0))
			   (equal
			    (nonneg-int-mod (+ x (* j n))
					    (nonneg-int-gcd (- x)
							    n))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(<= 0 n)
				(<= (+ x (* j n)) 0)
				(<= 0 x))
			   (equal
			    (nonneg-int-mod (+ (- x) (- (* j n)))
					    (nonneg-int-gcd x n))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(<= 0 n)
				(<= 0 (+ x (* j n)))
				(<= 0 x))
			   (equal
			    (nonneg-int-mod (+ x (* j n))
					    (nonneg-int-gcd x n))
			    0))))
  :hints (("Subgoal 4"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a (- x))
		 (b n)
		 (x 1)
		 (y (- j))
		 (n (nonneg-int-gcd (- x) n))))
	  ("Subgoal 3"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a (- x))
		 (b n)
		 (x -1)
		 (y j)
		 (n (nonneg-int-gcd (- x) n))))
	  ("Subgoal 2"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a x)
		 (b n)
		 (x -1)
		 (y (- j))
		 (n (nonneg-int-gcd x n))))
	  ("Subgoal 1"
	   :use (:instance
		 linear-combination-nonneg-int-mod
		 (a x)
		 (b n)
		 (x 1)
		 (y j)
		 (n (nonneg-int-gcd x n))))))

(defthm
  Nonneg-int-gcd-abs->=
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(< 0 n))
	   (>= (nonneg-int-gcd (abs (+ x (* j n))) n)
	       (nonneg-int-gcd (abs x) n)))
  :rule-classes nil)

(defthm
  Nonneg-int-mod-abs
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(< 0 n))
	   (equal
	    (nonneg-int-mod (abs x)
			    (nonneg-int-gcd (abs (+ x (* j n)))
					    n))
	    0))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(<= 0 n)
				(<= (+ x (* j n)) 0)
				(<= x 0))
			   (equal
			    (nonneg-int-mod (- x)
					    (nonneg-int-gcd
					     (+ (- x)(- (* j n)))
					     n))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= 0 (+ x (* j n)))
				(<= x 0))
			   (equal
			    (nonneg-int-mod (- x)
					    (nonneg-int-gcd
					     (+ x (* j n))
					     n))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= (+ x (* j n)) 0)
				(<= 0 x))
			   (equal
			    (nonneg-int-mod x
					    (nonneg-int-gcd
					     (+ (- x)(- (* j n)))
					     n))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= 0 (+ x (* j n)))
				(<= 0 x))
			   (equal
			    (nonneg-int-mod x
					    (nonneg-int-gcd
					     (+ x (* j n))
					     n))
			    0))))
  :hints (("Subgoal 4"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a (+ (- x)(- (* j n))))
		 (b n)
		 (x 1)
		 (y j)
		 (n (nonneg-int-gcd (+ (- x)(- (* j n))) n))))
	  ("Subgoal 3"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a (+ (- x) (- (* j n))))
		 (b n)
		 (x -1)
		 (y (- j))
		 (n (nonneg-int-gcd (+ (- x) (- (* j n))) n))))
	  ("Subgoal 2"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a (+ x (* j n)))
		 (b n)
		 (x -1)
		 (y j)
		 (n (nonneg-int-gcd (+ x (* j n)) n))))
	  ("Subgoal 1"
	   :use (:instance
		 Linear-combination-nonneg-int-mod
		 (a (+ x (* j n)))
		 (b n)
		 (x 1)
		 (y (- j))
		 (n (nonneg-int-gcd (+ x (* j n)) n))))))

(defthm
  Nonneg-int-gcd-abs-<=
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(< 0 n))
	   (<= (nonneg-int-gcd (abs (+ x (* j n))) n)
	       (nonneg-int-gcd (abs x) n)))
  :rule-classes nil)

(defthm
  Nonneg-int-gcd-abs
  (implies (and (integerp j)
		(integerp n)
		(integerp x)
		(< 0 n))
	   (equal (nonneg-int-gcd (abs (+ x (* j n))) n)
		  (nonneg-int-gcd (abs x) n)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= (+ x (* j n)) 0)
				(<= x 0))
			   (equal
			    (nonneg-int-gcd (+ (- x)(- (* j n))) n)
			    (nonneg-int-gcd (- x) n)))
		  :hints (("Goal"
			   :cases ((< (+ x (* j n)) 0)))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= 0 (+ x (* j n)))
				(<= x 0))
			   (equal (nonneg-int-gcd (+ x (* j n)) n)
				  (nonneg-int-gcd (- x) n))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= (+ x (* j n)) 0)
				(<= 0 x))
			   (equal
			    (nonneg-int-gcd (+ (- x)(- (* j n))) n)
			    (nonneg-int-gcd x n))))
		 (:rewrite
		  :corollary
		  (implies (and (integerp j)
				(integerp n)
				(integerp x)
				(< 0 n)
				(<= 0 (+ x (* j n)))
				(<= 0 x))
			   (equal (nonneg-int-gcd (+ x (* j n)) n)
				  (nonneg-int-gcd x n)))))
  :hints (("Goal"
	 :in-theory (disable Nonneg-int-mod-abs-+-*
			     Nonneg-int-mod-abs)
	 :use (Nonneg-int-gcd-abs->=
	       Nonneg-int-gcd-abs-<=))))

(defthm
  Commutativity-of-nonneg-int-gcd
  (implies (and (integerp x)
		(integerp y)
		(>= x 0)
		(>= y 0))
	   (equal (nonneg-int-gcd x y)
		  (nonneg-int-gcd y x)))
  :hints (("Goal"
	   :cases ((< x y)(> x y)))))

(defthm
  Cross-product-factor
  (implies (and (equal (nonneg-int-gcd a b) 1)
		(equal (* a d)(* b c))
		(integerp a)
		(integerp b)
		(integerp c)
		(integerp d)
		(>= a 0)
		(>= b 0)
		(>= c 0)
		(>= d 0))
	   (and (equal (nonneg-int-mod c a) 0)
		(equal (nonneg-int-mod d b) 0)))
  :rule-classes nil
  :hints (("Goal"
	   :use ((:instance
		  Divisor-of-product-divides-factor
		  (x c)
		  (y b)
		  (z a))
		 (:instance
		  Divisor-of-product-divides-factor
		  (x d)
		  (y a)
		  (z b))))))

(defthm
  Nonneg-int-gcd-1-right
  (equal (nonneg-int-gcd x 1)
	 1))

(defthm
  Nonneg-int-gcd-1-left
  (implies (and (integerp x)
		(>= x 0))
 	   (equal (nonneg-int-gcd 1 x)
		  1))
  :rule-classes ((:rewrite
		  :corollary
		  (equal (nonneg-int-gcd 1 x)
			 1)))
  :hints (("Goal"
	   :in-theory (disable Nonneg-int-gcd-1-right )
	   :use Nonneg-int-gcd-1-right)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Numerator and Denominator ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  Nonneg-int-gcd-numerator-denominator
  (equal (nonneg-int-gcd (abs (numerator x))
			 (denominator x))
	 1)
  :rule-classes ((:rewrite
		  :corollary
		  (implies (>= (numerator x) 0)
			   (equal (nonneg-int-gcd (denominator x)
						  (numerator x))
				  1)))
		 (:rewrite
		  :corollary
		  (implies (<= (numerator x) 0)
			   (equal (nonneg-int-gcd (denominator x)
						  (-
						   (numerator x)))
				  1))))
  :hints (("Goal"
	   :use (:instance
		 lowest-terms
		 (n (nonneg-int-gcd (abs (numerator x))
				    (denominator x)))
		 (r (* (signum (numerator x))
		       (nonnegative-integer-quotient
			(abs (numerator x))
			(nonneg-int-gcd (abs (numerator x))
					(denominator x)))))
		 (q (nonnegative-integer-quotient
		     (denominator x)
		     (nonneg-int-gcd (abs (numerator x))
				     (denominator x))))))))

(defthm
  Lowest-terms-nonneg-int-mod
  (implies (and (integerp n1)
		(integerp n2)
		(integerp d1)
		(integerp d2)
		(> d1 0)
		(> d2 0)
		(equal (nonneg-int-gcd (abs n1) d1)
		       1)
		(equal (* (/ d1) n1)
		       (* (/ d2) n2)))
	   (and (equal (nonneg-int-mod d2 d1) 0)
		(equal (nonneg-int-mod (abs n2)(abs n1)) 0)))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (enable prefer-*-to-/)
	   :use (:instance
		 Cross-product-factor
		 (a (abs n1))
		 (b d1)
		 (c (abs n2))
		 (d d2)))))

(defthm
  Lowest-terms-<=
  (implies (and (integerp n1)
		(integerp n2)
		(integerp d1)
		(integerp d2)
		(> d1 0)
		(> d2 0)
		(equal (nonneg-int-gcd (abs n1) d1)
		       1)
		(equal (* (/ d1) n1)
		       (* (/ d2) n2)))
	   (and (<= d1 d2)
		(<= (abs n1)(abs n2))))
  :rule-classes nil
  :hints (("Goal"
	   :use Lowest-terms-nonneg-int-mod
	   :in-theory (enable prefer-*-to-/))))

(defthm
  LEAST-numerator-denominator-nonneg-int-mod
  (implies (and (integerp n)
		(integerp d)
		(> d 0))
	   (and (equal (nonneg-int-mod d
				       (denominator (* (/ d) n)))
		       0)
		(equal (nonneg-int-mod (abs n)
				       (abs
					(numerator (* (/ d) n))))
		       0)))
  :rule-classes ((:rewrite
		  :corollary
		  (implies (and (integerp n)
				(integerp d)
				(> d 0))
			   (equal
			    (nonneg-int-mod d
					    (denominator (* (/ d)
							    n)))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp n)
				(integerp d)
				(>= n 0)
				(> d 0))
			   (equal
			    (nonneg-int-mod n
					    (numerator (* (/ d)
							  n)))
			    0)))
		 (:rewrite
		  :corollary
		  (implies (and (integerp n)
				(integerp d)
				(<= n 0)
				(> d 0))
			   (equal
			    (nonneg-int-mod (- n)
					    (-
					     (numerator (* (/ d)
							   n))))
			    0))))
  :hints (("Goal"
	   :use (:instance
		 Lowest-terms-nonneg-int-mod
		 (n1 (numerator  (* (/ d) n)))
		 (d1 (denominator (* (/ d) n)))
		 (n2 n)
		 (d2 d)))))

;; Why is the curious hint needed for Subgoal 4?
;; What rules are interfering and how are these rules used?
;; It goes through on its own in the original book!

(defthm
  LEAST-numerator-denominator-<=
  (implies (and (integerp n)
		(integerp d)
		(> d 0))
	   (and (<= (denominator (* (/ d) n)) d)
		(<= (abs (numerator (* (/ d) n)))(abs n))))
  :rule-classes ((:linear
		  :corollary
		  (implies (and (integerp n)
				(integerp d)
				(> d 0))
			   (<= (denominator (* (/ d) n)) d)))
		 (:linear
		  :corollary
		  (implies (and (integerp n)
				(integerp d)
				(>= n 0)
				(> d 0))
			   (<= (numerator (* (/ d) n)) n)))
		 (:linear
		  :corollary
		  (implies (and (integerp n)
				(integerp d)
				(<= n 0)
				(> d 0))
			   (<= n (numerator (* (/ d) n))))))
  :hints (("Goal"
	   :in-theory (enable Divisor-<=))
	  ("Subgoal 4"
	   :in-theory (disable <-minus-minus
			       DIVISOR-<=
			       LEAST-NUMERATOR-DENOMINATOR-NONNEG-INT-MOD)
	   :use (DIVISOR-<= LEAST-NUMERATOR-DENOMINATOR-NONNEG-INT-MOD))
	  ("Subgoal 1"
	   :cases ((> n 0)))))

(defthm
  Unique-rationalp
  (implies (and (integerp n)
		(integerp d)
		(> d 0)
		(equal (nonneg-int-gcd (abs n) d)
		       1))
	   (and (equal (denominator (* (/ d) n)) d)
		(equal (numerator (* (/ d) n)) n)))
  :hints (("Goal"
	   :use (:instance
		 Lowest-terms-<=
		 (n1 n)
		 (d1 d)
		 (n2 (numerator (* (/ d) n)))
		 (d2 (denominator (* (/ d) n)))))))

