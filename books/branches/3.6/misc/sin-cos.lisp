; sin-cos.lisp  --  series approximations to SIN and COS
; Copyright (C) 1997  Computational Logic, Inc.

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

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    sin-cos.lisp
;;;
;;;    Unlimited series approximations to SIN and COS, plus functions for
;;;    creating SIN/COS tables.
;;;
;;;    Bishop Brock and Calvin Harrison
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

;;;****************************************************************************
;;;
;;;  Environment
;;;
;;;****************************************************************************

(in-package "ACL2")

(deflabel sin-cos
  :doc ":doc-section sin-cos
  SIN/COS approximations.
  ~/~/~/")


;;;****************************************************************************
;;;
;;;  Series approximations of sin/cos.
;;;
;;;****************************************************************************

(defun compute-series (x parity ex fact num itr ans)
  ":doc-section sin-cos
  Series approximation to SIN/COS.
  ~/~/

  This function is used to calculate the following Maclaurin series:

  To compute SIN:
 
  x - (x^3/3!) + (x^5/5!) - (x^7/7!) + ....

  To compute COS:
 
  1- (x^2/2!) + (x^4/4!) - (x^6/6!) + ....

  Arguments:

  x      -- x
  parity -- T to add the new term, NIL to subtract the new term.
  ex     -- x^num
  fact   -- num!
  itr    -- Number of iterations
  ans    -- Accumulated answer.
  ~/"
  (declare (xargs :guard (and (rationalp x)
			      (booleanp parity)
			      (rationalp ex)
			      (integerp fact)
			      (> fact 0)
			      (integerp num)
			      (>= num 0)
			      (integerp itr)
			      (>= itr 0)
			      (rationalp ans))))
  (if (zp itr)
      ans
    (compute-series x (not parity) (* x x ex) (* (+ 2 num) (+ 1 num) fact)
		    (+ 2 num) (1- itr) (if parity
					   (+ ans (/ ex fact))
					 (- ans (/ ex fact))))))

(local
 (defthm type-of-compute-series
  (implies
   (and (rationalp x)
	(rationalp ex)
	(integerp fact)
	(integerp num)
	(rationalp ans))
   (rationalp (compute-series x parity ex fact num itr ans)))
  :rule-classes :type-prescription))

(defun fast-compute-series
  (num-x^2 denom-x^2 num-x^n num-sum denom-sum n parity itr)
  ":doc-section sin-cos
  Efficient series approximation to SIN/COS.
  ~/~/

  This function is used to calculate the following Maclaurin series:

  To compute SIN:
 
  x - (x^3/3!) + (x^5/5!) - (x^7/7!) + ....

  To compute COS:
 
  1- (x^2/2!) + (x^4/4!) - (x^6/6!) + ....

  Rather than accumulating each term as shown, we instead compute the
  numerator and denominator of the sum, and return these two values.  This
  avoids the necessity of reducing each rational as it is accumulated.  On
  one set of examples this procudure was almost an order of magnitude faster
  than the simple summation given by COMPUTE-SERIES.

  Given x^2 as num-x^2/denom-x^2, and a partial sum num-sum/denom-sum,
  we compute the next partial sum as:
  
  num-sum       denom-x^2 (n + 1) (n + 2)      num-x^n num-x^2
  ---------  *  -------------------------   +  --------------------------
  denom-sum     denom-x^2 (n + 1) (n + 2)      denom-x^2 (n + 1) (n + 2)

  Again, the rationals are not actually computed, and instead we simply return
  the numerator and denominator of the answer.

  Arguments:

  num-x^2   -- (Numerator of x)^2.
  denom-x^2 -- (Denominator of x)^2.
  num-x^n   -- (num-x)^n
  num-sum   -- Numerator of partial sum.
  denom-sum -- Denominator of partial sum.
  n         -- n
  parity    -- T to add next term, NIL to subtract next term.
  itr       -- Number of iterations to perform.
  ~/"
  (declare (xargs :guard (and (integerp num-x^2)
			      (integerp denom-x^2)
			      (not (= denom-x^2 0))
			      (integerp num-x^n)
			      (integerp num-sum)
			      (integerp denom-sum)
			      (not (= denom-sum 0))
			      (integerp n)
			      (<= 0 n)
			      (booleanp parity)
			      (integerp itr)
			      (<= 0 itr))
                  :guard-hints (("Goal" :in-theory (disable DISTRIBUTIVITY)))))

  (if (zp itr)
      (mv num-sum denom-sum)
    (let*
      ((n+1*n+2          (* (+ n 1) (+ n 2)))
       (multiplier       (* denom-x^2 n+1*n+2))
       (new-denom-sum    (* denom-sum multiplier))
       (adjusted-num-sum (* num-sum multiplier))
       (new-num-x^n      (* num-x^n num-x^2))
       (new-num-sum      (if parity
			     (+ adjusted-num-sum new-num-x^n)
			   (- adjusted-num-sum new-num-x^n))))

      (fast-compute-series num-x^2 denom-x^2 new-num-x^n
			   new-num-sum new-denom-sum
			   (+ 2 n) (not parity) (1- itr)))))

(local
 (defthm type-of-fast-compute-series
  (implies
   (and (integerp num-x^2)
	(integerp denom-x^2)
	(not (= denom-x^2 0))
	(integerp num-x^n)
	(integerp num-sum)
	(integerp denom-sum)
	(not (= denom-sum 0))
	(integerp n)
	(<= 0 n)
	(booleanp parity)
	(integerp itr)
	(<= 0 itr))
   (and
    (integerp
     (mv-nth 0 (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				    n parity itr)))
    (integerp
     (mv-nth 1 (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				    n parity itr)))
    (not
     (equal
      (mv-nth 1
	      (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				   n parity itr))
      0))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies
     (and (integerp num-x^2)
	  (integerp denom-x^2)
	  (not (= denom-x^2 0))
	  (integerp num-x^n)
	  (integerp num-sum)
	  (integerp denom-sum)
	  (not (= denom-sum 0))
	  (integerp n)
	  (<= 0 n)
	  (booleanp parity)
	  (integerp itr)
	  (<= 0 itr))
     (integerp
      (mv-nth 0
	      (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				   n parity itr)))))
   (:type-prescription
    :corollary
    (implies
     (and (integerp num-x^2)
	  (integerp denom-x^2)
	  (not (= denom-x^2 0))
	  (integerp num-x^n)
	  (integerp num-sum)
	  (integerp denom-sum)
	  (not (= denom-sum 0))
	  (integerp n)
	  (<= 0 n)
	  (booleanp parity)
	  (integerp itr)
	  (<= 0 itr))
     (and
      (integerp
       (mv-nth 1
	       (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				    n parity itr)))
      (not
       (equal
	(mv-nth 1
		(fast-compute-series num-x^2 denom-x^2 num-x^n
				     num-sum denom-sum n parity itr))
	0))))))
       
  :hints
  (("Goal"
    :in-theory (disable distributivity))))) ;Too slow

(defun fast-compute-cos (x itr)
  ":doc-section sin-cos
   This function returns the numerator and denominator of a rational
   approximation to cos(x) (in radians) by itr iterations of
   FAST-COMPUTE-SERIES.  
  ~/~/~/"
  (declare (xargs :guard (and (rationalp x)
			      (integerp itr)
			      (>= itr 0))))
  (fast-compute-series (* (numerator x) (numerator x))
		       (* (denominator x) (denominator x))
		       1 1 1 0 nil itr))

(defun fast-compute-sin (x itr)
  ":doc-section sin-cos
   This function returns the numerator and denominator of a rational
   approximation to sin(x) (in radians) by itr iterations of
   FAST-COMPUTE-SERIES.  
  ~/~/~/"
  (declare (xargs :guard (and (rationalp x)
			      (integerp itr)
			      (>= itr 0))))
  (fast-compute-series (* (numerator x) (numerator x))
		       (* (denominator x) (denominator x))
		       (numerator x) (numerator x) (denominator x) 1 nil itr))

(defun truncated-integer-cos (x itr scale)
  ":doc-section sin-cos
  Integer approximation to cos(x) * scale. 
  ~/~/
  A rational approximation to cos(x), scaled up by scale, and then TRUNCATED
  to an integer.~/"
  (declare (xargs :guard (and (rationalp x)
			      (integerp itr)
			      (<= 0 itr)
			      (rationalp scale))
		  :guard-hints
		  (("Goal"
		    :in-theory (disable mv-nth)))))
  (mv-let (num denom) (fast-compute-cos x itr)
    (truncate (* num scale) denom)))

(defun truncated-integer-sin (x itr scale)
  ":doc-section sin-cos
  Integer approximation to sin(x) * scale.
  ~/~/
  A rational approximation to cos(x), scaled up by scale, and then TRUNCATED
  to an integer.~/"
  (declare (xargs :guard (and (rationalp x)
			      (integerp itr)
			      (<= 0 itr)
			      (rationalp scale))
		  :guard-hints
		  (("Goal"
		    :in-theory (disable mv-nth)))))
  (mv-let (num denom) (fast-compute-sin x itr)
    (truncate (* num scale) denom)))

(defun truncated-integer-sin/cos-table-fn (sin/cos i n pie itr scale)
  ":doc-section sin-cos
  Helper for SIN/COS-TABLE-FN
  ~/~/
  Note that this function has special code for 0, pi/2, pi, and (3/2)pi.
  The convergence of the series at these points is problematic in the
  context of truncation (vs. rounding).~/"
  (declare (xargs :guard (and (or (eq sin/cos :SIN) (eq sin/cos :COS))
			      (integerp i)
			      (<= 0 i)
			      (integerp n)
			      (<= 0 n)
			      (<= i n)
			      (rationalp pie)
			      (integerp itr)
			      (<= 0 itr)
			      (rationalp scale))
		  :measure (ifix (if (<= n i) 0 (- n i)))))
  (cond
   ((zp (- n i)) nil)
   (t (let ((i/n (/ i n)))
	(cons
	 (cons i (case sin/cos
		   (:sin
		    (case i/n
		      ((0 1/2) 0)	        ;0, pi
		      (1/4 (truncate scale 1))  ;pi/2
		      (3/4 (truncate scale -1)) ;(3/2)pi
		      (t
		       (truncated-integer-sin (* 2 pie i/n) itr scale))))
		   (t
		    (case i/n
		      (0 (truncate scale 1))    ;0
		      ((1/4 3/4) 0)	        ;pi/2, (3/2)pi
		      (1/2 (truncate scale -1))	;pi
		      (t 
		       (truncated-integer-cos (* 2 pie i/n) itr scale))))))
	 (truncated-integer-sin/cos-table-fn
	  sin/cos (1+ i) n pie itr scale))))))

(defun truncated-integer-sin/cos-table (sin/cos n pie itr scale)
  ":doc-section sin-cos
  Create a scaled, truncated integer sin/cos table from 0 to 2*pi.
  ~/~/
  This function creates a table of approximations to
  
  sin[cos]( (2 pi i)/n ) * scale, i = 0,...,n-1.

  The result is an alist ( ... (i . sin[cos](i) ) ... ).

  Arguments:

  sin/cos -- :SIN or :COS.
  n       -- Total number of table entries
  pie     -- An approximation to pi sufficiently accurate for the user's
             purposes.
  itr     -- Required number of iterations of FAST-COMPUTE-SIN[COS]
             sufficient for user's accuracy.
  scale   -- Scale factor.
  ~/"
  (declare (xargs :guard (and (or (eq sin/cos :SIN) (eq sin/cos :COS))
			      (integerp n)
			      (<= 0 n)
			      (rationalp pie)
			      (integerp itr)
			      (<= 0 itr)
			      (rationalp scale))))

  (truncated-integer-sin/cos-table-fn sin/cos 0 n pie itr scale))

