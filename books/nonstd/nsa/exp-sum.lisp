;;; This book develops the theorem that e^{x+y} = e^x * e^y.  This
;;; fundamental result is the key to proving the continuity of e^x.
;;; It is also the key towards proving the fundamental trigonometric
;;; identities, after we define sine and cosine in terms of e^x.

(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(include-book "arithmetic/binomial" :dir :system)

(include-book "inner-sums")
(include-book "exp")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; Consider the Taylor expansion of e^{x+y}.  It consists of the sum
;; of terms of the form (x+y)^i/i!  From the binomial theorem, we can
;; replace the term (x+y)^i by its binomial expansion.  The resulting
;; Taylor expansion of (x+y)^i is given below:

(defun binomial-over-factorial-unswapped (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (/ (sumlist (binomial-expansion x y 0 k))
	       (factorial k))
	    (binomial-over-factorial-unswapped
	     x y (1+ k) n))
    nil))

;; It's useful to expand (y+x)^i instead of (x+y)^i....

(defun binomial-over-factorial (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (/ (sumlist (binomial-expansion y x 0 k))
	       (factorial k))
	    (binomial-over-factorial x y (1+ k) n))
    nil))

(in-theory (disable n-expt-expt))

;; Now, we show that the list of numbers in that expansion is
;; non-empty (so long as we ask for more than 0 elements).

(defthm exp-x+y-binomial-unswapped-expansion-lemma
  (implies (and (integerp counter) (<= 0 counter))
	   (not (binomial-over-factorial-unswapped x y
						   counter (+ -1 counter))))
  :hints (("Goal"
	   :expand ((binomial-over-factorial-unswapped x y
						   counter (+ -1 counter))))))

;; And here is an important theorem.  The Taylor expansion of e^{x+y}
;; is in fact given by the binomial-factorial function defined above!

(defthm exp-x+y-binomial-unswapped-expansion
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(integerp counter)
		(<= 0 counter))
	   (equal (taylor-exp-list nterms
				   counter
				   (+ x y))
		  (binomial-over-factorial-unswapped
		   x
		   y
		   counter
		   (1- (+ nterms counter)))))
  :hints (("Goal"
	   :induct (taylor-exp-list  nterms counter (+ x y))
	   :in-theory (disable choose expt))))

;; We observe that the function binomial-over-factorial-unswapped is
;; the same as binomial-over-factorial, since the only difference is
;; one expands (x+y)^i and the other (y+x)^i.

(defthm binomial-unswapped-is-just-binomial
  (implies (and (integerp n) (<= 0 n))
	   (equal (binomial-over-factorial-unswapped x y k n)
		  (binomial-over-factorial x y k n)))
  :hints (("Subgoal *1/1"
	   :use (:instance binomial-sum-commutes (n k))
	   :in-theory (disable binomial-expansion))))

;; So we have that the Taylor expansion of e^{x+y} is the same as the
;; binomial-over-factorial expansion.

(defthm exp-x+y-binomial-expansion
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(integerp counter)
		(<= 0 counter))
	   (equal (taylor-exp-list  nterms counter (+ x y))
		  (binomial-over-factorial x y
					   counter
					   (1- (+ nterms counter)))))
  :hints (("Goal"
	   :cases ((and (equal nterms 0) (equal counter 0))))))

;; Now, what we have is a function that looks like (sum a_i) where the
;; a_i terms are binomial expansions -- i.e., a_i (sum a_{i,j}) for
;; some a_{i,j} function.  So, we define here the inner sum, which
;; adds up all the items in the binomial expansion (row)....

(defun binomial-over-factorial-inner-sum (x y j i)
  (declare (xargs :measure (nfix (1+ (- i j)))))
  (if (and (integerp i) (integerp j) (<= 0 j) (<= j i))
      (cons (/ (* (choose j i)
		  (expt x (- i j)) (expt y j))
	       (factorial i))
	    (binomial-over-factorial-inner-sum
	     x y (1+ j) i))
    nil))

;; ...and here is the outer sum, which adds up all the binomial
;; expansions (rows).  Note, this is a triangular sum.

(defun binomial-over-factorial-outer-sum (x y i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (sumlist
	     (binomial-over-factorial-inner-sum
	      x y 0 i))
	    (binomial-over-factorial-outer-sum
	     x y (1+ i) n))
    nil))

;; Here is a simple theorem.  Since binomial-over-factorial-inner-sum
;; is adding up a term that looks like (x+y)^i/i!, we can multiply
;; both sides by i! and end up with the binomial expansion of
;; (x+y)^i.

(defthm inner-sum-*-factorial
  (equal (* (factorial n)
	    (sumlist (binomial-over-factorial-inner-sum x y j n)))
	 (sumlist (binomial-expansion y x j n)))
  :hints (("Goal" :induct (binomial-over-factorial-inner-sum x y j n)
	   :in-theory (disable choose expt))))

;; Added for v2-6 by Matt K.:  Probably because of changes in term-order
;; (though I'm not sure), we need the following in order to get
;; binomial-over-factorial-=-expt-k-n-inner-sum-expansion-outer-sum proved.

(local (defthm left-right-cancellation-for-+
         (equal (equal (+ x y) (+ z x))
                (equal (fix y) (fix z)))))

;; It is clear that the binomial-over-factorial defined earlier is the
;; same as the version defined using row sums -- since the latter just
;; expands the terms in the binomial expansion.

(defthm binomial-over-factorial-=-expt-k-n-inner-sum-expansion-outer-sum
  (implies (and (integerp n) (<= 0 n))
	   (equal (binomial-over-factorial x y k n)
		  (binomial-over-factorial-outer-sum x y k n))))

;; A key lemma is that since (choose j i) = i!/(j! * (j-i)!), then
;; (choose j i) / i! = 1/(j! * (j-i)!)

(defthm choose-/-factorial
  (implies (and (integerp i) (integerp j) (<= 0 j) (<= j i))
	   (equal (/ (choose j i) (factorial i))
		  (/ 1 (* (factorial j) (factorial (- i j)))))))

;; So now, we redefine the binomial sum using the fact that the terms
;; in the binomial expansion of (x+y)^i/i! can be simplified using the
;; lemma above.

(local
 (defun inner-sum-1 (x y j i n)
   (declare (xargs :measure (nfix (1+ (- n j)))))
   (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
       (cons (/ (* (expt x (- i j)) (expt y j))
		(* (factorial j) (factorial (- i j))))
	     (inner-sum-1 x y (1+ j) i n))
     nil)))

;; Clearly, the two definitions of this binomial sum are equivalent.

(local
 (defthm binomial-over-factorial-is-inner-sum-1
   (equal (binomial-over-factorial-inner-sum x y j i)
	  (inner-sum-1 x y j i i))))

;; So now, we redefine the outer sum using the new version of the
;; inner binomial sum.

(local
 (defun outer-sum-1 (x y i n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (cons (sumlist (inner-sum-1 x y 0 i i))
	     (outer-sum-1 x y (1+ i) n))
     nil)))

;; And it's easy to see the two versions of the outer sum are equal to
;; each other.

(local
 (defthm binomial-over-factorial-is-outer-sum-1
   (equal (binomial-over-factorial-outer-sum x y i n)
	  (outer-sum-1 x y i n))))

;; Now, let's define the inner sums, but this time instead of
;; expanding all the (x+y)^j terms (i.e., going in rows), we look at
;; the terms involving y^j (i.e., going in columns).

(local
 (defun inner-sum-2 (x y i j n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (cons (/ (* (expt x (- i j)) (expt y j))
		(* (factorial j) (factorial (- i j))))
	     (inner-sum-2 x y (1+ i) j n))
     nil)))

;; And here is the sum of the terms by adding up all the columns.

(local
 (defun outer-sum-2 (x y j n)
   (declare (xargs :measure (nfix (1+ (- n j)))))
   (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
       (cons (sumlist (inner-sum-2 x y j j n))
	     (outer-sum-2 x y (1+ j) n))
     nil)))

;; What we've done, essentially, is to swap the two summations.
;; Before, we added up all the (x+y)^0/0! terms, then the (x+y)^1/1!
;; and so on.  Now, we add up all the terms involving y^0, then the
;; terms involving y^1, etc.  The sums are the same, because of the
;; generic theorem that justifies swapping outer and inner
;; summations.

(local
 (defthm outer-sum-1-is-outer-sum-2
   (implies (integerp n)
	    (equal (sumlist (outer-sum-1 x y 0 n))
		   (sumlist (outer-sum-2 x y 0 n))))
   :hints (("Goal"
	    :use (:functional-instance ok-to-swap-inner-outer-expansions-lt-m=n
				       (row-expansion-outer-lt-m=n
					(lambda (i n)
					  (outer-sum-1 x y i n)))
				       (row-expansion-inner
					(lambda (i j n)
					  (inner-sum-1 x y j i n)))
				       (binop
					(lambda (i j)
					  (/ (* (expt x (- i j))
						(expt y j))
					     (* (factorial j)
						(factorial (- i j))))))
				       (col-expansion-outer-lt-m=n
					(lambda (j n)
					  (outer-sum-2 x y j n)))
				       (col-expansion-inner
					(lambda (i j n)
					  (inner-sum-2 x y i j n))))))
   :rule-classes ((:rewrite :corollary
			    (equal (sumlist (outer-sum-1 x y 0 n))
				   (sumlist (outer-sum-2 x y 0 n)))))
   :otf-flg t))

;; Now, examining inner-sum-2, it is clear that the term y^j/j! is
;; being used everywhere, but it's not changed in the recursion.
;; I.e., it is a constant, so we can take it out of the summation.
;; Here is the sum of the remaining terms.

(local
 (defun inner-sum-3 (x i j n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (cons (/ (expt x (- i j)) (factorial (- i j)))
	     (inner-sum-3 x (1+ i) j n))
     nil)))

;; We can see that the sum of inner-sum-2 is the same as the sum of
;; inner-sum-3 after we multiply by the factored term y^j/j!

(local
 (defthm inner-sum-3-factors-inner-sum-2
   (equal (sumlist (inner-sum-2 x y i j n))
	  (* (sumlist (inner-sum-3 x i j n))
	     (/ (expt y j) (factorial j))))
   :hints (("Goal"
	    :by (:functional-instance factor-constant-from-expansion
				      (expansion-oneop-times-zeroop
				       (lambda (i n)
					 (inner-sum-2 x y i j n)))
				      (expansion-oneop
				       (lambda (i n)
					 (inner-sum-3 x i j n)))
				      (oneop
				       (lambda (i)
					 (/ (expt x (- i j))
					    (factorial (- i j)))))
				      (zeroop
				       (lambda ()
					 (/ (expt y j) (factorial j)))))))))

;; And here is the definition of the outer sum using the "factored"
;; version of the inner sum.


(local
 (defun outer-sum-3 (x y j n)
   (declare (xargs :measure (nfix (1+ (- n j)))))
   (if (and (integerp j) (integerp n) (<= 0 j) (<= j n))
       (cons (/ (* (sumlist (inner-sum-3 x j j n))
		   (expt y j))
                (factorial j))
             (outer-sum-3 x y (1+ j) n))
     nil)))

;; Clearly, it's equal to our last characterization of the sum.

(local
 (defthm outer-sum-3-is-outer-sum-2
   (equal (outer-sum-2 x y j n)
	  (outer-sum-3 x y j n))))

;; The terms in inner-sum-3 are of the form x^{i-j}/(i-j)!  Since j is
;; constant, it looks suspiciously like these terms are in fact some
;; Taylor expansion of e^x.  To relate i-j to the indices in the
;; Taylor expansion, we need an obvious cancellation.  If n<i, then
;; n-j<i-j.

(defthm obvious-cancellation
  (implies (< n i)
	   (< (- n j) (- i j)))
  :rule-classes (:rewrite
		 (:rewrite :corollary
			   (implies (< n i)
				    (< (+ (- j) n) (+ i (- j)))))))

;; So now, we have that inner-sum-3 is actually a retelling of just
;; the right segment of the Taylor expansion of e^x.

(local
 (defthm taylor-exp-list-is-inner-sum-3
   (implies (and (integerp i)
		 (integerp j) (<= 0 j) (<= j i)
		 (integerp n))
	    (equal (inner-sum-3 x i j n)
		   (taylor-exp-list (1+ (- n i))
				    (- i j)
				    x)))
   :hints (("Goal"
	    :in-theory (disable taylor-exp-list-split)))))

;; And next, we use the Taylor expansion of e^x to replace inner-sum-3
;; in our outer sum, getting a new definition of the Taylor expansion
;; of e^{x+y}.

(defun exp-x-y-k-n (x y i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (* (sumlist
		(taylor-exp-list (1+ (- n i)) 0 x))
	       (taylor-exp-term y i))
	    (exp-x-y-k-n x y (1+ i) n))
    nil))

;; And in fact, this definition is equal to our last definition, given
;; in outer-sum-3.

(local
 (defthm exp-x-y-k-n-is-outer-sum-3
   (equal (outer-sum-3 x y j n)
	  (exp-x-y-k-n x y j n))))

;; So now, we know that the Taylor expansion of e^{x+y} can be
;; computed using the function exp-x-y-k-n.

(defthm exp-k-n-sum-simplification
  (implies (and (integerp nterms) (<= 0 nterms))
	   (equal (sumlist
		   (taylor-exp-list nterms 0 (+ x y)))
		  (sumlist
		   (exp-x-y-k-n x y 0 (1- nterms)))))
  :hints (("Goal"
	   :cases ((equal nterms 0)))))

;; Next, we consider the function e^x * e^y, where we approximate both
;; exponents with a Taylor expansion.

(defun exp-x-*-exp-y-n (x y i n)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
      (cons (* (sumlist (taylor-exp-list (1+ n) 0 x))
	       (taylor-exp-term y i))
	    (exp-x-*-exp-y-n x y (1+ i) n))
    nil))


;; This key lemma shows that exp-x-*-exp-y-n really computes the
;; Taylor expansion of e^x types the Taylor expansion of e^y, starting
;; each expansion at the ith term....

(defthm exp-x-*-exp-y-n-=-exp-x-n-*-exp-y-n-lemma
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(integerp i)
		(<= i nterms))
	   (equal (* (sumlist (taylor-exp-list nterms 0 x))
		     (sumlist (taylor-exp-list (- nterms i) i y)))
		  (sumlist (exp-x-*-exp-y-n x y i (1- nterms))))))

(in-theory (disable exp-x-*-exp-y-n-=-exp-x-n-*-exp-y-n-lemma))

;; ...so in particular it's true if we look at *all* terms in the
;; expansion (starting at i=0).

(defthm exp-x-*-exp-y-n-=-exp-x-n-*-exp-y-n
  (implies (and (integerp nterms)
		(<= 0 nterms))
	   (equal (* (sumlist
		      (taylor-exp-list nterms 0 x))
		     (sumlist
		      (taylor-exp-list nterms 0 y)))
		  (sumlist
		   (exp-x-*-exp-y-n x y 0
				    (1- nterms)))))
  :hints (("Goal"
	   :use ((:instance exp-x-*-exp-y-n-=-exp-x-n-*-exp-y-n-lemma
			    (i 0))))))

;; So the question is, what is the difference between exp-x-y-k-n
;; (which computes a Taylor approximation of e^{x+y} and
;; exp-x-*-exp-y-n (which computes the product of the Taylor
;; approximations to e^x and e^y).  We see that it is equal to the
;; terms x^i/i! * y^j/j! where i+j > n.  If we think in terms of an
;; n-by-n matrix holding the a_{i,j} terms, then exp-x-y-k-n
;; corresponds to the diagonal and lower triangular elements, and
;; exp-x-*-exp-y-n is the entire matrix.  So the difference is the
;; upper triangular part of this matrix.  We define this difference
;; here.

(local
 (defun prod-sum-delta (x y i n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (cons (* (sumlist
		 (taylor-exp-list i (1+ (- n i)) x))
		(taylor-exp-term y i))
	     (prod-sum-delta x y (1+ i) n))
     nil)))

;; Next we want to show that prod-sum-delta really is the difference
;; between these two functions.

(local
 (encapsulate
  ()

  ;; So first, we show that the sum of the exp-x-y-k-n in the upper
  ;; triangular region is zero -- since all such terms are zero!

  (local
   (defthm lemma-1
     (implies (and (< (+ -1 nterms) i)
		   (integerp nterms)
		   (<= 0 nterms))
	      (equal (sumlist (exp-x-y-k-n x y i (+ -1 (- i) nterms)))
		     0))
     :hints (("Goal" :expand ((exp-x-y-k-n x y i (+ -1 (- i) nterms)))))))

  ;; Next, we split the sum of the terms of the Taylor expansion e^x
  ;; into the lower+diagonal and upper triangular region.

  (local
   (defthm lemma-2
     (implies (and (integerp n)
		   (integerp i)
		   (<= 0 i)
		   (<= i (+ 1 n)))
	      (equal (sumlist (taylor-exp-list (+ 1 n) 0 x))
		     (+ (sumlist (taylor-exp-list (+ 1 n (- i)) 0 x))
			(sumlist (taylor-exp-list i (+ 1 n (- i)) x)))))
     :hints (("Goal"
	      :use ((:instance taylor-exp-list-split
			       (n1 (+ 1 n (- i)))
			       (n2 i)
			       (counter 0))
		    (:instance sumlist-append
			       (x (taylor-exp-list (+ 1 (- i) n) 0 x))
			       (y (taylor-exp-list i (+ 1 (- i) n) x)))
		    )
	      :in-theory (disable taylor-exp-list-split taylor-exp-list
				  sumlist sumlist-append)
	      :do-not-induct t))))


  ;; We show that the sum of the terms in e^x minus the sum of the
  ;; upper-triangular region is the sum of the lower+diagonal region.

  (local
   (defthm lemma-3
     (implies (and (integerp n)
		   (integerp i)
		   (<= 0 i)
		   (<= i (+ 1 n)))
	      (equal (+ (sumlist (taylor-exp-list (+ 1 n) 0 x))
			(- (sumlist (taylor-exp-list (+ 1 n (- i)) 0 x))))
		     (sumlist (taylor-exp-list i (+ 1 n (- i)) x))))
     :instructions
     (:promote (:dv 1)
	       (:dv 1)
	       (:rewrite lemma-2)
	       :up :s :up :s :s :s :s)))

  ;; Carrying out this argument over all the y^j/j! shows that the
  ;; difference between exp-x-*-exp-y-n (the product of the Taylor
  ;; approximations) and exp-x-y-k-n (the Taylor approximation of the
  ;; product) is equal to prod-sum-delta.

  (defthm expt-x-*-expt-y-n---exp-x-y-k-n-=-prod-sum-delta-lemma
    (equal (- (sumlist (exp-x-*-exp-y-n x y i n))
	      (sumlist (exp-x-y-k-n x y i n)))
	   (sumlist (prod-sum-delta x y i n)))
    :hints (("Goal"
	     :induct (prod-sum-delta x y i n)
	     :in-theory (disable taylor-exp-list
				 taylor-exp-term))
	    ("Subgoal *1/1'5'"
	     :use ((:instance taylor-exp-list-split
			      (n1 (+ (- I) N))
			      (n2 i)
			      (counter 1)))
	     :in-theory (disable taylor-exp-list-split taylor-exp-list taylor-exp-term
				 sumlist))))

  ;; We specialize the result above for when we're looking at the
  ;; entire matrix.

  (defthm expt-x-*-expt-y-n---exp-x-y-k-n-=-prod-sum-delta
    (implies (and (integerp nterms)
		  (<= 0 nterms))
	     (equal (- (* (sumlist (taylor-exp-list nterms 0 x))
			  (sumlist (taylor-exp-list nterms 0 y)))
		       (sumlist (taylor-exp-list nterms 0 (+ x y))))
		    (sumlist (prod-sum-delta x y 0 (1- nterms)))))
    :hints (("Goal"
	     :in-theory '(expt-x-*-expt-y-n---exp-x-y-k-n-=-prod-sum-delta-lemma
			  exp-x-*-exp-y-n-=-exp-x-n-*-exp-y-n
			  exp-k-n-sum-simplification)
	     :do-not-induct t)))
  ))

;; Next, we define the notion of multiplying all elements of a list by
;; a number.

(local
 (defun mult-scalar (x s)
   (if (consp x)
       (cons (* (car x) s)
	     (mult-scalar (cdr x) s))
     nil)))

;; This number can be factored out a sumlist....

(local
 (defthm sumlist-mult-scalar
   (equal (sumlist (mult-scalar s x))
	  (* (sumlist s) x))))

;; ...and its norm can be factored out of a sumlist-norm.

(local
 (defthm sumlist-norm-mult-scalar
   (equal (sumlist-norm (mult-scalar s x))
	  (* (sumlist-norm s) (norm x)))))

;; So now we give a slightly different definition of prod-sum-delta,
;; where the y^j/j! terms are pushed into the x^i/i! instead of being
;; factored outside the summation.

(local
 (defun prod-sum-delta-2 (x y i n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (append (mult-scalar
		(taylor-exp-list i (1+ (- n i)) x)
		(taylor-exp-term y i))
	       (prod-sum-delta-2 x y (1+ i) n))
     nil)))

;; Naturally, the two definitions are equal.

(local
 (defthm prod-sum-delta-=-prod-sum-delta-2
   (equal (sumlist (prod-sum-delta x y i n))
	  (sumlist (prod-sum-delta-2 x y i n)))))

;; Next, we perform the same procedure on exp-x-*-exp-y-n, resulting
;; in exp-x-*-exp-y-n-2.

(local
 (defun exp-x-*-exp-y-n-2 (x y i n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (append (mult-scalar (taylor-exp-list (1+ n) 0 x)
			    (taylor-exp-term y i))
	       (exp-x-*-exp-y-n-2 x y (1+ i) n))
     nil)))

;; Again, these two functions are equal.

(local
 (defthm exp-x-*-exp-y-n-=-exp-x-*-exp-y-n-2
   (equal (sumlist (exp-x-*-exp-y-n x y i n))
	  (sumlist (exp-x-*-exp-y-n-2 x y i n)))))

;; Now, we define a new expansion of the Taylor expansion, but we
;; specify a "lower limit".  All the x^i/i! terms where i is less than
;; this lower limit are defined as 0.  Thus, this function returns
;; lists of the form (0 0 0 ... 0 x^i/i! x^{i+1}/(i+1)! ... x^n/n!)

(local
 (defun taylor-exp-list-3 (nterms counter llimit x)
   (if (or (zp nterms)
	   (not (integerp counter))
	   (< counter 0))
       nil
     (cons (if (< counter llimit)
	       0
	     (taylor-exp-term x counter))
	   (taylor-exp-list-3 (1- nterms)
			      (1+ counter)
			      llimit
			      x)))))

;; Now, if we're adding up taylor-exp-list-3 elements starting at some
;; index less than the lower limit, then we know we can just skip that
;; first element, since it'll be zero.

(local
 (encapsulate
  ()

  (local
   (defthm lemma-1
     (implies (and (integerp nterms)
		   (integerp counter)
		   (<= 0 counter)
		   (< counter llimit))
	      (equal (sumlist (taylor-exp-list-3 nterms counter llimit x))
		     (sumlist (taylor-exp-list-3 (1- nterms) (1+ counter) llimit x))))))

  ;; So by induction, we can skip the first k elements, as long as we
  ;; don't cross the lower limit boundary.

  (local (in-theory (enable (:induction factorial))))
  (local
   (defthm lemma-2
     (implies (and (integerp nterms)
		   (integerp counter)
		   (<= 0 counter)
		   (integerp k)
		   (<= 0 k)
		   (<= (+ counter k) llimit))
	      (equal (sumlist (taylor-exp-list-3 nterms counter llimit x))
		     (sumlist (taylor-exp-list-3 (- nterms k) (+ counter k) llimit x))))
     :hints (("Goal" :induct (factorial k)))))

  ;; And here is the best result along these lines, where we can
  ;; actually get the largest k that won't cross the boundary.

  (local
   (defthm lemma-3
     (implies (and (integerp nterms)
		   (integerp counter)
		   (<= 0 counter)
		   (integerp llimit)
		   (<= counter llimit))
	      (equal (sumlist (taylor-exp-list-3 nterms counter llimit x))
		     (sumlist (taylor-exp-list-3 (- nterms
						    (- llimit counter))
						 llimit llimit x))))
     :hints (("Goal" :use ((:instance lemma-2 (k (- llimit counter))))
	      :in-theory (disable lemma-1 lemma-2 sumlist
				  taylor-exp-list-3)
	      :do-not-induct t))))

  ;; On the other hand, if we start beyond the lower limit, then
  ;; taylor-exp-list-3 is just the same as taylor-exp-list

  (local
   (defthm lemma-4
     (implies (and (integerp nterms)
		   (integerp counter)
		   (<= 0 counter)
		   (<= llimit counter))
	      (equal (sumlist (taylor-exp-list-3 nterms counter llimit x))
		     (sumlist (taylor-exp-list nterms counter x))))))

  ;; Together, these lemmas show that sum of taylor-exp-list starting
  ;; at some index is the same as the sum of the taylor-exp-list-3
  ;; terms starting at 0, and using the old index as the "lower limit".

  (defthm taylor-exp-list-=-taylor-exp-list-3
      (implies (and (integerp counter)
                    (integerp nterms)
                    (<= 0 counter)
                    (<= 0 nterms))
               (equal (sumlist
                       (taylor-exp-list nterms counter x))
                      (sumlist
                       (taylor-exp-list-3 (+ nterms counter)
                                          0
                                          counter
                                          x)))))
  ))

;; OK, so now we can replace taylor-exp-list with taylor-exp-list-3 in
;; to define prod-sum-delta-3.  Notice that this definition always
;; returns a list of n elements!  Which means we are dealing with
;; square matrices now.

(local
 (defun prod-sum-delta-3 (x y i n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (append (mult-scalar
		(taylor-exp-list-3 (1+ n)
				   0
				   (1+ (- n i))
				   x)
		(taylor-exp-term y i))
	       (prod-sum-delta-3 x y (1+ i) n))
     nil)))

;; Clearly, prod-sum-delta-3 is just the same as the original
;; prod-sum-delta.

(local
 (defthm prod-sum-delta-=-prod-sum-delta-3
   (equal (sumlist (prod-sum-delta x y i n))
	  (sumlist (prod-sum-delta-3 x y i n)))))

;; Now, we think of a different Taylor approximation of e^x * e^y.
;; The trick is to find the Taylor approximation of e^x and e^y using
;; only n/2 elements!  Thinking of that n-by-n matrix again, what we
;; have are elements in the lower n/2-by-n/2 square -- all other
;; elements are zero.  What this function computes is just the
;; opposite.  The terms in that lower n/2-by-n/2 square are all zero,
;; and the other terms have the same values as the the Taylor
;; approximation of e^x*e^y up to n elements.  What we see is that the
;; terms in exp-x-*-exp-y-n-3 add up to the difference between the
;; approximation using n elements and the one using n/2 elements.  For
;; n large enough, this difference is i-small.  Moreover, this
;; difference is clearly bigger than prod-sum-delta-3, so
;; prod-sum-delta-3 is also i-small!

(local
 (defun exp-x-*-exp-y-n-3 (x y i n)
   (declare (xargs :measure (nfix (1+ (- n i)))))
   (if (and (integerp i) (integerp n) (<= 0 i) (<= i n))
       (append (mult-scalar
		(if (< i (next-integer (/ n 2)))
		    (taylor-exp-list-3
		     (1+ n)
		     0
		     (next-integer (/ n 2))
		     x)
		  (taylor-exp-list-3 (1+ n) 0 0 x))
		(taylor-exp-term y i))
	       (exp-x-*-exp-y-n-3 x y (1+ i) n))
     nil)))

;; So now, we reason about Taylor approximations up to m, as opposed to
;; Taylor approximations up to n.  We start with the notion of the
;; prefix of a list.

(defun list-prefix-p (l1 l2)
  (if (consp l1)
      (and (consp l2)
	   (equal (car l1) (car l2))
	   (list-prefix-p (cdr l1) (cdr l2)))
    t))

;; This function removes a prefix from a list -- OK, actually it
;; doesn't check that it's *really* removing a prefix, it just removes
;; the first len(l1) elements from l2!

(defun remove-prefix (l1 l2)
  (if (consp l1)
      (remove-prefix (cdr l1) (cdr l2))
    l2))

;; Here's a silly theorem.  If I remove any prefix from the empty
;; list, I get back the empty list.

(defthm remove-prefix-nil
  (equal (remove-prefix x nil) nil))

;; The important theorem here is that the sumlist-norm of removing the
;; prefix l1 from the list l2 is the sumlist-norm of l2 minus the
;; sumlist-norm of l1.

(defthm sumlist-norm-list-prefix
  (implies (list-prefix-p l1 l2)
	   (equal (sumlist-norm (remove-prefix l1 l2))
		  (- (sumlist-norm l2)
		     (sumlist-norm l1)))))

;; SO now, if m<=n we get that the Taylor approximation of e^x using m
;; terms is a prefix of the approximation using n terms.

(defthm prefix-taylor-exp-list
  (implies (and (integerp n) (<= 0 n) (<= m n))
	   (list-prefix-p (taylor-exp-list m i x)
			  (taylor-exp-list n i x))))

;; So now we can see that the sum of the taylor-exp-list-3 with a
;; lower limit of m is equal to the regular taylor-exp-list using all
;; n elements minus the taylor-exp-list of the first m elements.

(local
 (encapsulate
  ()

  ;; First, we show that the sumlist-norm of removing the prefix
  ;; Taylor expansion of m elements from the Taylor expansion of n
  ;; elements is just the difference of the sumlist-norm of the n
  ;; elements and the sumlist-norm of the m element approximation.

  (local
   (defthm lemma-1
     (implies (and (integerp n) (<= 0 n) (<= m n))
	      (equal (sumlist-norm (remove-prefix (taylor-exp-list m i x)
						  (taylor-exp-list n i x)))
		     (- (sumlist-norm (taylor-exp-list n i x))
			(sumlist-norm (taylor-exp-list m i x)))))))


  ;; A simple lemma checks the "lower limit" boundary condition of
  ;; taylor-exp-list-3 -- in fact, the function returns only zeros
  ;; beyond that point.

  (local
   (defthm lemma-2
     (implies (and (integerp n) (<= 0 n)
		   (integerp i) (<= 0 i)
		   (integerp m) (<= 0 m) (<= (+ n i) m))
	      (equal (sumlist-norm (taylor-exp-list-3 n i m x)) 0))))

  ;; If we use a lower limit of 0, then taylor-exp-list-3 is the same
  ;; thing as taylor-exp-list.

  (local
   (defthm lemma-3
     (implies (and (integerp n) (<= 0 n)
		   (integerp i) (<= 0 i))
	      (equal (taylor-exp-list-3 n i 0 x)
		     (taylor-exp-list n i x)))))

  ;; Otherwise, the taylor-exp-list-3 using a lower limit of m can be
  ;; computed by removing the first m elements of the Taylor expansion

  (local
   (defthm lemma-4
     (implies (and (integerp n) (<= 0 n)
		   (integerp i) (<= 0 i)
		   (integerp m) (<= 0 m))
	      (equal (sumlist-norm (taylor-exp-list-3 n i m x))
		     (sumlist-norm (remove-prefix (taylor-exp-list (- m i) i x)
						  (taylor-exp-list n i x)))))
     :hints (("Subgoal *1/6.1''"
	      :expand ((taylor-exp-list (+ -1 (- i) m) (+ 1 i) x))))))


  ;; And so the sumlist-norm of the taylor-exp-list-3 can be computed
  ;; as the difference of the sumlist-norm of the taylor-exp-list of
  ;; all n elements and the first m elements.

  (defthm sumlist-norm-taylor-exp-list
    (implies (and (integerp m) (<= 0 m)
		  (integerp i) (<= 0 i)
		  (integerp n) (<= m n))
	     (equal (sumlist-norm
		     (taylor-exp-list-3 n i m x))
		    (- (sumlist-norm
			(taylor-exp-list n i x))
		       (sumlist-norm
			(taylor-exp-list (- m i)
					 i
					 x))))))
  ))

(local (in-theory (disable taylor-exp-term taylor-exp-list)))

;; So now we apply that theorem to the exp-x-*-exp-y-n-2 function.

(local
 (encapsulate
  ()

  ;; First of all, we get a boundary condition for exp-x-*-exp-y-n-2
  ;; (which is the simple product of the Taylor approximations).

  (local
   (defthm lemma-1
     (implies (and (< n i)
		   (integerp i)
		   (integerp n)
		   (<= 0 i)
		   (<= 2 n))
	      (equal (exp-x-*-exp-y-n-2 x y i (+ -1 (next-integer (* 1/2 n))))
		     nil))))

  ;; Next, we show that the Taylor approximation of length 1 is equal
  ;; to '(1) -- since x^0/0! = 1....

  (local
   (defthm lemma-2
     (equal (taylor-exp-list 1 0 x) (list 1))
     :hints (("Goal" :in-theory (enable taylor-exp-list taylor-exp-term)))))

  ;; And here is another boundary condition for exp-x-*-exp-y-n-2.

  (local
   (defthm lemma-3
     (implies (< n i)
	      (equal (sumlist-norm (exp-x-*-exp-y-n-2 x y i n))
		     0))))

  ;; Yet another boundary condition!

  (local
   (defthm lemma-4
     (equal (sumlist-norm (taylor-exp-list -1 i x)) 0)
     :hints (("Goal" :expand (taylor-exp-list -1 i x)))))

  ;; ...and another one....

  (local
   (defthm lemma-5
     (equal (taylor-exp-term x 0) 1)
     :hints (("Goal" :expand (taylor-exp-term x 0)))))

  ;; And finally, we have that sumlist-norm of exp-x-*-exp-y-n-3 is
  ;; equal to the difference of the n-element taylor approximation and
  ;; the n/2 element approximation.

  (defthm sumlist-norm-exp-x-*-exp-y-n-3
    (implies (and (integerp i) (integerp n)
		  (<= 0 i) (<= 2 n))
	     (equal (sumlist-norm
		     (exp-x-*-exp-y-n-3 x y i n))
		    (- (sumlist-norm
			(exp-x-*-exp-y-n-2 x y i n))
		       (sumlist-norm
			(exp-x-*-exp-y-n-2
			 x
			 y
			 i
			 (1- (next-integer (/ n 2))))))))
    :hints (("Goal"
	     :induct (exp-x-*-exp-y-n-3 x y i n))
	    ("Subgoal *1/1.2.1'5'"
	     :expand ((taylor-exp-list (next-integer (* 1/2 n)) 0 x)))))
  ))

;; And now, a crucial theorem.  The sumlist-norm of exp-x-*-exp-y-n-2
;; (which expands the product of the approximations to e^x and e^y) is
;; the same as the product of the sumlist-norms of e^x and e^y.

(local
 (encapsulate
  ()

  ;; First, we establish (again) that if the Taylor expansion has only
  ;; one element, it must be equal to 1.

  (local
   (defthm lemma-2
     (equal (taylor-exp-list 1 0 x) (list 1))
     :hints (("Goal" :in-theory (enable taylor-exp-list taylor-exp-term)))))

  ;; And now, a boundary condition, when the expansion is negative
  ;; (i.e., a_0 ... a_{-3})!

  (local
   (defthm lemma-4
     (implies (<= n 0)
	      (equal (sumlist-norm (taylor-exp-list n i x)) 0))
     :hints (("Goal" :expand (taylor-exp-list n i x)))))


  ;; And then the main theorem follows.

  (defthm sumlist-norm-exp-x-*-exp-y-n-2
    (implies (and (integerp i) (integerp n)
		  (<= 0 i) (<= 0 n))
	     (equal (sumlist-norm
		     (exp-x-*-exp-y-n-2 x y i n))
		    (* (sumlist-norm
			(taylor-exp-list (1+ n) 0 x))
		       (sumlist-norm
			(taylor-exp-list (- (1+ n) i)
					 i
					 y)))))
    :instructions ((:induct (exp-x-*-exp-y-n-2 x y i n))
		   :prove :promote (:claim (<= i n))
		   (:drop 1)
		   (:demote 1)
		   (:dv 1 1)
		   (:= t)
		   :up :s :top :promote (:dv 1 1)
		   :x :up :x (:dv 2)
		   := :top (:dv 2 2 1)
		   :x (:dv 1)
		   (:= t)
		   :up
		   :s :up :x :up (:rewrite distributivity)
		   (:dv 1 1)
		   :x :up :s :top :s))
  ))

;; Now, we know that if we look at the Taylor approximation for x^n
;; using M terms and then using N terms and both M and N are i-large,
;; than the results are i-close to each other.  We restate that by
;; showing that the difference in the approximations is i-small.

(defthm exp-convergent-norm-using-small
  (implies (and (i-limited x)
		(integerp nterms1)
		(<= 0 nterms1)
		(i-large nterms1)
		(integerp nterms2)
		(<= 0 nterms2)
		(i-large nterms2))
	   (i-small (- (sumlist-norm (taylor-exp-list nterms1 0 x))
		       (sumlist-norm (taylor-exp-list nterms2 0 x)))))
   :hints (("Goal"
	    :use ((:instance exp-convergent-norm))
	    :in-theory (enable-disable (i-close) (exp-convergent-norm)))))

;; So now, we wish to use that to prove that the sumlist-norm of
;; exp-x-*-exp-y-n-3 is i-small.

(local
 (encapsulate
  ()

  ;; First, we have some non-standard analysis algebra, namely if x
  ;; and y are limited and x, x' are close, then x*y and x'*y are
  ;; close.

  (local
   (defthm lemma-1
     (implies (and (i-limited x)
		   (i-limited y)
		   (i-close x x2))
	      (i-close (* x y) (* x2 y)))
     :hints (("Goal" :use ((:instance distributivity
				      (x y)
				      (y x)
				      (z (- x2))))
	      :in-theory (enable-disable (i-close i-small) (distributivity))))))

  ;; The same theorem, but this time with x*y and x'*y' close.

  (local
   (defthm lemma-2
     (implies (and (i-limited x)
		   (i-limited y)
		   (i-close x x2)
		   (i-close y y2))
	      (i-close (* x y) (* x2 y2)))
     :hints (("Goal"
	      :use ((:instance i-close-transitive
			       (x (* x y))
			       (y (* x2 y))
			       (z (* x2 y2)))
		    (:instance lemma-1)
		    (:instance lemma-1 (y x2) (x y) (x2 y2))
		    (:instance i-close-limited (x x) (y x2)))
	      :in-theory (disable i-close-transitive i-close-limited lemma-1)))))

  ;; So now, we have a strong theorem, namely that for any i-large N,
  ;; the Taylor expansion of e^x is limited.  (Previously, we only
  ;; needed this result up to i-large-integer.)

  (defthm taylor-exp-list-norm-limited-strong
    (implies (and (i-limited x)
		  (i-large n))
	     (i-limited (sumlist-norm (taylor-exp-list n 0 x))))
    :hints (("Goal"
	     :cases ((and (integerp n) (<= 0 n))))
	    ("Subgoal 2"
	     :expand (taylor-exp-list n 0 x))
	    ("Subgoal 1"
	     :use ((:instance taylor-exp-list-norm-limited)
		   (:instance exp-convergent-norm
			      (nterms1 (i-large-integer))
			      (nterms2 n))
		   (:instance i-close-limited
			      (x (sumlist-norm (taylor-exp-list (i-large-integer)
								0
								x)))
			      (y (sumlist-norm (taylor-exp-list n 0 x)))))
	     :in-theory (disable taylor-exp-list-norm-limited
				 exp-convergent-norm
				 i-close-limited))))

  ;; For that matter, the approximation up to N+1 is also limited....

  (local
   (defthm taylor-exp-list-norm-limited-strong-1+n
     (implies (and (i-limited x)
		   (i-large n))
	      (i-limited (sumlist-norm (taylor-exp-list (+ 1 n) 0 x))))))

  ;; Now, if N/2 is limited, so is N.

  (local
   (defthm limited-n/2
     (implies (and (acl2-numberp n)
		   (i-limited (* 1/2 n)))
	      (i-limited n))
     :hints (("Goal"
	      :use ((:instance i-limited-times
			       (x (* 1/2 n))
			       (y 2)))
	      :in-theory (disable i-limited-times)))))

  ;; So if N is large, so is N/2.

  (local
   (defthm large-n/2
     (implies (i-large n)
	      (i-large (* 1/2 n)))
     :hints (("Goal"
	      :use ((:instance limited*large->large
			       (x 1/2)
			       (y n)))
	      :in-theory (enable-disable (i-small i-large)
					 (limited*large->large))))))

  ;; And so if N is large, so is next-integer(N/2).

  (local
   (defthm large-next-integer-n/2
     (implies (and (i-large n)
		   (realp n)
		   (<= 0 n))
	      (i-large (next-integer (* 1/2 n))))
     :hints (("Goal"
	      :use ((:instance large-if->-large
			       (x (* 1/2 n))
			       (y (next-integer (* 1/2 n)))))
	      :in-theory (disable large-if->-large)))))

  ;; And so the Taylor approximation up to next-integer(N/2) is limited.

  (local
   (defthm taylor-exp-list-norm-limited-strong-n/2
     (implies (and (i-limited x)
		   (realp n)
		   (i-large n)
		   (<= 0 n))
	      (i-limited (sumlist-norm (taylor-exp-list (NEXT-INTEGER (* 1/2 N)) 0 x))))))

  ;; So finally, we get the result we want, namely that for limited x
  ;; and y and large n, the exp-x-*-exp-y-n-3 of x, y, and n is
  ;; i-small.  Later we will show exp-x-*-exp-y-n-3 is a bound on
  ;; prod-sum-delta, and so prod-sum-delta is i-small.

  (defthm sumlist-norm-exp-x-*-exp-y-n-3-small
    (implies (and (integerp n) (<= 2 n)
		  (i-limited x) (i-limited y) (i-large n))
	     (i-small (sumlist-norm
		       (exp-x-*-exp-y-n-3 x y 0 n))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-2
			      (x (sumlist-norm (taylor-exp-list (+ 1 n) 0 x)))
			      (x2 (sumlist-norm (taylor-exp-list (next-integer (* 1/2 n))
								 0 x)))
			      (y (sumlist-norm (taylor-exp-list (+ 1 n) 0 y)))
			      (y2 (sumlist-norm (taylor-exp-list (next-integer (* 1/2 n))
								 0 y)))))
	     :in-theory (disable taylor-exp-list-split lemma-1 lemma-2
				 exp-x-*-exp-y-n-3
				 exp-x-*-exp-y-n-2))
	    ("Goal'''"
	     :in-theory (enable i-close))))
  ))

;; An induction hint to cdr on two lists simultaneously.

(local
 (defun induction-hint-on-x1-y1 (x1 y1)
   (if (endp x1)
       y1
     (induction-hint-on-x1-y1 (cdr x1) (cdr y1)))))

;; Here's a useful theorem.  If x1 is a sequence bounded by y1 and x2
;; is a sequence bounded by y2, then append(x1,x2) is bounded by
;; append(y1,y2) -- as long as x1 and x2 have the same length!

(defthm seq-norm-<=-append
  (implies (and (seq-norm-<= x1 y1)
		(seq-norm-<= x2 y2)
		(equal (len x1) (len y1)))
	   (seq-norm-<= (append x1 x2)
			(append y1 y2)))
  :hints (("Goal"
	   :induct (induction-hint-on-x1-y1 x1 y1))))

;; Another useful lemma, multiplying two sequences by the same scalar
;; does not change any bounded properties of the sequences.

(local
 (defthm seq-norm-<=-mult-scalar
   (implies (seq-norm-<= x y)
	    (seq-norm-<= (mult-scalar x s)
			 (mult-scalar y s)))))

;; Moreover, after multiplying a list by a scalar, the length is
;; unchanged.

(local
 (defthm len-mult-scalar
   (equal (len (mult-scalar x s)) (len x))))

;; A simple theorem is that the taylor-exp-list-3 using l2 as a lower
;; limit is bounded by the taylor-exp-list-3 using l1 as a lower limit
;; if l1<=l2.  The reason is that the l2-sequence disallows a few more
;; terms than the l1-sequence and replaces them by zeros.

(local
 (defthm seq-norm-<=-taylor-exp-list-3
   (implies (<= llimit1 llimit2)
	    (seq-norm-<= (taylor-exp-list-3 n i llimit2 x)
			 (taylor-exp-list-3 n i llimit1 x)))))

;; Here is a simple characterization of the length of a Taylor
;; approximation.

(local
 (defthm len-taylor-exp-list-3
   (implies (and (integerp n) (<= 0 n)
		 (integerp i) (<= 0 i))
	    (equal (len (taylor-exp-list-3 n i l x)) n))))

;; So now, we have that prod-sum-delta-3 is bounded above by
;; exp-x-*-exp-y-n-3, since the former has the same values as the
;; latter (if in the upper triangle) or zero (if not on the upper
;; triangle).

(local
 (defthm prod-sum-delta-3-seq-<=-exp-x-*-exp-y-n-3
   (implies (<= 2 n)
	    (seq-norm-<= (prod-sum-delta-3 x y i n)
			 (exp-x-*-exp-y-n-3 x y i n)))
   :hints (("Goal"
	    :in-theory (disable taylor-exp-list-3
				taylor-exp-term))
	   ("Subgoal *1/1.2"
	    :use ((:instance seq-norm-<=-append
			     (x1 (mult-scalar (taylor-exp-list-3 (+ 1 n)
								 0 (+ 1 (- i) n)
								 x)
					      (taylor-exp-term y i)))
			     (x2 (prod-sum-delta-3 x y (+ 1 i) n))
			     (y1 (mult-scalar (taylor-exp-list-3 (+ 1 n)
								 0 (next-integer (* 1/2 n))
								 x)
					      (taylor-exp-term y i)))
			     (y2 (exp-x-*-exp-y-n-3 x y (+ 1 i) n)))
		  (:instance seq-norm-<=-mult-scalar
			     (x (taylor-exp-list-3 (+ 1 n)
						   0 (+ 1 (- i) n)
						   x))
			     (y (taylor-exp-list-3 (+ 1 n)
						   0 (next-integer (* 1/2 n))
						   x))
			     (s (taylor-exp-term y i)))
		  (:instance seq-norm-<=-taylor-exp-list-3
			     (n (+ 1 n))
			     (i 0)
			     (llimit1 (next-integer (* 1/2 n)))
			     (llimit2 (+ 1 (- i) n))))
	    :in-theory (disable taylor-exp-list-3
				taylor-exp-term
				seq-norm-<=-append
				seq-norm-<=-mult-scalar
				seq-norm-<=-taylor-exp-list-3)))))

;; And so, the sumlist-norm of the prod-sum-delta-3 must be i-small....

(local
 (defthm prod-sum-norm-delta-3-small
     (implies (and (integerp n) (<= 2 n)
		   (i-limited x) (i-limited y) (i-large n))
	      (i-small (sumlist-norm (prod-sum-delta-3 x y 0 n))))
     :hints (("Goal" :do-not-induct t
	      :use ((:instance comparison-test-small
			       (x (prod-sum-delta-3 x y 0 n))
			       (y (exp-x-*-exp-y-n-3 x y 0 n)))
		    (:instance prod-sum-delta-3-seq-<=-exp-x-*-exp-y-n-3 (i 0))
		    (:instance sumlist-norm-exp-x-*-exp-y-n-3-small))
	      :in-theory nil))))

;; ...and so the sum of prod-sum-delta-3 is small...

(local
 (defthm prod-sum-delta-3-small
     (implies (and (integerp n) (<= 2 n)
		   (i-limited x) (i-limited y) (i-large n))
	      (i-small (sumlist (prod-sum-delta-3 x y 0 n))))))

;; ...which in turn means the sum of prod-sum-delta is small.

(local
 (defthm prod-sum-delta-small
     (implies (and (integerp n) (<= 2 n)
		   (i-limited x) (i-limited y) (i-large n))
	      (i-small (sumlist (prod-sum-delta x y 0 n))))))

;; Now, 2 < n when n is large...duh...

(local
 (defthm 2-<-large-n
   (implies (and (integerp n)
		 (<= 0 n)
		 (i-large n))
	    (<= 2 n))
   :hints (("Goal"
	    :use ((:instance large-if->-large (x n) (y 2)))
	    :in-theory (disable large-if->-large)))))

;; So I can get a better reformulation of the fact that the sum of the
;; prod-sum-delta is small.

(local
 (defthm prod-sum-delta-small-better
     (implies (and (integerp n) (<= 0 n)
		   (i-limited x) (i-limited y) (i-large n))
	      (i-small (sumlist (prod-sum-delta x y 0 n))))))

;; Next, we can show that the difference between the product of the
;; Taylor approximation of e^x and e^y and the Taylor approximation of
;; e^{x+y} is small.  This is a Big Moment!

(local
 (defthm expt-x-*-expt-y-n---exp-x-y-k-n-small
   (implies (and (integerp nterms) (<= 0 nterms)
		 (i-limited x) (i-limited y)
		 (i-large nterms))
	    (i-small (- (* (sumlist
			    (taylor-exp-list nterms 0 x))
			   (sumlist
			    (taylor-exp-list nterms 0
					     y)))
			(sumlist
			 (taylor-exp-list nterms
					  0
					  (+ x y))))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance expt-x-*-expt-y-n---exp-x-y-k-n-=-prod-sum-delta)
		  (:instance prod-sum-delta-small-better (n (+ 1 nterms))))
	    :in-theory (disable expt-x-*-expt-y-n---exp-x-y-k-n-=-prod-sum-delta
				prod-sum-delta-small-better
				prod-sum-delta-small
				taylor-exp-list
				taylor-exp-term
				sumlist
				prod-sum-delta-3
				taylor-exp-list-3)))))

;; And if two numbers are small, they have the same standard-part
;; (namely 0).

(local
 (defthm small-x-y->same-standard-part
   (implies (and (i-small (- x y))
		 (acl2-numberp x)
		 (i-limited y))
	    (equal (standard-part x) (standard-part y)))
   :hints (("Goal"
	    :use ((:instance close-x-y->same-standard-part))
	    :in-theory (enable-disable (i-close i-small) (close-x-y->same-standard-part))))))

;; Now, exp-x-y-k-n is limited.

(local
 (defthm exp-x-y-k-n-limited
   (implies (and (i-limited x) (i-limited y))
	    (i-limited (sumlist (exp-x-y-k-n x y 0 (+ -1 (i-large-integer))))))
   :hints (("Goal"
	    :use ((:instance exp-k-n-sum-simplification
			     (nterms (i-large-integer)))
		  (:instance taylor-exp-list-limited (x (+ x y))))
	    :in-theory (disable exp-k-n-sum-simplification
				taylor-exp-list-limited)))))

;; and so we can take standard-parts everywhere and get that the
;; standard-part of the products of the Taylor approximations is the
;; standard-part of the approximation of the product.

(local
 (defthm expt-x-*-expt-y-n---exp-x-y-k-n-standard-parts
   (implies (and (i-limited x) (i-limited y))
	    (equal (standard-part
		    (* (sumlist (taylor-exp-list (i-large-integer) 0 x))
		       (sumlist (taylor-exp-list (i-large-integer) 0 y))))
		   (standard-part
		    (sumlist (taylor-exp-list (i-large-integer)
					      0
					      (+ x y))))))
   :hints (("Goal"
	    :use ((:instance small-x-y->same-standard-part
			     (x (* (sumlist (taylor-exp-list (i-large-integer) 0 x))
				   (sumlist (taylor-exp-list (i-large-integer) 0 y))))
			     (y (sumlist (taylor-exp-list (i-large-integer)
							  0
							  (+ x y)))))
		  (:instance expt-x-*-expt-y-n---exp-x-y-k-n-small
			     (nterms (i-large-integer)))
		  (:instance taylor-exp-list-limited)
		  (:instance taylor-exp-list-limited (x y))
		  )
	    :in-theory (disable close-x-y->same-standard-part
				small-x-y->same-standard-part
				expt-x-*-expt-y-n---exp-x-y-k-n-small
				taylor-exp-list-limited)
))))

;; And the same theorem holds after we consider how ACL2 will rewrite
;; the term!

(local
 (defthm expt-x-*-expt-y-n---exp-x-y-k-n-standard-parts-better
   (implies (and (i-limited x) (i-limited y))
	    (equal (* (standard-part
		       (sumlist (taylor-exp-list (i-large-integer) 0 x)))
		      (standard-part
		       (sumlist (taylor-exp-list (i-large-integer) 0 y))))
		   (standard-part
		    (sumlist (taylor-exp-list (i-large-integer)
					      0
					      (+ x y))))))
   :hints (("Goal"
	    :use ((:instance expt-x-*-expt-y-n---exp-x-y-k-n-standard-parts)
		  (:instance standard-part-of-times
			     (x (sumlist (taylor-exp-list (i-large-integer) 0 x)))
			     (y (sumlist (taylor-exp-list (i-large-integer) 0 y))))
		  (:instance taylor-exp-list-limited)
		  (:instance taylor-exp-list-limited (x y)))
	    :in-theory nil))))

;; And therefore, it follows that e^x=e^y for all standard x and y,
;; and by transfer for all x and y!

(defthm-std exp-sum
  (implies (and (acl2-numberp x)
		(acl2-numberp y))
	   (equal (acl2-exp (+ x y))
		  (* (acl2-exp x) (acl2-exp y))))
  :hints (("Goal"
	   :in-theory (disable taylor-exp-list-=-taylor-exp-list-3))))
