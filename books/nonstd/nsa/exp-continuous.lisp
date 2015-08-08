;; This book proves the fact that e^x is a continuous function.  That
;; is, for standard x, e^x is close to e^y if x is close to y.  The
;; argument is that if x is close to y, then y=x+eps where eps is some
;; infinitesimal.  So, e^y=e^{x+eps} = e^x * e^eps.  Moreover, e^eps
;; is infinitesimally close to 1, so it can be written as 1+eps2.  So,
;; we have that e^y = e^x * (1+eps2) = e^x + eps2 * e^x.  Since e^x is
;; limited and eps2 is infinitesimal, eps2 * e^x is infinitesimal and
;; so e^y = e^x + eps3 where eps3 is some infinitesimal.  In other
;; words, e^y is close to e^x.

(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "exp-sum")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; First we show that e^x is infinitesimally close to 1 when x is
;; infinitesimal.  To do this, we consider the partial sums of the
;; Taylor expansion of e^x = 1 + x + x^2/2! + ... + x^n/n!.  We want
;; to show that the terms involving x are infinitesimal.  We can't
;; just say well, each term is infinitesimal, so the sum is
;; infinitesimal, since we don't know how large n is.  E.g., the
;; sequence 1/n + 1/n + ... + 1/n is not necessarily small just
;; because 1/n is small -- if there are n of the 1/n terms, the sum is
;; equal to 1.  Instead, we try to find an upper bound for the sum.
;; Consider x^k/k! = x * (x^{k-1}/k!) < x * (x^{k-1}/2^{k-1}).
;; The trick is that k! > 2^{k-1}, for k>2.  So, now, the sum of the
;; Taylor terms x + x^2/2! + ... + x^n/n! can be bounded by the
;; geometric series x + x*(x/2) + x*(x/2)^2 + ... x*(x/2)^{n-1}.
;; Moreover, if x<1, this series can be bounded by the simpler
;; x + x/2 + x/2^2 + ... x/2^{n-1} < 2x.  So, if x is small, it
;; follows that x + x^2/2! + ... + x^n/n! < 2x is also small, and so
;; e^x is close to 1.  There's an important trick, however.  The
;; expression e^x can not be expanded into its Taylor approximation
;; unless x is standard.  So in particular, we do not want to reason
;; about x being infinitesimal above!  Instead, we simply assume that
;; x<1 (or more properly that norm(x)<1) and then show that e^x<x*x.
;; Then, we can talk about what happens when x is infinitesimal, in
;; which case x<1, and x*x is infinitesimal.

;; So first, we show that for x<1, x^n < x, so that we can think about
;; the sequence x + x/2! + x/3! + ... + x/n!

(local
 (defthm lemma-1
   (implies (and (< (norm x) 1)
		 (integerp n)
		 (<= 2 n))
	    (<= (norm (expt x n)) (norm x)))))

;; Now, we want to get rid of the n! terms.  We do that by considering
;; the function 2^n, which is less than n!.

(local
 (defun expt-2-n (n)
   (if (zp n)
       1
     (* 2 (expt-2-n (+ -1 n))))))

;; Here we establish that n! > 2^{n-1}, which is the key step.

(local
 (defthm lemma-2
   (implies (and (integerp n)
		 (<= 2 n))
	    (<= (norm (expt-2-n (+ -1 n)))
		(norm (factorial n))))
   :hints (("Goal" :induct (factorial n)
	    :in-theory (enable-disable (factorial) (norm-two))))))

(local (in-theory (disable expt-2-n expt)))

;; Simple algebraic rules.  You'd think ACL2 would do this by itself.

(local
 (defthm lemma-3
   (implies (and (realp x1) (<= 0 x1)
		 (realp x2) (<= x1 x2)
		 (realp y1) (<= 0 y1)
		 (realp y2) (<= y1 y2))
	    (<= (* x1 y1) (* y2 x2)))))

;; The lemmas above combine to show that x^n/n! < x/2^n.

(local
 (defthm lemma-4
   (implies (and (< (norm x) 1)
		 (integerp n)
		 (<= 2 n))
	    (<= (norm (taylor-exp-term x n))
		(* (norm x)
		   (/ (norm (expt-2-n (+ -1 n)))))))
   :hints (("Goal'"
	    :use ((:instance lemma-1)
		  (:instance lemma-2))
	    :in-theory (disable lemma-1 lemma-2)))))

(local (in-theory (disable taylor-exp-term)))

;; Now, consider the sequence 1, 1/2, 1/2^2, ..., 1/2^n

(local
 (defun expt-2-n-list (nterms n)
   (if (zp nterms)
       nil
     (cons (/ (expt-2-n (+ -1 n)))
	   (expt-2-n-list (1- nterms) (1+ n))))))


;; More algebra!

(local
 (defthm lemma-5
   (implies (and (realp x1) (realp x2) (<= x1 x2)
		 (realp y1) (realp y2) (<= y1 y2))
	    (<= (+ x1 y1) (+ x2 y2)))))

;; A key lemma is that x+x^2/2!+...+x^n/n! is bouned by x*(1+1/2+...+1/2^n).

(local
 (defthm lemma-6
   (implies (and (< (norm x) 1)
		 (integerp n)
		 (<= 2 n))
	    (<= (sumlist-norm
		 (taylor-exp-list nterms n x))
		(* (norm x)
		   (sumlist-norm
		    (expt-2-n-list nterms n)))))))


;; So now, we try to find the norm of (1+1/2+...+1/2^n).  First, we
;; look at the sum of the norms of the 1/2^k terms.

(local
 (defun expt-2-n-list-norm (nterms n)
   (if (zp nterms)
       nil
     (cons (/ (norm (expt-2-n (+ -1 n))))
	   (expt-2-n-list-norm (1- nterms) (1+ n))))))

;; We show that the norm of (1+1/2+...+1/2^n) is equal to the sum of
;; the norms of the 1/2^k terms.

(local
 (defthm sumlist-norm-expt-2-n-list
   (equal (sumlist-norm (expt-2-n-list nterms n))
	  (sumlist (expt-2-n-list-norm nterms n)))
   :hints (("Goal" :induct (expt-2-n-list nterms n)))))

;; A simple rewrite rule to "drive car into" expt-2-n-list-norm.

(local
 (defthm car-expt-2-n-list-norm
   (equal (car (expt-2-n-list-norm nterms n))
	  (if (zp nterms)
	      nil
	    (/ (norm (expt-2-n (+ -1 n))))))
   :hints (("Goal" :expand ((EXPT-2-N-LIST-NORM nterms n))))))

;; And here is a crucial lemma: (1+1/2+...+1/2^n) is a geometric
;; sequence with ration 1/2.

(local
 (defthm geometric-sequence-p-expt-2-n-list-norm
   (implies (and (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (geometric-sequence-p (expt-2-n-list-norm nterms n) 1/2))
   :hints (("Subgoal *1/4.2" ; Subgoal number changed by Matt K. for v2-9.
	    :expand ((expt-2-n n)))
	   ("Subgoal *1/3''"
	    :expand ((expt-2-n-list-norm 1 n))))))

(local (in-theory (disable expt-2-n-list-norm)))

;; Because of the previous lemma, we can find the sum of the sequence
;; (1+1/2+...+1/2^n) using the standard geometric sequence sum.

(local
 (defthm sumlist-expt-2-n-list-norm
   (implies (and (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (equal (sumlist (expt-2-n-list-norm nterms n))
		   (- (* 2 (/ (norm (expt-2-n (+ -1 n)))))
		      (last-elem (expt-2-n-list-norm nterms n)))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance sumlist-geometric
			     (seq (expt-2-n-list-norm nterms n))
			     (ratio 1/2)))
	    :in-theory (disable sumlist last-elem expt-2-n-list-norm
				expt-2-n))
	   ("Goal'''"
	    :expand ((expt-2-n-list-norm nterms n))))))


;; A simple lemma, 2/2^n = 1/2^{n-1}....

(local
 (defthm lemma-7
   (implies (and (integerp n)
		 (<= 1 n))
	    (equal (* 2 (/ (norm (expt-2-n n))))
		   (/ (norm (expt-2-n (+ -1 n))))))
   :hints (("Goal" :induct (expt-2-n n)
	    :in-theory (enable expt-2-n)))))

;; We need to let ACL2 know about the type of the terms in
;; expt-2-n-list-norm -- they are positive reals.

(local
 (defthm lemma-8
   (implies (and (not (zp nterms))
		 (not (zp n)))
	    (and (realp (last-elem (expt-2-n-list-norm nterms n)))
		 (<= 0 (last-elem (expt-2-n-list-norm nterms n)))))
   :hints (("Goal"
	    :in-theory (enable expt-2-n-list-norm)))))

;; A simple algebraic rule.....

(local
 (defthm lemma-9
   (implies (and (equal z (+ x (- y)))
		 (<= 0 y)
		 (equal x x1))
	    (<= z x1))))

;; So now we have a simple bound for the sum of the 1/2^n terms.

(local
 (defthm lemma-10
   (implies (and (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (<= (sumlist (expt-2-n-list-norm nterms n))
		(* 2 (/ (norm (expt-2-n (+ -1 n)))))))
   :hints (("Goal" :do-not-induct t
	     :use ((:instance sumlist-expt-2-n-list-norm))
	     :in-theory (disable sumlist-expt-2-n-list-norm lemma-7)))))

;; And more to the point, the terms 1/2^k + ... + 1/2^n add up to no
;; more than 1/2^{k-2}.

(local
 (defthm lemma-11
   (implies (and (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (<= (sumlist (expt-2-n-list-norm nterms n))
		(/ (norm (expt-2-n (+ -2 n))))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-10))
	    :in-theory (disable sumlist-expt-2-n-list-norm lemma-10)))))

;; So now we note that 1/2^n < 1...

(local
 (defthm lemma-12
   (implies (and (integerp n)
		 (<= 0 n))
	    (<= (/ (norm (expt-2-n n))) 1))
   :hints (("Goal"
	    :induct (expt-2-n n)
	    :in-theory (enable expt-2-n)))))

;; and so the sum of the terms 1/2^k + ... + 1/2^n is less than 1 (for
;; k>=2).

(local
 (defthm sumlist-expt-2-n-list-norm-best
   (implies (and (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (<= (sumlist (expt-2-n-list-norm nterms n))
		1))
   :hints (("Goal" :use ((:instance lemma-11)
			 (:instance lemma-12 (n (+ -2 n))))
	    :in-theory nil
	    :do-not-induct t))))


;; We let ACL2 know that the sum of 1/2^k + ... + 1/2^n is real.

(local
 (defthm lemma-13
   (realp (sumlist (expt-2-n-list-norm nterms n)))
   :hints (("Goal" :in-theory (enable expt-2-n-list-norm)))))

;; This lemma is just an algebraic simplification.  Since we know that
;; 1/2^k + ... + 1/2^n < 1, it follows that x*(1/2^k + ... + 1/2^n) < x

(local
 (defthm lemma-14
   (implies (and (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (<= (* (norm x) (sumlist (expt-2-n-list-norm nterms n)))
		(norm x)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance sumlist-expt-2-n-list-norm-best)
		  (:instance <-*-left-cancel
			     (x 1)
			     (z (norm x))
			     (y (sumlist (expt-2-n-list-norm nterms n)))))
	    :in-theory (disable sumlist-expt-2-n-list-norm-best
				sumlist-expt-2-n-list-norm
				;silly-inequality
				<-*-left-cancel
				<-y-*-y-x
				lemma-7)))))

;; From that and the previous lemma about n! and 2^n, we have that
;; x^2/2! + ... + x^n/n! < x.

(local
 (defthm lemma-15
   (implies (and (< (norm x) 1)
		 (not (zp nterms))
		 (integerp n)
		 (<= 2 n))
	    (<= (sumlist-norm
		 (taylor-exp-list nterms n x))
		(norm x)))
   :hints (("Goal" :use ((:instance lemma-6)
			 (:instance lemma-14))
	    :in-theory (disable lemma-6 lemma-14)
	    :do-not-induct t))))

;; Now, we show how the sum of the norms of x + x^2/2! + ... + x^n/n!
;; is related to that of x^2/2! + ... + x^n/n! since we already have a
;; bound for the latter term.

(local
 (defthm lemma-16
   (implies (and (integerp nterms)
		 (<= 1 nterms))
	    (equal (sumlist-norm (taylor-exp-list nterms 1 x))
		   (+ (norm x)
		      (sumlist-norm (taylor-exp-list (+ -1 nterms) 2 x)))))
   :hints (("Goal" :do-not-induct t
	    :expand ((taylor-exp-list nterms 1 x)))
	   ("Goal'"
	    :expand ((taylor-exp-term X 1))
	    :in-theory (enable expt)))))

;; Now, we simplify a few constant terms.  First, (taylor-exp-list 1 1 x)
;; is just x, so its norm is norm(x).

(local
 (defthm lemma-17
   (equal (sumlist-norm (taylor-exp-list 1 1 x))
	  (norm x))))

;; And here is a degenerate case.  When there are no terms in the
;; sequence, its sum (and hence norm) is zero.

(local
 (defthm lemma-18
   (equal (sumlist-norm (taylor-exp-list 0 n x)) 0)))

;; Finally, we have that x + x^2/2! + ... + x^n/n! < x + x

(local
 (defthm lemma-19
   (implies (and (< (norm x) 1)
		 (integerp nterms)
		 (<= 1 nterms))
	    (<= (sumlist-norm (taylor-exp-list nterms 1 x))
		(+ (norm x) (norm x))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-15 (nterms (+ -1 nterms)) (n 2))
		  (:instance lemma-16))
	    :in-theory (disable lemma-5 lemma-15 sumlist-norm taylor-exp-list)))))

;; Another constant term.  The first term in the taylor sequence of
;; e^x is 1.

(local
 (defthm lemma-20
   (equal (taylor-exp-term x 0) 1)
   :hints (("Goal" :in-theory (enable taylor-exp-term expt)))))

;; This rewrite lemma allows us to get the sum of the Taylor sequence
;; in terms of x + x^2/2! + ... + x^n/n!.

(local
 (defthm lemma-21
   (implies (and (integerp nterms) (< 0 nterms))
	    (equal (+ -1 (sumlist (taylor-exp-list nterms 0 x)))
		   (sumlist (taylor-exp-list (+ -1 nterms) 1 x))))
   :hints (("Goal" :do-not-induct t
	    :expand ((taylor-exp-list nterms 0 x))))))


;; So now, we want to think about standard-parts.  First, we establish
;; that the terms we are interested in are limited.  This is
;; straight-forward, since we already know the Taylor list is limited.

(local
 (defthm lemma-22
   (implies (i-limited x)
	    (i-limited (+ 1
			  (sumlist (taylor-exp-list
				    (+ -1 (i-large-integer)) 1 x)))))
   :hints (("Goal"
	    :use ((:instance taylor-exp-list-limited))
	    :in-theory (disable taylor-exp-list-limited))
	   ("Goal'"
	    :expand ((taylor-exp-list (i-large-integer) 0 x))))))

;; So we can take standard-parts of both sides and get an expression
;; for standard_part(1-Taylor(e^x)).

(local
 (defthm lemma-23
   (implies (i-limited x)
	    (equal (+ -1
		      (standard-part
		       (sumlist (taylor-exp-list (i-large-integer) 0 x))))
		   (standard-part
		    (sumlist (taylor-exp-list (+ -1 (i-large-integer)) 1 x)))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance standard-part-of-plus
			     (x -1)
			     (y (sumlist (taylor-exp-list (i-large-integer)
							  0 x)))))))))
;; Similarly, we know Taylor_1^n(e^x)<x+x, so we take standard-parts
;; of both sides.

(local
 (defthm lemma-24
   (implies (< (norm x) 1)
	    (<= (standard-part
		 (sumlist-norm (taylor-exp-list (+ -1 (i-large-integer)) 1 x)))
		(standard-part (+ (norm x) (norm x)))))
   :hints (("Goal"
	    :use ((:instance lemma-19 (nterms (+ -1 (i-large-integer))))

		  (:instance standard-part-<=
			     (x (sumlist-norm (taylor-exp-list (+ -1 (i-large-integer)) 1 x)))
			     (y (+ (norm x) (norm x)))))
	    :in-theory (disable lemma-19 lemma-16
				standard-part-<=)))))

;; And now we establish the same result, but taking the norm of the
;; sum instead of the sum of the norms.

(local
 (defthm lemma-25
   (implies (< (norm x) 1)
	    (<= (standard-part
		 (norm (sumlist (taylor-exp-list (+ -1 (i-large-integer)) 1 x))))
		(standard-part (+ (norm x) (norm x)))))
   :hints (("Goal"
	    :use ((:instance lemma-24)
		  (:instance norm-sumlist-<=-sumlist-norm
			     (l (taylor-exp-list (+ -1 (i-large-integer)) 1 x)))
		  (:instance standard-part-<=
			     (x (norm (sumlist (taylor-exp-list (+ -1 (i-large-integer)) 1 x))))
			     (y (sumlist-norm (taylor-exp-list (+ -1 (i-large-integer)) 1 x)))))
	    :in-theory (disable lemma-24 standard-part-<=
				norm-sumlist-<=-sumlist-norm)))))

;; For standard x, we can simplify standard_part(x+x) into x+x.

(local
 (defthm lemma-26
   (implies (standard-numberp x)
	    (equal (standard-part (+ (norm x) (norm x)))
		   (+ (norm x) (norm x))))
   :hints (("Goal"
	    :use ((:instance standard-part-of-plus
			     (x (norm x))
			     (y (norm x)))
		  (:instance standards-are-limited))
	    :in-theory (disable standard-part-of-plus standards-are-limited)))))

;; And so, if x is standard and less than 1, we have that
;; standard-part(1-Taylor_1^n(e^x)) is less than x+x.

(local
 (defthm lemma-27
   (implies (and (standard-numberp x)
		 (< (norm x) 1))
	    (<= (standard-part
		 (norm (+ -1 (sumlist (taylor-exp-list (i-large-integer) 0 x)))))
		(+ (norm x) (norm x))))
   :hints (("Goal"
	    :use ((:instance lemma-26)
		  (:instance lemma-25)
		  (:instance lemma-21 (nterms (i-large-integer))))
	    :in-theory nil))))

;; And this is the same result, but pushing the standard-part into the
;; norm.

(local
 (defthm lemma-28
   (implies (and (standard-numberp x)
                 (< (norm x) 1))
            (<= (norm
                 (standard-part (+ -1
                                   (sumlist
                                    (taylor-exp-list
                                     (i-large-integer)
                                     0
                                     x)))))
                (+ (norm x) (norm x))))
   :hints (("Goal"
	    :use ((:instance lemma-27)
		  (:instance taylor-exp-list-limited)
		  (:instance i-limited-plus
			     (x -1)
			     (y (sumlist (taylor-exp-list (i-large-integer) 0 x)))))
	    :in-theory (disable lemma-27 taylor-exp-list-limited
				i-limited-plus)))))

;; Again, the same theorem, but we take the 1 out of the
;; standard-part(1-X) term.

(local
 (defthm lemma-29
   (implies (and (standard-numberp x)
		 (< (norm x) 1))
	    (<= (norm
		 (+ -1 (standard-part (sumlist (taylor-exp-list (i-large-integer) 0 x)))))
		(+ (norm x) (norm x))))
   :hints (("Goal"
	    :use ((:instance lemma-28))
	    :in-theory (disable lemma-28)))))

;; And now, by transfer we have that for all numbers with |x|<1,
;; |1-e^x|<|x|+|x|.

(local
 (defthm-std lemma-30
   (implies (and (acl2-numberp x)
		 (< (norm x) 1))
	    (<= (norm (+ -1 (acl2-exp x)))
		(+ (norm x) (norm x))))
   :hints (("Goal" :in-theory (disable lemma-23)))))

;; We're almost done.  We only need to establish that |x|<1 for
;; infinitesimal x.  That allows us to use the previous theorem.

(local
 (defthm lemma-31
   (implies (i-small x)
	    (< (norm x) 1))
   :hints (("Goal"
	    :use ((:instance small-<-non-small
			     (x (norm x))
			     (y 1))
		  (:instance standard-small-is-zero (x 1)))
	    :in-theory (disable small-<-non-small)))))

;; Now, we simplify the terms |norm(x)+norm(x)|, since the |..| are
;; redundant.

(local
 (defthm lemma-32
   (equal (abs (+ (norm x) (norm x)))
	  (+ (norm x) (norm x)))))

;; The same goes for the simpler |norm(x)| term.

(local
 (defthm lemma-33
   (equal (abs (norm x)) (norm x))))

;; From the above, it is established that if x is small, norm(1-e^x)
;; is also small.

(local
 (defthm lemma-34
   (implies (and (acl2-numberp x)
		 (i-small x))
	    (i-small (norm (+ -1 (acl2-exp x)))))
   :hints (("Goal"
	    :use ((:instance small-if-<-small
			     (x (+ (norm x) (norm x)))
			     (y (norm (+ -1 (acl2-exp x))))))
	    :in-theory (disable small-if-<-small)))))


;; And thus it follows that 1-e^x is small.

(local
 (defthm lemma-35
   (implies (and (acl2-numberp x)
		 (i-small x))
	    (i-small (+ -1 (acl2-exp x))))
   :hints (("Goal"
	    :use ((:instance small-norm
			     (x (+ -1 (acl2-exp x)))))
	    :in-theory (disable small-norm)))))

;; Or alternatively that e^x is close to 1.

(defthm exp-of-infinitesimal
  (implies (i-small x)
	   (i-close (acl2-exp x) 1))
  :hints (("Goal" :in-theory (enable i-close))))

;; Now, if x and y are limited and x is close to 1, we show that y-x*y
;; is small.

(local
 (defthm lemma-36
	 (implies (and (i-limited x)
		       (i-limited y)
		       (i-close x 1))
		  (i-small (+ y (- (* y x)))))
	 :hints (("Goal"
		  :in-theory (enable i-close i-small))
		 ("Goal''"
		  :use ((:theorem (implies (equal (+ -1 (standard-part x)) 0)
					   (equal (standard-part x) 1))))))))

;; And so, if y is limited and 1-x is small, y-y*x is small.

(local
 (defthm lemma-37
	 (implies (and (i-limited y)
		       (i-small (+ -1 x)))
		  (i-small (+ y (- (* y x)))))
	 :hints (("Goal"
		  :use ((:instance lemma-36)
			(:instance i-close-limited-2 (y 1)))
		  :in-theory (enable i-close i-small)))))

;; A quick lemma, e^x is limited for standard x.

(defthm exp-limited
  (implies (standard-numberp x)
	   (i-limited (acl2-exp x))))

;; Now, from the above lemmas, it follows that if x is standard and y
;; is close to x, e^x is close to e^y.

(defthm exp-continuous
  (implies (and (standard-numberp x)
		(i-close y x))
	   (i-close (acl2-exp x) (acl2-exp y)))
  :hints (("Goal"
	   :use ((:instance exp-sum
			    (x x)
			    (y (- y x)))
		 (:instance exp-of-infinitesimal
			    (x (- y x))))
	   :in-theory (enable-disable (i-close)
				      (acl2-exp
				       exp-sum
				       lemma-35
				       exp-of-infinitesimal)))
	  ("Goal'4'"
	   :use ((:instance lemma-37
			    (x (acl2-exp (+ (- x) y)))
			    (y (acl2-exp x)))
		 (:instance exp-limited))
	   :in-theory (disable lemma-36 lemma-37 exp-limited))))

;; This is the same theorem, but with x close to y, instead of y close
;; to x -- which is the same thing, of course, but not to the rewriter!

(defthm exp-continuous-2
  (implies (and (standard-numberp x)
		(i-close x y))
	   (i-close (acl2-exp x) (acl2-exp y)))
  :hints (("Goal"
	   :use ((:instance exp-continuous)
		 (:instance i-close-symmetric))
	   :in-theory nil)))
