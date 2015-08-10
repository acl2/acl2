(in-package "ACL2")

;; This book proves the extreme-value theorems; i.e., a continuous function
;; achieves its maximum and minimum over a closed interval.

(include-book "nonstd/nsa/continuity" :dir :system)

(local (include-book "arithmetic/idiv" :dir :system))

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; First, we introduce rcfn-2 - a Real Continuous FunctioN of two
;; arguments.  It is assumed to return standard values for standard
;; arguments, and to satisfy the continuity criterion.

(encapsulate
 ((rcfn-2 (x arg) t)
  (rcfn-2-domain () t))

 ;; Our witness real-valued continuous function is the identity function of
 ;; x. We ignore the extra argument arg.

 (local (defun rcfn-2 (x arg) (declare (ignore arg)) (realfix x)))
 (local (defun rcfn-2-domain () (interval nil nil)))

 ;; The interval really is an interval

 (defthm intervalp-rcfn-2-domain
   (interval-p (rcfn-2-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm rcfn-2-domain-real
   (implies (inside-interval-p x (rcfn-2-domain))
            (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm rcfn-2-domain-non-trivial
   (or (null (interval-left-endpoint (rcfn-2-domain)))
       (null (interval-right-endpoint (rcfn-2-domain)))
       (< (interval-left-endpoint (rcfn-2-domain))
          (interval-right-endpoint (rcfn-2-domain))))
   :rule-classes nil)

 ;; The function returns real values (even for improper arguments).

 (defthm rcfn-2-real
   (realp (rcfn-2 x arg))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y is a real close to x, then rcfn-2(x, arg)
 ;; is close to rcfn-2(y, arg).

 (defthm rcfn-2-continuous
   (implies (and (standardp arg)
                 (standardp x)
		 (inside-interval-p x (rcfn-2-domain))
		 (i-close x y)
		 (inside-interval-p y (rcfn-2-domain)))
	    (i-close (rcfn-2 x arg) (rcfn-2 y arg))))
 )

(defthm-std standardp-nth-i-arg
  (implies (and (standardp arg)
                (standardp i))
           (standardp (nth i arg)))
  :rule-classes (:rewrite :type-prescription))

(defthm-std rcfn-2-standard
    (implies (and (standardp x)
                  (standardp arg))
	     (standardp (rcfn-2 x arg)))
  :rule-classes (:rewrite :type-prescription))

(defthm-std standardp-rcfn-2-domain
    (standardp (rcfn-2-domain))
  :rule-classes (:rewrite :type-prescription))

;; Now, we show that Rcfn is uniformly continuous when it is
;; continuous over a closed, bounded interval.

(defthm rcfn-2-uniformly-continuous
  (implies (and (standardp arg)
                (interval-left-inclusive-p (rcfn-2-domain))
		(interval-right-inclusive-p (rcfn-2-domain))
		(inside-interval-p x (rcfn-2-domain))
		(i-close x y)
		(inside-interval-p y (rcfn-2-domain)))
	   (i-close (rcfn-2 x arg) (rcfn-2 y arg)))
  :hints (("Goal"
	   :use ((:instance rcfn-2-continuous
			    (x (standard-part x))
			    (y x))
		 (:instance rcfn-2-continuous
			    (x (standard-part x))
			    (y y))
		 (:instance i-close-transitive
			    (x (standard-part x))
			    (y x)
			    (z y))
		 (:instance i-close-transitive
			    (x (rcfn-2 x arg))
			    (y (rcfn-2 (standard-part x) arg))
			    (z (rcfn-2 y arg)))
		 (:instance i-close-symmetric
			    (x (rcfn-2 (standard-part x) arg))
			    (y (rcfn-2 x arg)))
		 (:instance standard-part-inside-interval
			    (x x)
			    (interval (rcfn-2-domain)))
		 )
	   :in-theory (disable rcfn-2-continuous i-close-transitive
			       i-close-symmetric
			       standard-part-inside-interval))))

;; But using that lemma, we can prove that (rcfn-2 (std-pt x) arg) is equal
;; to (std-pt (rcfn-2 x arg)) -- the reason is that x is close to its
;; std-pt, and since rcfn is continuous, that means (rcfn-2 x arg) is to
;; close to the (rcfn-2 (std-pt x) arg).  The last one is known to be
;; standard (by an encapsulate hypothesis), so it must be the
;; standard-part of (rcfn-2 x arg).

(defthm rcfn-2-standard-part
  (implies (and (standardp arg)
                (inside-interval-p x (rcfn-2-domain))
		(inside-interval-p (standard-part x) (rcfn-2-domain))
		(i-limited x))
	   (equal (rcfn-2 (standard-part x) arg)
		  (standard-part (rcfn-2 x arg))))
  :hints (("Goal"
	   :use ((:instance rcfn-2-continuous
			    (x (standard-part x))
			    (y x))
		 (:instance close-x-y->same-standard-part
			    (x (RCFN-2 (STANDARD-PART X) arg))
			    (y (RCFN-2 X arg))))
	   :in-theory (enable-disable (standards-are-limited)
				      (rcfn-2-continuous
				       rcfn-2-uniformly-continuous
				       close-x-y->same-standard-part)))))

;; The next task is to prove the extreme theorems.  The approach is
;; similar to the intermediate-value theorem.  First, we define a
;; function that splits up the interval [a,b] into a grid of size eps
;; and then we find the maximum of the function at the points in the
;; grid.

(defun find-max-rcfn-2-x-n (a max-x i n eps arg)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (> (rcfn-2 (+ a (* i eps)) arg) (rcfn-2 max-x arg))
	  (find-max-rcfn-2-x-n a (+ a (* i eps)) (1+ i) n eps arg)
	(find-max-rcfn-2-x-n a max-x (1+ i) n eps arg))
    max-x))

;; Since the function above takes in a "max-so-far" argument, it is
;; important to note that the initial value of max-so-far is a lower
;; bound for the maximum.

(defthm find-max-rcfn-2-x-n-is-monotone
  (<= (rcfn-2 max-x arg)
      (rcfn-2 (find-max-rcfn-2-x-n a max-x i n eps arg)
              arg)))

;; Now, we can say that the maximum returned really is the maximum of
;; all the f(x) values at the points x on the grid.

(defthm find-max-rcfn-2-x-n-is-maximum
  (implies (and (integerp i)
		(integerp k)
		(integerp n)
		(<= 0 i)
		(<= i k)
		(<= k n)
		(realp a)
		(realp eps)
		(< 0 eps))
	   (<= (rcfn-2 (+ a (* k eps)) arg)
	       (rcfn-2 (find-max-rcfn-2-x-n a max-x i n eps arg) arg)))
  :hints (("Subgoal *1/7"
	   :use ((:instance find-max-rcfn-2-x-n-is-monotone))
	   :in-theory (disable find-max-rcfn-2-x-n-is-monotone))))

;; Naturally, we want to prove that the x value returned for the
;; maximum is in the interval [a,b].  First, we show that it's at most
;; b.  Notice we need to assume the starting value of max-x is less
;; than b!

(defthm find-max-rcfn-2-x-n-upper-bound
  (implies (and (<= max-x (+ a (* n eps)))
		(realp a)
		(realp eps)
		(integerp i)
		(integerp n)
		(< 0 eps))
	   (<= (find-max-rcfn-2-x-n a max-x i n eps arg)
               (+ a (* n eps))))
  :hints (("Subgoal *1/1"
	   :use ((:theorem
		  (implies (and (< (+ a (* eps n)) (+ a (* i eps)))
				(realp a)
				(realp eps)
				(< 0 eps)
				(integerp i)
				(integerp n))
			   (< n i)))))
	  ("Subgoal *1/1.1"
	   :use ((:theorem
		  (implies (< (+ a (* eps n)) (+ a (* eps i)))
			   (< (* eps n) (* eps i)))))))
  :rule-classes nil)

;; To show that find-max-rcfn-2-x-n returns a value that is not less
;; than a, we need a simple lemma to do the induction at each of the
;; points in the grid.

(defthm find-max-rcfn-2-x-n-lower-bound-lemma
  (implies (<= max-x (+ a (* i eps)))
	   (<= max-x (find-max-rcfn-2-x-n a max-x i n eps arg))))

;; Now, we can fix the lower range of find-max-x-r-n

(defthm find-max-rcfn-2-x-n-lower-bound
  (<= a (find-max-rcfn-2-x-n a a 0 n eps arg))
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-2-x-n-lower-bound-lemma
			    (max-x a)
			    (i 0)))
	   :in-theory (disable find-max-rcfn-2-x-n-lower-bound-lemma))))

;; Next, we would like to use defun-std to introduce find-max-x.
;; Before that, we have to show that find-max-x-n is i-limited.  This
;; is simple, since we know it's in the range [a,b] and b is limited.

(defthm find-max-rcfn-2-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-max-rcfn-2-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b))
                                    arg)))
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-2-x-n-upper-bound
			    (max-x a)
			    (n (i-large-integer))
			    (eps (/ (- b a) (i-large-integer)))
			    (i 0))))
	  ("Goal'"
	   :use ((:instance
		  (:theorem
		   (implies (and (realp a)
				 (realp b)
				 (realp x)
				 (i-limited a)
				 (i-limited b)
				 (<= a x)
				 (<= x b))
			    (i-limited x)))
		  (x (find-max-rcfn-2-x-n a a 0 (i-large-integer)
				   (+ (- (* (/ (i-large-integer)) a))
				      (* (/ (i-large-integer))
					 b))
                                   arg)))))
	  ("Subgoal 1'"
	   :use ((:instance large-if->-large
			    (x x)
			    (y (if (< (abs a) (abs b))
				   (abs b)
				 (abs a)))))
	   :in-theory (disable large-if->-large))))

;; More important, if a and b are in the domain, so is find-max-x-n,
;; and that also follows since we know it's inside [a,b]

(defthm find-max-rcfn-2-x-n-in-domain
    (implies (and (inside-interval-p a (rcfn-2-domain))
		  (inside-interval-p b (rcfn-2-domain))
		  (< a b))
	     (inside-interval-p
              (find-max-rcfn-2-x-n a a
                                   0 (i-large-integer)
                                   (+ (- (* (/ (i-large-integer)) a))
                                      (* (/ (i-large-integer)) b))
                                   arg)
                                (rcfn-2-domain)))
  :hints (("Goal"
	   :use ((:instance
                  INSIDE-INTERVAL-P-SQUEEZE
                  (a a)
                  (b b)
                  (c (find-max-rcfn-2-x-n a a
                                          0 (i-large-integer)
                                          (+ (- (* (/ (i-large-integer)) a))
                                             (* (/ (i-large-integer)) b))
                                          arg))
                  (interval (rcfn-2-domain)))
		 (:instance find-max-rcfn-2-x-n-upper-bound
			    (a a)
			    (max-x a)
			    (i 0)
			    (n (i-large-integer))
			    (eps (+ (- (* (/ (i-large-integer)) a))
				    (* (/ (i-large-integer)) b))))
		 )
	   :in-theory (disable INSIDE-INTERVAL-P-SQUEEZE))))

;; And now we can introduce the function find-max-rcfn-2-x which (we
;; claim) finds the point x in [a,b] at which (rcfn-2 x arg) achieves a
;; maximum.

(defun-std find-max-rcfn-2-x (a b arg)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-max-rcfn-2-x-n a
                                          a
                                          0
                                          (i-large-integer)
                                          (/ (- b a) (i-large-integer))
                                          arg))
    0))

;; So first, let's do the easy part of the claim, namely that the x
;; returned by find-max satisfies a <= x.

(defthm-std find-max-rcfn-2-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-max-rcfn-2-x a b arg)))
  :hints (("Goal'"
	   :use ((:instance standard-part-<=
			    (x a)
			    (y (find-max-rcfn-2-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))
                                   arg))))
	   :in-theory (disable standard-part-<=))))

;; Similarly, that x satisfies x <= b, so x is in [a, b].

(defthm-std find-max-rcfn-2-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-max-rcfn-2-x a b arg) b))
; Matt K. v7-1 mod for ACL2 mod on 2/13/2015: "Goal''" changed to "Goal'".
  :hints (("Goal'"
	   :use ((:instance standard-part-<=
			    (x (find-max-rcfn-2-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))
                                   arg))
			    (y b))
		 (:instance find-max-rcfn-2-x-n-upper-bound
			    (max-x a)
			    (i 0)
			    (n (i-large-integer))
			    (eps (/ (- b a) (i-large-integer))))

		 )
	   :in-theory (disable standard-part-<=))))

;; And find-max is inside an interval if a and b are inside the interval

(defthm find-max-rcfn-2-x-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (find-max-rcfn-2-x a b arg) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (find-max-rcfn-2-x a b arg))))
	   :in-theory (disable inside-interval-p-squeeze)))
  )

;; OK now, (rcfn-2 max arg) should be the maximum at all the grid points,
;; modulo standard-part.  Why?  Because max is (std-pt max-n).  By
;; construction, max-n is the maximum of all grid-points.  But, (rcfn-2
;; max arg) and (rcfn-2 max-n arg) are close to each other, since rcfn-2 is
;; continuous. Also, (rcfn-2 max arg) is standard, since max and arg are standard, so
;; (rcfn-2 max arg) = (std-pt (rcfn-2 max-n arg)) >= (std-pt (rcfn-2 x_i arg))
;; where x_i is any point in the grid.

(defthm find-max-rcfn-2-is-maximum-of-grid
  (implies (and (standardp arg)
                (realp a) (standardp a)
		(realp b) (standardp b)
		(inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(< a b)
		(integerp k)
		(<= 0 k)
		(<= k (i-large-integer)))
	   (<= (standard-part (rcfn-2 (+ a (* k (/ (- b a)
						 (i-large-integer))))
                                      arg))
	       (rcfn-2 (find-max-rcfn-2-x a b arg) arg)))
  :hints (("Goal"
	   :use ((:instance standard-part-<=
			    (x (rcfn-2 (+ a (* k (/ (- b a)
						  (i-large-integer))))
                                       arg))
			    (y (rcfn-2
				      (find-max-rcfn-2-x-n a a 0
						    (i-large-integer)
						    (/ (- b a)
						       (i-large-integer))
                                                    arg)
                                      arg)))
		 (:instance find-max-rcfn-2-x-n-is-maximum
			    (i 0)
			    (n (i-large-integer))
			    (eps (/ (- b a) (i-large-integer)))
			    (max-x a))
		 (:instance rcfn-2-standard-part
			    (x (FIND-MAX-RCFN-2-X-N A A 0 (I-LARGE-INTEGER)
						  (+ (- (* (/ (I-LARGE-INTEGER)) A))
						     (* (/ (I-LARGE-INTEGER)) B))
                                                  arg)))
                 (:instance find-max-rcfn-2-x-inside-interval
			    (a a)
			    (b b)
			    (interval (rcfn-2-domain))))
	   :in-theory (disable standard-part-<=
			       find-max-rcfn-2-x-n-is-maximum
			       rcfn-2-standard-part
			       find-max-rcfn-2-x-inside-interval))))

;; Now, we know the maximum we found really is the maximum at all the
;; grid points.  But what about an arbitrary x in [a,b]?  What we'll
;; do is to find where x falls in the grid.  I.e., we want the i so
;; that x is in [x_{i-1},x_i].  What we'll know is that (rcfn-2 x arg) is
;; the standard-part of (rcfn-2 x_i arg), since x and x_i are close to each
;; other, and x and arg are standard.  But then, since we know that
;; (rcfn-2 max arg) is >= (std-pt (rcfn-2 x_i arg)) = (rcfn-2 x arg) we have
;; that max really is the maximum for all x.

;; But wait!  That's not quite true.  The equality (std-pt (rcfn-2 x_i arg)) =
;; (rcfn-2 x arg) only holds when x and arg are standard!  So what this
;; argument does is prove that (rcfn-2 max arg) >= (rcfn-2 x arg) for all
;; standard x and standard arg.  To finish up the proof, we need to appeal to
;; the transfer principle!

;; We use the function upper-bound-of-grid that finds the right index i.

;; Since rcfn-2 is continuous, it follows that (rcfn-2 x arg) and
;; (rcfn-2 x_i arg) are close to each other!

(local
 (defthm cancel-<-+-obvious
     (implies (and (realp a)
		   (realp b)
		   (realp c))
	      (equal (< (+ a b) (+ a c))
		     (< b c)))
   :hints (("Goal"
	    :use ((:theorem (implies (and (realp a)
					  (realp b)
					  (realp c))
				     (iff (< (+ a b) (+ a c))
					  (< b c)))))))))

(defthm rcfn-2-x-close-to-rcfn-2-upper-bound-of-grid
  (implies (and (standardp arg)
                (integerp i)
		(<= 0 i)
		(integerp n)
		(<= i n)
		(realp eps)
		(< 0 eps)
		(inside-interval-p a (rcfn-2-domain))
		(inside-interval-p (+ a (* n eps)) (rcfn-2-domain))
		(realp x)
		(standardp x)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps)))
		(i-small eps))
	   (i-close (rcfn-2 x arg)
		    (rcfn-2 (+ a (* (upper-bound-of-grid a x i n eps)
				  eps))
                            arg)))
  :hints (("Goal"
	   :use ((:instance rcfn-2-continuous
			    (y (+ a (* (upper-bound-of-grid a x i n eps)
				       eps))))
		 (:instance x-in-upper-bound-of-grid-small-eps-better)
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b (+ a (* n eps)))
			    (c x)
			    (interval (rcfn-2-domain)))
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b (+ a (* n eps)))
			    (c (+ a (* i eps)))
			    (interval (rcfn-2-domain)))
		 (:instance inside-interval-p-squeeze
			    (a (+ a (* i eps)))
			    (b (+ a (* n eps)))
			    (c (+ a (* (upper-bound-of-grid a x i n eps) eps)))
			    (interval (rcfn-2-domain))))
	   :in-theory (disable rcfn-2-continuous
			       x-in-upper-bound-of-grid-small-eps-better
			       upper-bound-of-grid
			       inside-interval-p-squeeze))))

;; In particular, (std-pt (rcfn-2 x_i arg)) = (std-pt (rcfn-2 x arg)) and when
;; x and arg are standard that's equal to (rcfn-2 x arg).

(defthm rcfn-2-x-close-to-rcfn-2-upper-bound-of-grid-better
  (implies (and (standardp arg)
                (integerp i)
		(<= 0 i)
		(integerp n)
		(<= i n)
		(realp eps)
		(< 0 eps)
		(inside-interval-p a (rcfn-2-domain))
		(inside-interval-p (+ a (* n eps)) (rcfn-2-domain))
		(realp x)
		(standardp x)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps)))
		(i-small eps))
	   (equal (standard-part (rcfn-2 (+ a (* (upper-bound-of-grid a x i n eps)
					       eps))
                                         arg))
		  (rcfn-2 x arg)))
  :hints (("Goal"
	   :use ((:instance rcfn-2-x-close-to-rcfn-2-upper-bound-of-grid)
		 (:instance close-x-y->same-standard-part
			    (x (rcfn-2 x arg))
			    (y (rcfn-2 (+ a (* (upper-bound-of-grid a x i n eps)
					     eps))
                                       arg))))
	   :in-theory (disable
		       rcfn-2-x-close-to-rcfn-2-upper-bound-of-grid
		       close-x-y->same-standard-part
		       upper-bound-of-grid))))

;; So that means that (rcfn-2 max arg) >= (rcfn-2 x arg), because we already know
;; that (rcfn-2 max arg) >= (std-pt (rcfn-2 x_i arg)) for all indices i!
;; That only works for standard values of x and arg.

(local
 (defthm small-range
   (implies (and (realp a) (standardp a)
		 (realp b) (standardp b)
		 (< a b))
	    (i-small (+ (- (* (/ (i-large-integer)) a))
			(* (/ (i-large-integer)) b))))))

(defthm find-max-rcfn-2-is-maximum-of-standard
  (implies (and (standardp arg)
                (inside-interval-p a (rcfn-2-domain))
		(standardp a)
		(inside-interval-p b (rcfn-2-domain))
		(standardp b)
		(realp x) (standardp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn-2 x arg) (rcfn-2 (find-max-rcfn-2-x a b arg) arg)))
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-2-is-maximum-of-grid
			    (k (upper-bound-of-grid a x 0
						    (i-large-integer)
						    (/ (- b a)
						       (i-large-integer)))))
		 (:instance
		  rcfn-2-x-close-to-rcfn-2-upper-bound-of-grid-better
		  (n (i-large-integer))
		  (eps (/ (- b a) (i-large-integer)))
		  (i 0)))
	   :in-theory
	   (disable
	    rcfn-2-x-close-to-rcfn-2-upper-bound-of-grid-better
	    find-max-rcfn-2-is-maximum-of-grid
	    small-<-non-small
	    limited-integers-are-standard))))

;; So now, we "transfer" that result to *all* values of x in [a,b].
;; What we have is that for all x in [a,b], (rcfn-2 max arg) >= (rcfn-2 x arg)
;; and that max is in [a,b].  This is the "maximum theorem".

(defthm-std find-max-rcfn-2-is-maximum
  (implies (and (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn-2 x arg) (rcfn-2 (find-max-rcfn-2-x a b arg) arg)))
  :hints (("Goal"
	   :in-theory (disable find-max-rcfn-2-x))))

;; Now we do it with quantifiers

(defun-sk is-maximum-point-2 (a b max arg)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn-2 x arg) (rcfn-2 max arg)))))

(defun-sk achieves-maximum-point-2 (a b arg)
  (exists (max)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp max)
			(<= a max)
			(<= max b)
			(is-maximum-point-2 a b max arg)))))

(defthm maximum-point-2-theorem-sk
  (implies (and (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(< a b))
	   (achieves-maximum-point-2 a b arg))
  :hints (("Goal"
	   :use ((:instance achieves-maximum-point-2-suff
			    (max (find-max-rcfn-2-x a b arg)))
		 (:instance find-max-rcfn-2-is-maximum
			    (x (is-maximum-point-2-witness a b
                                                           (find-max-rcfn-2-x a b arg)
                                                           arg))))
	   :in-theory (disable achieves-maximum-point-2-suff
			       find-max-rcfn-2-is-maximum))))

;; Of course, the function also achieves its minimum.  To do that, we
;; start with the follogin function, which is similar to the "max-x-n"
;; function above.  Shouldn't ACL2 be able to do this sort of thing by
;; itself?

(defun find-min-rcfn-2-x-n (a min-x i n eps arg)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (< (rcfn-2 (+ a (* i eps)) arg) (rcfn-2 min-x arg))
	  (find-min-rcfn-2-x-n a (+ a (* i eps)) (1+ i) n eps arg)
	(find-min-rcfn-2-x-n a min-x (1+ i) n eps arg))
    min-x))

;; We have to prove that this function is limited.  Luckily, we can
;; just reuse the theorem about max-n being limited.

(defthm find-min-rcfn-2-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-min-rcfn-2-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b))
                                    arg)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-2-x-n-limited
				       (rcfn-2 (lambda (x arg)
                                                 (- (rcfn-2 x arg))))
				       (find-max-rcfn-2-x-n find-min-rcfn-2-x-n)
				       ))
	   :in-theory (disable find-max-rcfn-2-x-n-limited))))

;; That justifies the definition of min-x.

(defun-std find-min-rcfn-2-x (a b arg)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-min-rcfn-2-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))
                                   arg))
    0))

;; Now, to see that this function really returns a minimum, we just
;; have to instantiate the appropriate theorem about maximums.

(defthm find-min-rcfn-2-is-minimum
  (implies (and (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn-2 (find-min-rcfn-2-x a b arg) arg) (rcfn-2 x arg)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-2-is-maximum
				       (rcfn-2 (lambda (x arg)
                                                 (- (rcfn-2 x arg))))
				       (find-max-rcfn-2-x-n find-min-rcfn-2-x-n)
				       (find-max-rcfn-2-x find-min-rcfn-2-x)))
	   :in-theory (disable find-max-rcfn-2-is-maximum))))

;; Similarly, we want to show that a <= min-x -- just instantiate the
;; theorem about maximum!

(defthm find-min-rcfn-2-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-min-rcfn-2-x a b arg)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-2-x->=-a
				       (rcfn-2 (lambda (x arg)
                                                 (- (rcfn-2 x arg))))
				       (find-max-rcfn-2-x-n find-min-rcfn-2-x-n)
				       (find-max-rcfn-2-x find-min-rcfn-2-x)))
	   :in-theory (disable find-max-rcfn-2-x->=-a))))

;; And finally,, we want to show that min-x <= b -- again, just
;; instantiate the theorem about maximum!

(defthm find-min-rcfn-2-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-min-rcfn-2-x a b arg) b))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-2-x-<=-b
				       (rcfn-2 (lambda (x arg)
                                                 (- (rcfn-2 x arg))))
				       (find-max-rcfn-2-x-n find-min-rcfn-2-x-n)
				       (find-max-rcfn-2-x find-min-rcfn-2-x)))
	   :in-theory (disable find-max-rcfn-2-x-<=-b))))

;; And find-min is inside an interval if a and b are inside the interval

(defthm find-min-rcfn-2-x-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (find-min-rcfn-2-x a b arg) interval))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-2-x-inside-interval
				       (rcfn-2 (lambda (x arg)
                                                 (- (rcfn-2 x arg))))
				       (find-max-rcfn-2-x-n find-min-rcfn-2-x-n)
				       (find-max-rcfn-2-x find-min-rcfn-2-x)))
	   :in-theory (disable find-max-rcfn-2-x-inside-interval))))

;; Now we do it with quantifiers

(defun-sk is-minimum-point-2 (a b min arg)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn-2 min arg) (rcfn-2 x arg)))))

(defun-sk achieves-minimum-point-2 (a b arg)
  (exists (min)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp min)
			(<= a min)
			(<= min b)
			(is-minimum-point-2 a b min arg)))))

(defthm minimum-point-2-theorem-sk
  (implies (and (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(< a b))
	   (achieves-minimum-point-2 a b arg))
  :hints (("Goal"
	   :use ((:instance achieves-minimum-point-2-suff
			    (min (find-min-rcfn-2-x a b arg)))
		 (:instance find-min-rcfn-2-is-minimum
			    (x (is-minimum-point-2-witness a b
                                                           (find-min-rcfn-2-x a b arg)
                                                           arg))))
	   :in-theory (disable achieves-minimum-point-2-suff
			       find-min-rcfn-2-is-minimum))))

