#|

This book finds the maximum point of a continuous function in a
closed interval.

|#

(in-package "ACL2")

(include-book "continuity")

#|

;; This doesn't belong here.  It should be moved over to nsa.lisp, and
;; probably written as (equal (equal (stdpt x) (stdpt y)) t) instead.
;; It could be a dangerous lemma if it tries to rewrite all
;; occurrences of standard-part!

;; Note: It has been moved to nsa.lisp

(local
 (defthm close-x-y->same-standard-part
   (implies (and (i-close x y)
		 (i-limited x))
	    (equal (standard-part x) (standard-part y)))
   :hints (("Goal"
	    :use ((:instance i-close-limited))
	    :in-theory (enable-disable (i-close i-small)
				       (i-close-limited))))))
|#

;; The task is to prove the maximal theorem.  The approach is similar
;; to the intermediate-value theorem.  First, we define a function
;; that splits up the interval [a,b] into a grid of size eps and then
;; we find the maximum of the function at the points in the grid.

(defun find-max-rcfn-x-n (a max-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (> (rcfn (+ a (* i eps))) (rcfn max-x))
	  (find-max-rcfn-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-max-rcfn-x-n a max-x (1+ i) n eps))
    max-x))

;; Since the function above takes in a "max-so-far" argument, it is
;; important to note that the initial value of max-so-far is a lower
;; bound for the maximum.

(defthm find-max-rcfn-x-n-is-monotone
  (<= (rcfn max-x) (rcfn (find-max-rcfn-x-n a max-x i n eps))))

;; Now, we can say that the maximum returned really is the maximum of
;; all the f(x) values at the points x on the grid.

(defthm find-max-rcfn-x-n-is-maximum
  (implies (and (integerp i)
		(integerp k)
		(integerp n)
		(<= 0 i)
		(<= i k)
		(<= k n)
		(realp a)
		(realp eps)
		(< 0 eps))
	   (<= (rcfn (+ a (* k eps)))
	       (rcfn (find-max-rcfn-x-n a max-x i n eps))))
  :hints (("Subgoal *1/7"
	   :use ((:instance find-max-rcfn-x-n-is-monotone))
	   :in-theory (disable find-max-rcfn-x-n-is-monotone))))

;; Naturally, we want to prove that the x value returned for the
;; maximum is in the interval [a,b].  First, we show that it's at most
;; b.  Notice we need to assume the starting value of max-x is less
;; than b!

(defthm find-max-rcfn-x-n-upper-bound
  (implies (and (<= max-x (+ a (* n eps)))
		(realp a)
		(realp eps)
		(integerp i)
		(integerp n)
		(< 0 eps))
	   (<= (find-max-rcfn-x-n a max-x i n eps) (+ a (* n eps))))
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

;; To show that find-max-rcfn-x-n returns a value that is not less
;; than a, we need a simple lemma to do the induction at each of the
;; points in the grid.

(defthm find-max-rcfn-x-n-lower-bound-lemma
  (implies (<= max-x (+ a (* i eps)))
	   (<= max-x (find-max-rcfn-x-n a max-x i n eps))))

;; Now, we can fix the lower range of find-max-x-r-n

(defthm find-max-rcfn-x-n-lower-bound
  (<= a (find-max-rcfn-x-n a a 0 n eps))
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-x-n-lower-bound-lemma
			    (max-x a)
			    (i 0)))
	   :in-theory (disable find-max-rcfn-x-n-lower-bound-lemma))))

;; Next, we would like to use defun-std to introduce find-max-x.
;; Before that, we have to show that find-max-x-n is i-limited.  This
;; is simple, since we know it's in the range [a,b] and b is limited.

(defthm find-max-rcfn-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-max-rcfn-x-n a a
                                         0 (i-large-integer)
                                         (+ (- (* (/ (i-large-integer)) a))
                                            (* (/ (i-large-integer)) b)))))
  ;; Slight change in hint structure needed for v2-8.
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-x-n-upper-bound
			    (max-x a)
			    (n (i-large-integer))
			    (eps (/ (- b a) (i-large-integer)))
			    (i 0))
		 (:instance
                  (:theorem
                   (implies (and (realp a)
                                 (realp b)
                                 (realp x)
                                 (i-limited a)
                                 (i-limited b)
                                 (<= a x)
                                 (<= x b))
                            (i-limited x)))
                  (x (find-max-rcfn-x-n a a 0 (i-large-integer)
                                        (+ (- (* (/ (i-large-integer)) a))
                                           (* (/ (i-large-integer))
                                              b)))))))
	  ("Subgoal 1"
	   :use ((:instance large-if->-large
			    (x x)
			    (y (if (< (abs a) (abs b))
				   (abs b)
				 (abs a)))))
	   :in-theory (disable large-if->-large))))

;; And now we can introduce the function find-max-rcfn-x which (we
;; claim) finds the point x in [a,b] at which (rcfn x) achieves a
;; maximum.

(defun-std find-max-rcfn-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-max-rcfn-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))
    0))

;; So first, let's do the easy part of the claim, namely that the x
;; returned by find-max satisfies a <= x.

(defthm-std find-max-rcfn-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-max-rcfn-x a b)))
  :hints (("Goal'"
	   :use ((:instance standard-part-<=
			    (x a)
			    (y (find-max-rcfn-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))))
	   :in-theory (disable standard-part-<=))))

;; Similarly, that x satisfies x <= b, so x is in [a, b].

(defthm-std find-max-rcfn-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-max-rcfn-x a b) b))
; Matt K. v7-1 mod for ACL2 mod on 2/13/2015: "Goal''" changed to "Goal'".
  :hints (("Goal'"
	   :use ((:instance standard-part-<=
			    (x (find-max-rcfn-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))
			    (y b))
		 (:instance find-max-rcfn-x-n-upper-bound
			    (max-x a)
			    (i 0)
			    (n (i-large-integer))
			    (eps (/ (- b a) (i-large-integer))))

		 )
	   :in-theory (disable standard-part-<=)))
)

;; OK now, (rcfn max) should be the maximum at all the grid points,
;; modulo standard-part.  Why?  Because max is (std-pt max-n).  By
;; construction, max-n is the maximum of all grid-points.  But, (rcfn
;; max) and (rcfn max-n) are close to each other, since rcfn is
;; continuous. Also, (rcfn max) is standard, since max is standard, so
;; (rcfn max) = (std-pt (rcfn max-n)) >= (std-pt (rcfn x_i)) where x_i
;; is any point in the grid.

(defthm find-max-rcfn-is-maximum-of-grid
  (implies (and (realp a) (standard-numberp a)
		(realp b) (standard-numberp b)
		(< a b)
		(integerp k)
		(<= 0 k)
		(<= k (i-large-integer)))
	   (<= (standard-part (rcfn (+ a (* k (/ (- b a)
						 (i-large-integer))))))
	       (rcfn (find-max-rcfn-x a b))))
  :hints (("Goal"
	   :use ((:instance standard-part-<=
			    (x (rcfn (+ a (* k (/ (- b a)
						  (i-large-integer))))))
			    (y (rcfn
				      (find-max-rcfn-x-n a a 0
						    (i-large-integer)
						    (/ (- b a)
						       (i-large-integer))))))
		 (:instance find-max-rcfn-x-n-is-maximum
			    (i 0)
			    (n (i-large-integer))
			    (eps (/ (- b a) (i-large-integer)))
			    (max-x a)))
	   :in-theory (disable standard-part-<=
			       find-max-rcfn-x-n-is-maximum))))

;; Now, we know the maximum we found really is the maximum at all the
;; grid points.  But what about an arbitrary x in [a,b]?  What we'll
;; do is to find where x falls in the grid.  I.e., we want the i so
;; that x is in [x_{i-1},x_i].  What we'll know is that (rcfn x) is
;; the standard-part of (rcfn x_i), since x and x_i are close to each
;; other and x is standard.  But then, since we know that (rcfn max)
;; is >= (std-pt (rcfn x_i)) = (rcfn x) we have that max really is the
;; maximum for all x.

;; But wait!  That's not quite true.  The equality (std-pt (rcfn x_i)) =
;; (rcfn x) only holds when x is standard!  So what this argument does
;; is prove that (rcfn max) >= (rcfn x) for all standard x.  To finish
;; up the proof, we need to appeal to the transfer principle!

;; First, we define the function that finds the right index i.

(defun upper-bound-of-grid (a x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (< i n)
	   (<= (+ a (* i eps)) x))
      (upper-bound-of-grid a x (1+ i) n eps)
    i))

;; This seems obvious -- why didn't ACL2 figure it out by itself? --
;; but the index returned is a real number.

(defthm realp-upper-bound-of-grid
  (implies (realp i)
	   (realp (upper-bound-of-grid a x i n eps))))

;; More precisely, it's an _integer_.

(defthm integerp-upper-bound-of-grid
  (implies (integerp i)
	   (integerp (upper-bound-of-grid a x i n eps))))

;; OK now, the index found is at least equal to the starting index....

(defthm upper-bound-of-grid-lower-bound
  (<= i (upper-bound-of-grid a x i n eps)))

;; ...and it's at most the final index.

(defthm upper-bound-of-grid-upper-bound
  (implies (<= i n)
	   (<= (upper-bound-of-grid a x i n eps) n)))

;; So now, we can show that x is in the range [x_{i-1},x_i]

(defthm x-in-upper-bound-of-grid
  (implies (and (integerp i)
		(integerp n)
		(realp eps)
		(< 0 eps)
		(realp x)
		(<= i n)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps))))
	   (and (<= (- (+ a (* (upper-bound-of-grid a x i n eps)
			       eps))
		       eps)
		    x)
		(<= x (+ a (* (upper-bound-of-grid a x i n eps)
			      eps))))))

;; The above theorem implies that when eps is small, the difference
;; between x and x_i is small (since x_{i-1} <= x <= x_i and
;; x_i-x_{i-1} = eps is small).

(defthm x-in-upper-bound-of-grid-small-eps
  (implies (and (integerp i)
		(integerp n)
		(realp eps)
		(< 0 eps)
		(realp a)
		(realp x)
		(<= i n)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps)))
		(i-small eps))
	   (i-small (- (+ a (* (upper-bound-of-grid a x i n eps)
			       eps))
		       x)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance small-if-<-small
			    (x eps)
			    (y (- (+ a (* (upper-bound-of-grid a x i n eps)
					  eps))
				  x)))
		 (:instance x-in-upper-bound-of-grid))
	   :in-theory (disable small-if-<-small
			       x-in-upper-bound-of-grid))))

;; So, we have that when eps is small, x and x_i are close to each other.

(defthm x-in-upper-bound-of-grid-small-eps-better
  (implies (and (integerp i)
		(integerp n)
		(realp eps)
		(< 0 eps)
		(realp a)
		(realp x)
		(<= i n)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps)))
		(i-small eps))
	   (i-close x
		   (+ a (* (upper-bound-of-grid a x i n eps)
			   eps))))
  :hints (("Goal"
	   :use ((:instance i-close-symmetric
			    (x (+ a (* (upper-bound-of-grid a x i n eps)
				       eps)))
			    (y x))
		 (:instance x-in-upper-bound-of-grid-small-eps))
	   :in-theory '(i-close))))

;; Since rcfn is continuous, it follows that (rcfn x) and (rcfn x_i)
;; are close to each other!

(defthm rcfn-x-close-to-rcfn-upper-bound-of-grid
  (implies (and (integerp i)
		(integerp n)
		(realp eps)
		(< 0 eps)
		(realp a)
		(realp x)
		(standard-numberp x)
		(<= i n)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps)))
		(i-small eps))
	   (i-close (rcfn x)
		    (rcfn (+ a (* (upper-bound-of-grid a x i n eps)
				  eps)))))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (y (+ a (* (upper-bound-of-grid a x i n eps)
				       eps))))
		 (:instance x-in-upper-bound-of-grid-small-eps-better))
	   :in-theory (disable rcfn-continuous
			       x-in-upper-bound-of-grid-small-eps-better
			       upper-bound-of-grid))))

;; In particular, (std-pt (rcfn x_i)) = (std-pt (rcfn x)) and when x
;; is standard that's equal to (rcfn x).

(defthm rcfn-x-close-to-rcfn-upper-bound-of-grid-better
  (implies (and (integerp i)
		(integerp n)
		(realp eps)
		(< 0 eps)
		(realp a)
		(realp x)
		(standard-numberp x)
		(<= i n)
		(<= (+ a (* i eps)) x)
		(<= x (+ a (* n eps)))
		(i-small eps))
	   (equal (standard-part (rcfn (+ a (* (upper-bound-of-grid a x i n eps)
					       eps))))
		  (rcfn x)))
  :hints (("Goal"
	   :use ((:instance rcfn-x-close-to-rcfn-upper-bound-of-grid)
		 (:instance close-x-y->same-standard-part
			    (x (rcfn x))
			    (y (rcfn (+ a (* (upper-bound-of-grid a x i n eps)
					     eps))))))
	   :in-theory (disable
		       rcfn-x-close-to-rcfn-upper-bound-of-grid
		       close-x-y->same-standard-part
		       upper-bound-of-grid))))

;; So that means that (rcfn max) >= (rcfn x), because we already know
;; that (rcfn max) >= (std-pt (rcfn x_i)) for all indices i!  That
;; only works for standard values of x.

(local
 (defthm small-range
   (implies (and (realp a) (standard-numberp a)
		 (realp b) (standard-numberp b)
		 (< a b))
	    (i-small (+ (- (* (/ (i-large-integer)) a))
			(* (/ (i-large-integer)) b))))))

(defthm find-max-rcfn-is-maximum-of-standard
  (implies (and (realp a) (standard-numberp a)
		(realp b) (standard-numberp b)
		(realp x) (standard-numberp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn x) (rcfn (find-max-rcfn-x a b))))
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-is-maximum-of-grid
			    (k (upper-bound-of-grid a x 0
						    (i-large-integer)
						    (/ (- b a)
						       (i-large-integer)))))
		 (:instance
		  rcfn-x-close-to-rcfn-upper-bound-of-grid-better
		  (n (i-large-integer))
		  (eps (/ (- b a) (i-large-integer)))
		  (i 0)))
	   :in-theory
	   (disable
	    rcfn-x-close-to-rcfn-upper-bound-of-grid-better
	    find-max-rcfn-is-maximum-of-grid
	    small-<-non-small
	    limited-integers-are-standard))))

;; So now, we "transfer" that result to *all* values of x in [a,b].
;; What we have is that for all x in [a,b], (rcfn max) >= (rcfn x) and
;; that max is in [a,b].  This is the "maximum theorem".

(defthm-std find-max-rcfn-is-maximum
  (implies (and (realp a)
		(realp b)
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn x) (rcfn (find-max-rcfn-x a b))))
  :hints (("Goal"
	   :in-theory (disable find-max-rcfn-x))))

