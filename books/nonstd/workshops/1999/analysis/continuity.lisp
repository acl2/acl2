(in-package "ACL2")

;; This book establishes some facts about real continuous functions.
;; First, it shows that a function that is continuous on a closed
;; interval is uniformly continuous.  Second, it proves the
;; intermediate value theorem.  Last, it proves the extreme-value
;; theorems; i.e., a continuous function achieves its maximum and
;; minimum over a closed interval.

(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "arithmetic/top" :dir :system)
(include-book "arithmetic/realp" :dir :system)

;; First, we introduce rcfn - a Real Continuous FunctioN of a single
;; argument.  It is assumed to return standard values for standard
;; arguments, and to satisfy the continuity criterion.

(encapsulate
 ((rcfn (x) t))

 ;; Our witness continuous function is the identity function.

 (local (defun rcfn (x) x))

 ;; The function returns standard values for standard arguments.

 (defthm rcfn-standard
   (implies (standard-numberp x)
	    (standard-numberp (rcfn x)))
   :rule-classes (:rewrite :type-prescription))

 ;; For real arguments, the function returns real values.

 (defthm rcfn-real
   (implies (realp x)
	    (realp (rcfn x)))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y is a real close to x, then rcfn(x)
 ;; is close to rcfn(y).

 (defthm rcfn-continuous
   (implies (and (standard-numberp x)
		 (realp x)
		 (i-close x y)
		 (realp y))
	    (i-close (rcfn x) (rcfn y))))
 )

;; First, we have a simple lemma.  If x is limited, then
;; standard_part(x) is close to x.

(local
 (defthm standard-part-close
   (implies (i-limited x)
	    (i-close (standard-part x) x))
   :hints (("Goal"
	    :use ((:instance i-small-non-standard-part))
	    :in-theory (enable-disable (i-close i-small)
				       (i-small-non-standard-part))))))

;; Now, we show that Rcfn is uniformly continuous.  Note, this only
;; holds for limited x.  I.e., x is in the interval [-M,M] where M is
;; some standard real M.  But then, Rcfn is continuous on [-M,M], and
;; so its uniformly continuous on [-M,M] -- in particular, its
;; uniformly continuous around x.

(defthm rcfn-uniformly-continuous
  (implies (and (i-limited x)
		(realp x)
		(i-close x y)
		(realp y))
	   (i-close (rcfn x) (rcfn y)))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (x (standard-part x))
			    (y x))
		 (:instance rcfn-continuous
			    (x (standard-part x))
			    (y y))
		 (:instance i-close-transitive
			    (x (standard-part x))
			    (y x)
			    (z y))
		 (:instance i-close-transitive
			    (x (rcfn x))
			    (y (rcfn (standard-part x)))
			    (z (rcfn y)))
		 (:instance i-close-symmetric
			    (x (rcfn (standard-part x)))
			    (y (rcfn x))))
	   :in-theory (disable rcfn-continuous i-close-transitive
			       i-close-symmetric))))

;; This doesn't belong here.  It should be moved over to nsa.lisp, and
;; probably written as (equal (equal (stdpt x) (stdpt y)) t) instead.
;; It could be a dangerous lemma if it tries to rewrite all
;; occurrences of standard-part!

#|
;; Note: This was moved to nsa.lisp
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

;; But using that lemma, we can prove that (rcfn (std-pt x)) is equal
;; to (std-pt (rcfn x)) -- the reason is that x is close to its
;; std-pt, and since rcfn is continuous, that means (rcfn x) is to
;; close to the (rcfn (std-pt x)).  The last one is known to be
;; standard (by an encapsulate hypothesis), so it must be the
;; standard-part of (rcfn x).

(defthm rcfn-standard-part
  (implies (and (realp x)
		(i-limited x))
	   (equal (rcfn (standard-part x))
		  (standard-part (rcfn x))))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (x (standard-part x))
			    (y x))
		 (:instance close-x-y->same-standard-part
			    (x (RCFN (STANDARD-PART X)))
			    (y (RCFN X))))
	   :in-theory (enable-disable (standards-are-limited)
				      (rcfn-continuous
				       close-x-y->same-standard-part)))))

; This function finds the largest a+i*eps so that f(a+i*eps)<z.

(defun find-zero-n (a z i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (realp a)
	   (integerp i)
	   (integerp n)
	   (< i n)
	   (realp eps)
	   (< 0 eps)
	   (< (rcfn (+ a eps)) z))
      (find-zero-n (+ a eps) z (1+ i) n eps)
    (realfix a)))

;; We prove that f(a+i*eps)<z for the i chosen above.

(defthm rcfn-find-zero-n-<-z
  (implies (and (realp a) (< (rcfn a) z))
	   (< (rcfn (find-zero-n a z i n eps)) z)))

;; Moreover, we show that f(a+i*eps+eps) >= z, so that the i chosen by
;; find-zero-n is the largest possible.

(defthm rcfn-find-zero-n+eps->=-z
  (implies (and (realp a)
		(integerp i)
		(integerp n)
		(< i n)
		(realp eps)
		(< 0 eps)
		(< (rcfn a) z)
		(< z (rcfn (+ a (* (- n i) eps)))))
	   (<= z (rcfn (+ (find-zero-n a z i n eps)
			  eps)))))

;; The root found by find-zero-n is at least equal to a.

(defthm find-zero-n-lower-bound
  (implies (and (realp a) (realp eps) (< 0 eps))
	   (<= a (find-zero-n a z i n eps))))

;; Moreover, the root found by find-zero-n can't be any larger than
;; b-eps.  That means it must be in the range [a,b)

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (realp a)
		  (realp x))
	     (equal (<= a (+ a x))
		    (<= 0 x)))))

 (defthm find-zero-n-upper-bound
   (implies (and (realp a)
		 (integerp i)
		 (integerp n)
		 (<= 0 i)
		 (<= i n)
		 (realp eps)
		 (< 0 eps))
	    (<= (find-zero-n a z i n eps)
		(+ a (* (- n i) eps))))
   :hints (("Subgoal *1/6.1"
	    :use ((:instance lemma-1
			     (x (* (- n i) eps))))
	    :in-theory (disable lemma-1))))
 )

;; Now, if a and b are limited and a<=x<=b, then x is limited.  This
;; routine should probably go in nsa.lisp.

#|
Note: This has moved to nsa.lisp

(local
 (defthm limited-squeeze
   (implies (and (realp a) (realp b) (realp x)
		 (<= a x) (<= x b)
		 (i-limited a) (i-limited b))
	    (i-limited x))
   :hints (("Goal"
	    :use ((:instance large-if->-large
			     (x x)
			     (y a))
		  (:instance large-if->-large
			     (x x)
			     (y b)))
	    :in-theory (enable-disable (abs) (large-if->-large))))))
|#

(encapsulate
 ()

 (local
  (defthm lemma-0
    (implies (and (realp a)
		  (realp x)
		  (<= 0 x))
	     (not (< (+ a x) a)))))

 (local
  (defthm lemma-1
    (implies (and (realp a) (i-limited a)
		  (realp b) (i-limited b)
		  (integerp i) (integerp n)
		  (<= 0 i) (<= i n)
		  (<= (+ a (* (+ n (- i)) eps)) b)
		  (realp eps)
		  (< 0 eps))
	     (i-limited (+ a (* (+ n (- i)) eps))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance limited-squeeze
			      (x (+ a (* (- n i) eps)))))
	     :in-theory (disable distributivity limited-squeeze))
	    ("Goal'''"
	     :use ((:instance lemma-0
			      (x (* EPS (+ (- I) N))))))
	    )))

 (defthm limited-find-zero-n
   (implies (and (realp a) (i-limited a)
		 (realp b) (i-limited b)
		 (integerp i) (integerp n)
		 (<= 0 i) (<= i n)
		 (<= (+ a (* (+ n (- i)) eps)) b)
		 (realp eps)
		 (< 0 eps))
	    (i-limited (find-zero-n a z i n eps)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance find-zero-n-lower-bound)
		  (:instance find-zero-n-upper-bound)
		  (:instance lemma-1)
		  (:instance limited-squeeze
			     (x (find-zero-n a z i n eps))
			     (b (+ a (* (- n i) eps)))))
	    :in-theory (disable lemma-1
				find-zero-n-lower-bound
				find-zero-n-upper-bound
				large-if->-large
				limited-squeeze))))
 )

;; Specifically, the invocation of find-zero-n in find-zero is
;; i-limited

(encapsulate
 ()

 ;; First, we need to show what happens to find-zero-n when  the range
 ;; [a,b] is void.

 (local
  (defthm lemma-1
    (implies (and (<= b a) (realp b))
	     (equal (FIND-ZERO-N A Z 0 (I-LARGE-INTEGER)
				 (+ (- (* (/ (I-LARGE-INTEGER)) A))
				    (* (/ (I-LARGE-INTEGER)) B)))
		    (realfix a)))
    :hints (("Goal"
	     :expand ((FIND-ZERO-N A Z 0 (I-LARGE-INTEGER)
				   (+ (- (* (/ (I-LARGE-INTEGER)) A))
				      (* (/ (I-LARGE-INTEGER)) B)))))
	    ("Goal'"
	     :use ((:instance <-*-left-cancel
			      (z (/ (i-large-integer)))
			      (x a)
			      (y b)))
	     :in-theory (disable <-*-left-cancel
				 <-*-/-LEFT-COMMUTED
				 /-cancellation-on-left)))))

 ;; Silly simplification!  N+0=N

 (local
  (defthm lemma-2
    (equal (+ (i-large-integer) 0) (i-large-integer))))

 ;; And, N*x/N = x.

 (local
  (defthm lemma-3
    (equal (* (i-large-integer) x (/ (i-large-integer))) (fix x))))

 ;; Now, it's possible to show that find-zero-n is limited!

 (defthm limited-find-zero-body
   (implies (and (i-limited a)
		 (i-limited b)
		 (realp b))
	    (i-limited (find-zero-n a
				    z
				    0
				    (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
   :hints (("Goal"
	    :cases ((and (realp a) (< a b))))
	   ("Subgoal 1"
	    :use ((:instance limited-find-zero-n
			     (i 0)
			     (n (i-large-integer))
			     (eps (/ (- b a) (i-large-integer)))))
	    :in-theory (disable limited-find-zero-n))))
 )

;; And now, here's a routine that finds a "zero" in a given [a,b]
;; range.

(defun-std find-zero (a b z)
  (if (and (realp a)
	   (realp b)
	   (realp z)
	   (< a b))
      (standard-part
       (find-zero-n a
		    z
		    0
		    (i-large-integer)
		    (/ (- b a) (i-large-integer))))
    0))

;; Again, find-zero returns a root r so that f(r) <= z.

(defthm-std rcfn-find-zero-<=-z
  (implies (and (realp a)
		(realp b)
		(< a b)
		(realp z)
		(< (rcfn a) z))
	   (<= (rcfn (find-zero a b z)) z))
  :hints (("Goal"
	   :use ((:instance standard-part-<-2
			    (x z)
			    (y (rcfn (find-zero-n a z 0
						  (i-large-integer)
						  (+ (- (* (/ (i-large-integer)) a))
						     (* (/
							 (i-large-integer)) b))))))
		 (:instance rcfn-find-zero-n-<-z
			    (i 0)
			    (n (i-large-integer))
			    (eps (+ (- (* (/ (i-large-integer)) a))
				    (* (/ (i-large-integer)) b)))))
	   :in-theory (disable rcfn-find-zero-n-<-z))))

;; We need to know that if x is limited, so is (rcfn x)

(defthm rcfn-limited
  (implies (and (realp x)
		(i-limited x))
	   (i-limited (rcfn x)))
  :hints (("Goal"
	   :use ((:instance i-close-limited
			    (x (rcfn (standard-part x)))
			    (y (rcfn x)))
		 (:instance rcfn-continuous
			    (x (standard-part x))
			    (y x)))
	   :in-theory (enable-disable (standards-are-limited)
				      (i-close-limited
				       rcfn-continuous
				       rcfn-standard-part
                                       ;; added for v2-6:
                                       rcfn-uniformly-continuous)))))

;; We'll show that f(r+eps) >= z, so that the r found above is the
;; largest possible (within an eps resolution).

(encapsulate
 ()

 ;; First, a quick lemma: N+0 = N.

 (local
  (defthm lemma-1
    (equal (+ (i-large-integer) 0) (i-large-integer))))

 ;; Also, N*x/N = x.

 (local
  (defthm lemma-2
    (equal (* (i-large-integer) x (/ (i-large-integer))) (fix x))))

 ;; This silly rule lets us know that x is close to x+eps!

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (i-limited x)
		  (realp eps)
		  (i-small eps))
	     (i-close x (+ eps x)))
    :hints (("Goal" :in-theory (enable i-small i-close)))))

 ;; This horrible technical lemma simply gets rid of the +eps part of
 ;; (standard-part (rcfn (+ eps (find-zero-n ....)))) It follows,
 ;; simply, from the fact that eps is small and rcfn is uniformly
 ;; continuous, so (rcfn (+ eps (find-zero-n ...))) is close to (rcfn
 ;; (find-zero-n ...)).

 (local
  (defthm lemma-4
    (implies (and (realp a) (standard-numberp a)
		  (realp b) (standard-numberp b)
		  (< a b)
		  (standard-numberp z)
		  (< (rcfn a) z)
		  (< z (rcfn b)))
	     (equal (standard-part
		     (rcfn (+ (- (* (/ (i-large-integer)) a))
			      (* (/ (i-large-integer)) b)
			      (find-zero-n a z 0 (i-large-integer)
					   (+ (- (* (/ (i-large-integer)) a))
					      (* (/ (i-large-integer)) b))))))
		    (standard-part
		     (rcfn (find-zero-n a z 0 (i-large-integer)
					(+ (- (* (/ (i-large-integer)) a))
					   (* (/ (i-large-integer))
					      b)))))))
    :hints (("Goal"
	     :use ((:instance close-x-y->same-standard-part
			      (x (rcfn (find-zero-n a z 0 (i-large-integer)
						    (+ (- (* (/ (i-large-integer)) a))
						       (* (/ (i-large-integer))
							  b)))))
			      (y (rcfn (+ (- (* (/ (i-large-integer)) a))
					  (* (/ (i-large-integer)) b)
					  (find-zero-n a z 0 (i-large-integer)
						       (+ (- (* (/ (i-large-integer)) a))
							  (* (/ (i-large-integer))
							     b)))))))
		   (:instance rcfn-uniformly-continuous
			      (x (find-zero-n a z 0 (i-large-integer)
						    (+ (- (* (/ (i-large-integer)) a))
						       (* (/ (i-large-integer))
							  b))))
			      (y (+ (- (* (/ (i-large-integer)) a))
					  (* (/ (i-large-integer)) b)
					  (find-zero-n a z 0 (i-large-integer)
						       (+ (- (* (/ (i-large-integer)) a))
							  (* (/ (i-large-integer))
							     b))))))
		   (:instance lemma-3
			      (x (find-zero-n a z 0 (i-large-integer)
                                (+ (- (* (/ (i-large-integer)) a))
                                   (* (/ (i-large-integer)) b))))
			      (eps (+ (- (* (/ (i-large-integer)) a))
				      (* (/ (i-large-integer)) b)))))
	     :in-theory (disable close-x-y->same-standard-part
				 rcfn-uniformly-continuous
				 lemma-3)))))

 ;; And now, f(r+eps) >= z.

 (defthm-std rcfn-find-zero->=-z
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (realp z)
		 (< (rcfn a) z)
		 (< z (rcfn b)))
	    (<= z (rcfn (find-zero a b z))))
   :hints (("Goal"
	    :use ((:instance rcfn-find-zero-n+eps->=-z
			     (n (i-large-integer))
			     (i 0)
			     (eps (/ (- b a) (i-large-integer))))
		  (:instance standard-part-<=
			     (x z)
			     (y (RCFN (+ (- (* (/ (I-LARGE-INTEGER)) A))
					 (* (/ (I-LARGE-INTEGER)) B)
					 (FIND-ZERO-N A Z 0 (I-LARGE-INTEGER)
						      (+ (- (* (/ (I-LARGE-INTEGER)) A))
							 (* (/ (I-LARGE-INTEGER)) B)))))))
		  )
	    :in-theory (disable rcfn-find-zero-n+eps->=-z
				standard-part-<=))))
 )

;; Next, we prove that (find-zero a b z) is in the range (a,b)

(encapsulate
 ()

 ;; First, if a and b are standard, (b-a)/N is small, for N a large
 ;; integer.

 (local
  (defthm lemma-1
    (implies (and (standard-numberp a)
		  (standard-numberp b))
	     (i-small (/ (- b a) (i-large-integer))))))

 ;; Silly algebra!  a<=a+x if and only if 0<=x....

 (local
  (defthm lemma-2
    (implies (and (realp a)
		  (realp x))
	     (equal (<= a (+ a x))
		    (<= 0 x)))))

 ;; Now, we find an upper bound for the root returned by find-zero-n.

 (local
  (defthm lemma-3
    (implies (and (realp a)
		  (integerp i)
		  (integerp n)
		  (<= 0 i)
		  (<= i n)
		  (realp eps)
		  (< 0 eps))
	     (<= (find-zero-n a z i n eps)
		 (+ a (* (- n i) eps))))
    :hints (("Subgoal *1/6.1"
	     :use ((:instance lemma-2
			      (x (* (- n i) eps))))
	     :in-theory (disable lemma-2)))))

 ;; Silly simplification!  N+0=N

 (local
  (defthm lemma-4
    (equal (+ (i-large-integer) 0) (i-large-integer))))

 ;; And, N*x/N = x.

 (local
  (defthm lemma-5
    (equal (* (i-large-integer) x (/ (i-large-integer))) (fix x))))

 ;; A simple consequence is that the root found by find-zero(a,b,z) is
 ;; at most b.

 (local
  (defthm-std find-zero-upper-bound
    (implies (and (realp a) (realp b) (realp z)
		  (< a b))
	     (<= (find-zero a b z) b))
    :hints (("Goal"
	     :use ((:instance lemma-3
			      (i 0)
			      (n (i-large-integer))
			      (eps (/ (- b a) (i-large-integer))))
		   (:instance standard-part-<=
			      (x (find-zero-n a z 0 (i-large-integer)
					      (/ (- b a)
						 (i-large-integer))))
			      (y b)))
	     :in-theory (disable lemma-3
				 standard-part-<=)))))

 ;; Similarly, find-zero-n finds a root at least equal to a.

 (local
  (defthm lemma-7
    (implies (and (realp a) (realp eps) (< 0 eps))
	     (<= a (find-zero-n a z i n eps)))))

 ;; And that means find-zero finds a root at least a.

 (local
  (defthm-std find-zero-lower-bound
    (implies (and (realp a) (realp b) (realp z) (< a b))
	     (<= a (find-zero a b z)))
    :hints (("Goal"
	     :use ((:instance standard-part-<=
			      (x a)
			      (y (find-zero-n a z 0 (i-large-integer)
					      (/ (- b a)
						 (i-large-integer))))))
	     :in-theory (disable standard-part-<=)))))

 ;; And here is the intermediate value theorem.

 (defthm intermediate-value-theorem
   (implies (and (realp a)
		 (realp b)
		 (realp z)
		 (< a b)
		 (< (rcfn a) z)
		 (< z (rcfn b)))
	    (and (realp (find-zero a b z))
		 (< a (find-zero a b z))
		 (< (find-zero a b z) b)
		 (equal (rcfn (find-zero a b z))
			z)))
   :hints (("Goal"
	    :use ((:instance rcfn-find-zero-<=-z)
		  (:instance rcfn-find-zero->=-z)
		  (:instance find-zero-lower-bound)
		  (:instance find-zero-upper-bound))
	    :in-theory (disable find-zero
				find-zero-lower-bound
				find-zero-upper-bound
				rcfn-find-zero-<=-z
				rcfn-find-zero->=-z))))
 )

