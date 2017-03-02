(in-package "ACL2")

;; This book establishes some facts about real continuous functions.
;; First, it shows that a function that is continuous on a closed
;; interval is uniformly continuous.  Second, it proves the
;; intermediate value theorem.  Last, it proves the extreme-value
;; theorems; i.e., a continuous function achieves its maximum and
;; minimum over a closed interval.

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nsa")
(include-book "intervals")
(include-book "arithmetic/realp" :dir :system)

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; First, we introduce rcfn - a Real Continuous FunctioN of a single
;; argument.  It is assumed to return standard values for standard
;; arguments, and to satisfy the continuity criterion.

(encapsulate
 ((rcfn (x) t)
  (rcfn-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun rcfn (x) (realfix x)))
 (local (defun rcfn-domain () (interval nil nil)))

 ;; The interval really is an interval

 (defthm intervalp-rcfn-domain
     (interval-p (rcfn-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm rcfn-domain-real
     (implies (inside-interval-p x (rcfn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm rcfn-domain-non-trivial
     (or (null (interval-left-endpoint (rcfn-domain)))
	 (null (interval-right-endpoint (rcfn-domain)))
	 (< (interval-left-endpoint (rcfn-domain))
	    (interval-right-endpoint (rcfn-domain))))
   :rule-classes nil)

 ;; The function returns real values (even for improper arguments).

 (defthm rcfn-real
     (realp (rcfn x))
   :rule-classes (:rewrite :type-prescription))

 ;; If x is a standard real and y is a real close to x, then rcfn(x)
 ;; is close to rcfn(y).

 (defthm rcfn-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (rcfn-domain))
		 (i-close x y)
		 (inside-interval-p y (rcfn-domain)))
	    (i-close (rcfn x) (rcfn y))))
 )

;; This used to be an axiom, but we can now prove it directly

(defthm-std rcfn-standard
    (implies (standardp x)
	     (standardp (rcfn x)))
  :rule-classes (:rewrite :type-prescription))


(defthm-std standardp-rcfn-domain
    (standardp (rcfn-domain))
  :rule-classes (:rewrite :type-prescription))

;; Now, we show that Rcfn is uniformly continuous when it is
;; continuous over a closed, bounded interval.

(defthm rcfn-uniformly-continuous
  (implies (and (interval-left-inclusive-p (rcfn-domain))
		(interval-right-inclusive-p (rcfn-domain))
		(inside-interval-p x (rcfn-domain))
		(i-close x y)
		(inside-interval-p y (rcfn-domain)))
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
			    (y (rcfn x)))
		 (:instance standard-part-inside-interval
			    (x x)
			    (interval (rcfn-domain)))
		 )
	   :in-theory (disable rcfn-continuous i-close-transitive
			       i-close-symmetric
			       standard-part-inside-interval))))

;; This function finds the largest a+i*eps so that f(a+i*eps)<z.

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

 (local
  (defthm lemma-2
      (IMPLIES (AND (REALP EPS)
		    (< 0 EPS)
		    (REALP X)
		    (<= 1 X))
	       (<= EPS (* EPS X)))))

 (local
  (defthm lemma-3
      (IMPLIES (AND (REALP A)
		    (REALP EPS)
		    (< 0 EPS)
		    (REALP X)
		    (<= 1 X))
	       (<= (+ A EPS) (+ A (* EPS X))))
    :hints (("Goal"
	     :use ((:instance lemma-2))
	     :in-theory (disable lemma-2 <-*-Y-X-Y)))))

 (defthm find-zero-n-upper-bound-tight
   (implies (and (realp a)
		 (integerp i)
		 (integerp n)
		 (<= 0 i)
		 (< i n)
		 (realp eps)
		 (< 0 eps)
		 ;(< (rcfn a) z)
		 (< z (rcfn (+ a (* (- n i) eps)))))
	    (<= (+ eps (find-zero-n a z i n eps))
		(+ a (* (- n i) eps))))
   :hints (("Subgoal *1/7"
	    :use ((:instance lemma-3
			     (a a)
			     (eps eps)
			     (x (- n i))
			     )))
	   ("Subgoal *1/2"
	    :use ((:instance lemma-3
			     (a a)
			     (eps eps)
			     (x (- n i))
			     )))))
 )

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

(encapsulate
 nil

 (local
  (defthm lemma-1
      (IMPLIES
       (AND (STANDARDP A)
	    (STANDARDP B)
	    (STANDARDP Z)
	    (REALP A)
	    (REALP B)
	    (REALP Z)
	    (< A B))
       (STANDARDP (STANDARD-PART (FIND-ZERO-N A Z 0 (I-LARGE-INTEGER)
					      (+ (- (* (/ (I-LARGE-INTEGER)) A))
						 (* (/ (I-LARGE-INTEGER)) B))))))
    :hints (("Goal"
	     :use (:instance limited-find-zero-body)))))

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
)

;; But using that lemma, we can prove that (rcfn (std-pt x)) is equal
;; to (std-pt (rcfn x)) -- the reason is that x is close to its
;; std-pt, and since rcfn is continuous, that means (rcfn x) is to
;; close to the (rcfn (std-pt x)).  The last one is known to be
;; standard (by an encapsulate hypothesis), so it must be the
;; standard-part of (rcfn x).

(defthm rcfn-standard-part
  (implies (and (inside-interval-p x (rcfn-domain))
		(inside-interval-p (standard-part x) (rcfn-domain))
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
				       rcfn-uniformly-continuous
				       close-x-y->same-standard-part)))))

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
				standard-part-<=))))

 ;; Similarly, find-zero-n finds a root at least equal to a.

 (local
  (defthm lemma-7
    (implies (and (realp a) (realp eps) (< 0 eps))
	     (<= a (find-zero-n a z i n eps)))))

 ;; And that means find-zero finds a root at least a.

 (defthm-std find-zero-lower-bound
     (implies (and (realp a) (realp b) (realp z) (< a b))
	      (<= a (find-zero a b z)))
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			     (x a)
			     (y (find-zero-n a z 0 (i-large-integer)
					     (/ (- b a)
						(i-large-integer))))))
	    :in-theory (disable standard-part-<=))))

 )

(defthm find-zero-inside-interval
    (implies (and (inside-interval-p a (rcfn-domain))
		  (inside-interval-p b (rcfn-domain))
		  (< a b)
		  (realp z))
	     (inside-interval-p (find-zero a b z) (rcfn-domain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (find-zero a b z))
			    (interval (rcfn-domain)))
		 (:instance find-zero-lower-bound)
		 (:instance find-zero-upper-bound))
	   :in-theory (disable inside-interval-p-squeeze find-zero-lower-bound find-zero-upper-bound))))

(defthm find-zero-n-inside-interval
    (implies (and (inside-interval-p a (rcfn-domain))
		  (integerp i)
		  (integerp n)
		  (<= 0 i)
		  (<= i n)
		  (realp eps)
		  (< 0 eps)
		  (inside-interval-p (+ A (* (- N I) EPS)) (rcfn-domain)))
	     (inside-interval-p (FIND-ZERO-N A Z I N EPS) (rcfn-domain)))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b (+ A (* (- N I) EPS)))
			    (c (find-zero-n a z i n eps))
			    (interval (rcfn-domain)))
		 (:instance find-zero-n-lower-bound)
		 (:instance find-zero-n-upper-bound))
	   :in-theory (disable inside-interval-p-squeeze find-zero-n-lower-bound find-zero-n-upper-bound))))

;; Again, find-zero returns a root r so that f(r) <= z.

(defthm-std rcfn-find-zero-<=-z
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
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
				    (* (/ (i-large-integer)) b))))
		 (:instance find-zero-n-lower-bound
			    (i 0)
			    (n (i-large-integer))
			    (eps (+ (- (* (/ (i-large-integer)) a))
				    (* (/ (i-large-integer)) b))))
		 (:instance find-zero-n-upper-bound
			    (i 0)
			    (n (i-large-integer))
			    (eps (+ (- (* (/ (i-large-integer)) a))
				    (* (/ (i-large-integer)) b))))
		 (:instance find-zero-n-inside-interval
			    (i 0)
			    (n (i-large-integer))
			    (eps (+ (- (* (/ (i-large-integer)) a))
				    (* (/ (i-large-integer)) b))))
		 (:instance INSIDE-INTERVAL-P-SQUEEZE
			    (interval (rcfn-domain))
			    (a a)
			    (b b)
			    (c (find-zero-n a z 0
					    (i-large-integer)
					    (+ (- (* (/ (i-large-integer)) a))
					       (* (/
						   (i-large-integer)) b)))))
		 (:instance INSIDE-INTERVAL-P-SQUEEZE
			    (interval (rcfn-domain))
			    (a a)
			    (b b)
			    (c (standard-part
				(find-zero-n a z 0
					     (i-large-integer)
					     (+ (- (* (/ (i-large-integer)) a))
						(* (/
						    (i-large-integer)) b))))))
		 (:instance limited-squeeze
			    (a a)
			    (b b)
			    (x (find-zero-n a z 0
					    (i-large-integer)
					    (+ (- (* (/ (i-large-integer)) a))
					       (* (/
						   (i-large-integer)) b)))))
		 (:instance rcfn-standard-part
			    (x (find-zero-n a z 0
					    (i-large-integer)
					    (+ (- (* (/ (i-large-integer)) a))
					       (* (/
						   (i-large-integer)) b)))))
		 (:instance STANDARD-PART-<=
			    (x a)
			    (y (find-zero-n a z 0
					    (i-large-integer)
					    (+ (- (* (/ (i-large-integer)) a))
					       (* (/
						   (i-large-integer)) b)))))
		 (:instance STANDARD-PART-<=
			    (x (find-zero-n a z 0
					    (i-large-integer)
					    (+ (- (* (/ (i-large-integer)) a))
					       (* (/
						   (i-large-integer)) b))))
			    (y b))
		 )
	   :in-theory (disable rcfn-find-zero-n-<-z find-zero-n-inside-interval inside-interval-p-squeeze find-zero-n-lower-bound find-zero-n-upper-bound limited-squeeze limited-find-zero-body limited-find-zero-n rcfn-standard-part standard-part-<=))))

;; We need to know that if x is limited, so is (rcfn x)

(defthm rcfn-limited
  (implies (and (interval-left-inclusive-p (rcfn-domain))
		(interval-right-inclusive-p (rcfn-domain))
		(inside-interval-p x (rcfn-domain))
		(i-limited x))
	   (i-limited (rcfn x)))
  :hints (("Goal"
	   :use ((:instance i-close-limited
			    (x (rcfn (standard-part x)))
			    (y (rcfn x)))
		 (:instance rcfn-continuous
			    (x (standard-part x))
			    (y x))
		 (:instance standard-part-inside-interval
			    (x x)
			    (interval (rcfn-domain)))
		 )
	   :in-theory (enable-disable (standards-are-limited)
				      (i-close-limited
				       rcfn-continuous
				       rcfn-standard-part
				       standard-part-inside-interval
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
 ;; (standard-part (rcfn `(+ eps (find-zero-n ....)))) It follows,
 ;; simply, from the fact that eps is small and rcfn is uniformly
 ;; continuous, so (rcfn (+ eps (find-zero-n ...))) is close to (rcfn
 ;; (find-zero-n ...)).

 (local
  (defthm lemma-4
    (implies (and (interval-left-inclusive-p (rcfn-domain))
		  (interval-right-inclusive-p (rcfn-domain))
		  (inside-interval-p a (rcfn-domain)) ;(standardp a)
		  (inside-interval-p b (rcfn-domain)) ;(standardp b)
		  (< a b)
		  (realp z) ;(standardp z)
		  (< (rcfn a) z)
		  (< z (rcfn b)))
	     (inside-interval-p (find-zero-n a z 0 (i-large-integer)
						    (+ (- (* (/ (i-large-integer)) a))
						       (* (/ (i-large-integer))
							  b)))
				(rcfn-domain)))))


 (local
  (defthm lemma-5
    (implies (and (interval-left-inclusive-p (rcfn-domain))
		  (interval-right-inclusive-p (rcfn-domain))
		  (inside-interval-p a (rcfn-domain)) ;(standardp a)
		  (inside-interval-p b (rcfn-domain)) ;(standardp b)
		  (< a b)
		  (realp z) ;(standardp z)
		  (< (rcfn a) z)
		  (< z (rcfn b)))
	     (inside-interval-p (+ (- (* (/ (i-large-integer)) a))
					  (* (/ (i-large-integer)) b)
					  (find-zero-n a z 0 (i-large-integer)
						       (+ (- (* (/ (i-large-integer)) a))
							  (* (/ (i-large-integer))
							     b))))
				(rcfn-domain)))
    :hints (("Goal"
	     :use ((:instance find-zero-n-upper-bound-tight
			      (i 0)
			      (n (i-large-integer))
			      (eps (+ (- (* (/ (i-large-integer)) a))
				      (* (/ (i-large-integer)) b))))
		   (:instance (:theorem (implies (and (realp a) (realp eps) (realp f) (< 0 eps) (<= a f)) (<= a (+ f eps))))
			      (a a)
			      (f (find-zero-n a z 0 (i-large-integer)
						       (+ (- (* (/ (i-large-integer)) a))
							  (* (/ (i-large-integer))
							     b))))
			      (eps (+ (- (* (/ (i-large-integer)) a))
				      (* (/ (i-large-integer)) b))))
		   (:instance inside-interval-p-squeeze
			      (a a)
			      (b b)
			      (c (+ (- (* (/ (i-large-integer)) a))
					  (* (/ (i-large-integer)) b)
					  (find-zero-n a z 0 (i-large-integer)
						       (+ (- (* (/ (i-large-integer)) a))
							  (* (/ (i-large-integer))
							     b)))))
			      (interval (rcfn-domain)))
		   )
	     :in-theory (disable find-zero-n-upper-bound-tight inside-interval-p-squeeze)))
    ))

 (local
  (defthm lemma-6
    (implies (and (interval-left-inclusive-p (rcfn-domain))
		  (interval-right-inclusive-p (rcfn-domain))
		  (inside-interval-p a (rcfn-domain)) (standardp a)
		  (inside-interval-p b (rcfn-domain)) (standardp b)
		  (< a b)
		  (realp z) (standardp z)
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
   (implies (and (interval-left-inclusive-p (rcfn-domain))
		 (interval-right-inclusive-p (rcfn-domain))
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
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

 ;; And here is the intermediate value theorem.

(local
 (defthm weak-intermediate-value-theorem
   (implies (and (interval-left-inclusive-p (rcfn-domain))
		 (interval-right-inclusive-p (rcfn-domain))
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
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
				rcfn-find-zero->=-z)))))


(local
 (defthm rcfn-domain-non-trivial-direct
   (implies (and (interval-left-endpoint (rcfn-domain))
		 (interval-right-endpoint (rcfn-domain)))
	    (< (interval-left-endpoint (rcfn-domain))
	       (interval-right-endpoint (rcfn-domain))))
   :hints (("Goal"
	    :use ((:instance rcfn-domain-non-trivial))))
   :rule-classes (:built-in-clause)))


(defthm intermediate-value-theorem
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
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
; Changed by Matt K. after v4-3 to put every :use hint on "Goal".  The first
; change was to accommodate tau.  The second change was sometime later, and I
; don't know why it was necessary.
; Originally for "Subgoal 3", but deleted now:
;           :in-theory (disable subinterval-interval-closed-closed inside-trivial-interval)
	    :use ((:functional-instance weak-intermediate-value-theorem
					(rcfn-domain (lambda ()
						       (if (and (< a b)
								(inside-interval-p a (rcfn-domain))
								(inside-interval-p b (rcfn-domain)))
							   (interval a b)
							 (rcfn-domain)))))
                  (:instance inside-interval-p-contains-left-endpoint
			     (interval (interval a b)))
		  (:instance inside-interval-p-contains-right-endpoint
			     (interval (interval a b)))
                  (:instance subinterval-interval-closed-closed
			     (a a)
			     (b b)
			     (interval (rcfn-domain)))
		  (:instance inside-trivial-interval
			     (a y)
                             (b x))))))

;; Now, what happens when f(a)>z and f(b)<z.  First, we find the root.

(defun find-zero-n-2 (a z i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (realp a)
	   (integerp i)
	   (integerp n)
	   (< i n)
	   (realp eps)
	   (< 0 eps)
	   (< z (rcfn (+ a eps))))
      (find-zero-n-2 (+ a eps) z (1+ i) n eps)
    (realfix a)))

;; The key theorem -- if -x is close to -y, then x is close to y.

(defthm close-uminus
  (implies (and (acl2-numberp x)
		(acl2-numberp y))
	   (equal (i-close (- x) (- y))
		  (i-close x y)))
  :hints (("Goal"
	   :use ((:instance i-small-uminus (x (+ x (- y)))))
	   :in-theory (enable i-close i-small-uminus))))

;; We prove that this function returns a limited number for limited
;; arguments.

(defthm limited-find-zero-2-body
  (implies (and (i-limited a)
		(i-limited b)
		(realp b)
		(realp z)
		)
	   (i-limited (find-zero-n-2 a
				     z
				     0
				     (i-large-integer)
				     (+ (- (* (/ (i-large-integer)) a))
					(* (/ (i-large-integer)) b)))))
   :hints (("Goal"
	    :use ((:instance
		   (:functional-instance
		    limited-find-zero-body
		    (rcfn (lambda (x) (- (rcfn x))))
		    (find-zero-n (lambda (a z i n
					    eps)
				   (find-zero-n-2
				    a (- z) i n eps))))
		   (z (- z))))
	    :in-theory (disable limited-find-zero-body))))

;; We define the root we want in the range [a,b)

(defun-std find-zero-2 (a b z)
  (if (and (realp a)
	   (realp b)
	   (realp z)
	   (< a b))
      (standard-part
       (find-zero-n-2 a
		      z
		      0
		      (i-large-integer)
		      (/ (- b a) (i-large-integer))))
    0))

;; And here is the second version of the intermediate value theorem.

(local
 (defthm standardp-minus-z
   (implies (and (realp z)
                 (standardp z))
            (standardp (- z)))
   :rule-classes (:type-prescription :forward-chaining)))

(local
 (defthmd definition-of-find-zero-2-lemma
   (implies (and (standardp a)
                 (standardp b)
                 (standardp z))
            (equal (find-zero-2 a b z)
                   (if (and (realp a)
                            (realp b)
                            (realp z)
                            (< a b))
                       (standard-part
                        (find-zero-n-2 a
                                       z
                                       0
                                       (i-large-integer)
                                       (/ (- b a) (i-large-integer))))
                     0)))))

(local
 (defthmd definition-of-find-zero-2-uminus-z
   (implies (and (standardp a)
                 (standardp b)
                 (standardp z))
            (equal (find-zero-2 a b (- z))
                   (if (and (realp a)
                            (realp b)
                            (realp (- z))
                            (< a b))
                       (standard-part
                        (find-zero-n-2 a
                                       (- z)
                                       0
                                       (i-large-integer)
                                       (/ (- b a) (i-large-integer))))
                     0)))
   :hints (("Goal"
            :use ((:instance definition-of-find-zero-2-lemma
                             (z (- z))))))
   ))

(defthm intermediate-value-theorem-2
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(realp z)
		(< a b)
		(< z (rcfn a))
		(< (rcfn b) z))
	   (and (realp (find-zero-2 a b z))
		(< a (find-zero-2 a b z))
		(< (find-zero-2 a b z) b)
		(equal (rcfn (find-zero-2 a b z))
		       z)))
  :hints (("Goal"
	   :use ((:instance
		  (:functional-instance
		   intermediate-value-theorem
		   (rcfn (lambda (x) (- (rcfn x))))
		   (find-zero (lambda (a b z)
				(find-zero-2 a b
					     (if (realp z) (- z) z))))
		   (find-zero-n (lambda (a z i n
					   eps)
				  (find-zero-n-2
				   a (- z) i n eps))))
		  (z (if (realp z) (- z) z))
		  ))
	   :in-theory (disable intermediate-value-theorem))
          ("Subgoal 1"
           :use ((:instance definition-of-find-zero-2-uminus-z)))))

;; Now we state the intermediate value theorem using quantifiers

(defun-sk exists-intermediate-point (a b z)
  (exists (x)
	  (and (realp x)
	       (< a x)
	       (< x b)
	       (equal (rcfn x) z))))

(local
 (defthm intermediate-value-theorem-1-sk
     (implies (and (inside-interval-p a (rcfn-domain))
		   (inside-interval-p b (rcfn-domain))
		   (realp z)
		   (< a b)
		   (< (rcfn a) z)
		   (< z (rcfn b)))
	      (exists-intermediate-point a b z))
   :hints (("Goal"
	    :use ((:instance exists-intermediate-point-suff
			     (x (find-zero a b z)))
		  (:instance intermediate-value-theorem))
	    :in-theory (disable exists-intermediate-point-suff intermediate-value-theorem)))))

(local
 (defthm intermediate-value-theorem-2-sk
     (implies (and (inside-interval-p a (rcfn-domain))
		   (inside-interval-p b (rcfn-domain))
		   (realp z)
		   (< a b)
		   (< z (rcfn a))
		   (< (rcfn b) z))
	      (exists-intermediate-point a b z))
   :hints (("Goal"
	    :use ((:instance exists-intermediate-point-suff
			     (x (find-zero-2 a b z)))
		  (:instance intermediate-value-theorem-2))
	    :in-theory (disable exists-intermediate-point-suff intermediate-value-theorem-2)))))

(defthm intermediate-value-theorem-sk
    (implies (and (inside-interval-p a (rcfn-domain))
		  (inside-interval-p b (rcfn-domain))
		  (realp z)
		  (< a b)
		  (or (and (< (rcfn a) z) (< z (rcfn b)))
		      (and (< z (rcfn a)) (< (rcfn b) z))))
	      (exists-intermediate-point a b z))
  :hints (("Goal"
	   :use ((:instance intermediate-value-theorem-1-sk)
		 (:instance intermediate-value-theorem-2-sk))
	   :in-theory nil))
  )


;; The next task is to prove the extreme theorems.  The approach is
;; similar to the intermediate-value theorem.  First, we define a
;; function that splits up the interval [a,b] into a grid of size eps
;; and then we find the maximum of the function at the points in the
;; grid.

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
  :hints (("Goal"
	   :use ((:instance find-max-rcfn-x-n-upper-bound
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
		  (x (find-max-rcfn-x-n a a 0 (i-large-integer)
				   (+ (- (* (/ (i-large-integer)) a))
				      (* (/ (i-large-integer))
					 b)))))))
	  ("Subgoal 1'"
	   :use ((:instance large-if->-large
			    (x x)
			    (y (if (< (abs a) (abs b))
				   (abs b)
				 (abs a)))))
	   :in-theory (disable large-if->-large))))

;; More important, if a and b are in the domain, so is find-max-x-n,
;; and that also follows since we know it's inside [a,b]

(defthm find-max-rcfn-x-n-in-domain
    (implies (and (inside-interval-p a (rcfn-domain))
		  (inside-interval-p b (rcfn-domain))
		  (< a b))
	     (inside-interval-p (find-max-rcfn-x-n a a
						   0 (i-large-integer)
						   (+ (- (* (/ (i-large-integer)) a))
						      (* (/ (i-large-integer)) b)))
				(rcfn-domain)))
  :hints (("Goal"
	   :use ((:instance INSIDE-INTERVAL-P-SQUEEZE
			    (a a)
			    (b b)
			    (c (find-max-rcfn-x-n a a
						  0 (i-large-integer)
						  (+ (- (* (/ (i-large-integer)) a))
						     (* (/ (i-large-integer)) b))))
			    (interval (rcfn-domain)))
		 (:instance find-max-rcfn-x-n-upper-bound
			    (a a)
			    (max-x a)
			    (i 0)
			    (n (i-large-integer))
			    (eps (+ (- (* (/ (i-large-integer)) a))
				    (* (/ (i-large-integer)) b))))
		 )
	   :in-theory (disable INSIDE-INTERVAL-P-SQUEEZE))))

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
	   :in-theory (disable standard-part-<=))))

;; And find-max is inside an interval if a and b are inside the interval

(defthm find-max-rcfn-x-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (find-max-rcfn-x a b) interval))
  :hints (("Goal"
	   :use ((:instance inside-interval-p-squeeze
			    (a a)
			    (b b)
			    (c (find-max-rcfn-x a b))))
	   :in-theory (disable inside-interval-p-squeeze)))
  )

;; OK now, (rcfn max) should be the maximum at all the grid points,
;; modulo standard-part.  Why?  Because max is (std-pt max-n).  By
;; construction, max-n is the maximum of all grid-points.  But, (rcfn
;; max) and (rcfn max-n) are close to each other, since rcfn is
;; continuous. Also, (rcfn max) is standard, since max is standard, so
;; (rcfn max) = (std-pt (rcfn max-n)) >= (std-pt (rcfn x_i)) where x_i
;; is any point in the grid.

(defthm find-max-rcfn-is-maximum-of-grid
  (implies (and (realp a) (standardp a)
		(realp b) (standardp b)
		(inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
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
			    (max-x a))
		 (:instance rcfn-standard-part
			    (x (FIND-MAX-RCFN-X-N A A 0 (I-LARGE-INTEGER)
						  (+ (- (* (/ (I-LARGE-INTEGER)) A))
						     (* (/ (I-LARGE-INTEGER)) B)))))
		 (:instance find-max-rcfn-x-inside-interval
			    (a a)
			    (b b)
			    (interval (rcfn-domain))))
	   :in-theory (disable standard-part-<=
			       find-max-rcfn-x-n-is-maximum
			       rcfn-standard-part
			       find-max-rcfn-x-inside-interval))))

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

(defthm rcfn-x-close-to-rcfn-upper-bound-of-grid
  (implies (and (integerp i)
		(<= 0 i)
		(integerp n)
		(<= i n)
		(realp eps)
		(< 0 eps)
		(inside-interval-p a (rcfn-domain))
		(inside-interval-p (+ a (* n eps)) (rcfn-domain))
		(realp x)
		(standardp x)
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
		 (:instance x-in-upper-bound-of-grid-small-eps-better)
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b (+ a (* n eps)))
			    (c x)
			    (interval (rcfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a a)
			    (b (+ a (* n eps)))
			    (c (+ a (* i eps)))
			    (interval (rcfn-domain)))
		 (:instance inside-interval-p-squeeze
			    (a (+ a (* i eps)))
			    (b (+ a (* n eps)))
			    (c (+ a (* (upper-bound-of-grid a x i n eps) eps)))
			    (interval (rcfn-domain))))
	   :in-theory (disable rcfn-continuous
			       x-in-upper-bound-of-grid-small-eps-better
			       upper-bound-of-grid
			       inside-interval-p-squeeze))))

;; In particular, (std-pt (rcfn x_i)) = (std-pt (rcfn x)) and when x
;; is standard that's equal to (rcfn x).

(defthm rcfn-x-close-to-rcfn-upper-bound-of-grid-better
  (implies (and (integerp i)
		(<= 0 i)
		(integerp n)
		(<= i n)
		(realp eps)
		(< 0 eps)
		(inside-interval-p a (rcfn-domain))
		(inside-interval-p (+ a (* n eps)) (rcfn-domain))
		(realp x)
		(standardp x)
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
   (implies (and (realp a) (standardp a)
		 (realp b) (standardp b)
		 (< a b))
	    (i-small (+ (- (* (/ (i-large-integer)) a))
			(* (/ (i-large-integer)) b))))))

(defthm find-max-rcfn-is-maximum-of-standard
  (implies (and (inside-interval-p a (rcfn-domain))
		(standardp a)
		(inside-interval-p b (rcfn-domain))
		(standardp b)
		(realp x) (standardp x)
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
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn x) (rcfn (find-max-rcfn-x a b))))
  :hints (("Goal"
	   :in-theory (disable find-max-rcfn-x))))

;; Now we do it with quantifiers

(defun-sk is-maximum-point (a b max)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn x) (rcfn max)))))

(defun-sk achieves-maximum-point (a b)
  (exists (max)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp max)
			(<= a max)
			(<= max b)
			(is-maximum-point a b max)))))

(defthm maximum-point-theorem-sk
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(< a b))
	   (achieves-maximum-point a b))
  :hints (("Goal"
	   :use ((:instance achieves-maximum-point-suff
			    (max (find-max-rcfn-x a b)))
		 (:instance find-max-rcfn-is-maximum
			    (x (is-maximum-point-witness a b (find-max-rcfn-x a b)))))
	   :in-theory (disable achieves-maximum-point-suff
			       find-max-rcfn-is-maximum))))

;; Of course, the function also achieves its minimum.  To do that, we
;; start with the follogin function, which is similar to the "max-x-n"
;; function above.  Shouldn't ACL2 be able to do this sort of thing by
;; itself?

(defun find-min-rcfn-x-n (a min-x i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (integerp i)
	   (integerp n)
	   (<= i n)
	   (realp a)
	   (realp eps)
	   (< 0 eps))
      (if (< (rcfn (+ a (* i eps))) (rcfn min-x))
	  (find-min-rcfn-x-n a (+ a (* i eps)) (1+ i) n eps)
	(find-min-rcfn-x-n a min-x (1+ i) n eps))
    min-x))

;; We have to prove that this function is limited.  Luckily, we can
;; just reuse the theorem about max-n being limited.

(defthm find-min-rcfn-x-n-limited
  (implies (and (realp a)
		(i-limited a)
		(realp b)
		(i-limited b)
		(< a b))
	   (i-limited (find-min-rcfn-x-n a a
				    0 (i-large-integer)
				    (+ (- (* (/ (i-large-integer)) a))
				       (* (/ (i-large-integer)) b)))))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-n-limited
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       ))
	   :in-theory (disable find-max-rcfn-x-n-limited))))

;; That justifies the definition of min-x.

(defun-std find-min-rcfn-x (a b)
  (if (and (realp a)
	   (realp b)
	   (< a b))
      (standard-part (find-min-rcfn-x-n a
				   a
				   0
				   (i-large-integer)
				   (/ (- b a) (i-large-integer))))
    0))

;; Now, to see that this function really returns a minimum, we just
;; have to instantiate the appropriate theorem about maximums.

(defthm find-min-rcfn-is-minimum
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(< a b))
	   (<= (rcfn (find-min-rcfn-x a b)) (rcfn x)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-is-maximum
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-is-maximum))))

;; Similarly, we want to show that a <= min-x -- just instantiate the
;; theorem about maximum!

(defthm find-min-rcfn-x->=-a
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= a (find-min-rcfn-x a b)))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x->=-a
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-x->=-a))))

;; And finally,, we want to show that min-x <= b -- again, just
;; instantiate the theorem about maximum!

(defthm find-min-rcfn-x-<=-b
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (<= (find-min-rcfn-x a b) b))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-<=-b
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-x-<=-b))))

;; And find-min is inside an interval if a and b are inside the interval

(defthm find-min-rcfn-x-inside-interval
    (implies (and (inside-interval-p a interval)
		  (inside-interval-p b interval)
		  (< a b))
	     (inside-interval-p (find-min-rcfn-x a b) interval))
  :hints (("Goal"
	   :use ((:functional-instance find-max-rcfn-x-inside-interval
				       (rcfn (lambda (x) (- (rcfn
							     x))))
				       (find-max-rcfn-x-n find-min-rcfn-x-n)
				       (find-max-rcfn-x find-min-rcfn-x)))
	   :in-theory (disable find-max-rcfn-x-inside-interval))))

;; Now we do it with quantifiers

(defun-sk is-minimum-point (a b min)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn min) (rcfn x)))))

(defun-sk achieves-minimum-point (a b)
  (exists (min)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp min)
			(<= a min)
			(<= min b)
			(is-minimum-point a b min)))))

(defthm minimum-point-theorem-sk
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(< a b))
	   (achieves-minimum-point a b))
  :hints (("Goal"
	   :use ((:instance achieves-minimum-point-suff
			    (min (find-min-rcfn-x a b)))
		 (:instance find-min-rcfn-is-minimum
			    (x (is-minimum-point-witness a b (find-min-rcfn-x a b)))))
	   :in-theory (disable achieves-minimum-point-suff
			       find-min-rcfn-is-minimum))))
