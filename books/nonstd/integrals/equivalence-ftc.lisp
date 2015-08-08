(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/equivalence-continuity" :dir :system))
(local (include-book "nonstd/nsa/equivalence-derivatives" :dir :system))
(include-book "make-partition")
(local (include-book "equivalence-integrals"))
(local (include-book "ftc-2"))

(include-book "integrable-functions")

(encapsulate
 ( ((rcdfn-classical *) => *)
   ((rcdfn-classical-prime *) => *)
   ((rcdfn-classical-domain) => *)
   )

   (local (defun rcdfn-classical (x) (declare (ignore x)) 0))
   (local (defun rcdfn-classical-prime (x) (declare (ignore x)) 0))
   (local (defun rcdfn-classical-domain () (interval 0 1)))

   (defthm intervalp-rcdfn-classical-domain
     (interval-p (rcdfn-classical-domain))
   :rule-classes (:type-prescription :rewrite))

   (defthm rcdfn-classical-domain-real
     (implies (inside-interval-p x (rcdfn-classical-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

   (defthm rcdfn-classical-domain-non-trivial
     (or (null (interval-left-endpoint (rcdfn-classical-domain)))
	 (null (interval-right-endpoint (rcdfn-classical-domain)))
	 (< (interval-left-endpoint (rcdfn-classical-domain))
	    (interval-right-endpoint (rcdfn-classical-domain))))
     :rule-classes nil)

   (defthm rcdfn-classical-real
     (realp (rcdfn-classical x))
   :rule-classes (:rewrite :type-prescription))

   (defthm rcdfn-classical-prime-real
     (realp (rcdfn-classical-prime x))
   :rule-classes (:rewrite :type-prescription))

   (defun-sk forall-x-eps-delta-in-range-deriv-rcdfn-classical-works (x eps delta)
     (forall (x1)
	     (implies (and (inside-interval-p x1 (rcdfn-classical-domain))
			   (inside-interval-p x (rcdfn-classical-domain))
			   (realp delta)
			   (< 0 delta)
			   (realp eps)
			   (< 0 eps)
			   (not (equal x x1))
			   (< (abs (- x x1)) delta))
		      (< (abs (- (/ (- (rcdfn-classical x) (rcdfn-classical x1))
				    (- x x1))
				 (rcdfn-classical-prime x)))
			 eps))))

   (defun-sk exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works (x eps)
     (exists delta
	     (implies (and (inside-interval-p x (rcdfn-classical-domain))
			   (realp eps)
			   (< 0 eps))
		      (and (realp delta)
			   (< 0 delta)
			   (forall-x-eps-delta-in-range-deriv-rcdfn-classical-works x eps delta)))))

   (defthm rcdfn-classical-prime-is-derivative
     (implies (and (inside-interval-p x (rcdfn-classical-domain))
		   (realp eps)
		   (< 0 eps))
	      (exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works x eps))
     :hints (("Goal"
	      :use ((:instance exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works-suff
			       (delta 1))
		    (:instance forall-x-eps-delta-in-range-deriv-rcdfn-classical-works
			       (x x)
			       (eps eps)
			       (delta 1)))
	      :in-theory (disable abs))))

   (defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime (x0 eps delta)
     (forall (x)
	     (implies (and (inside-interval-p x (rcdfn-classical-domain))
			   (inside-interval-p x0 (rcdfn-classical-domain))
			   (realp delta)
			   (< 0 delta)
			   (realp eps)
			   (< 0 eps)
			   (< (abs (- x x0)) delta)
			   (not (equal x x0)))
		      (< (abs (- (rcdfn-classical-prime x) (rcdfn-classical-prime x0)))
			 eps)))
     :rewrite :direct)

   (defun-sk exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime (x0 eps)
     (exists (delta)
	     (implies (and (inside-interval-p x0 (rcdfn-classical-domain))
			   ;(standardp x0)
			   (realp eps)
			   ;(standardp eps)
			   (< 0 eps))
		      (and ;(standardp delta)
			   (realp delta)
			   (< 0 delta)
			   (forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime x0 eps delta)))))

   (defthmd rcdfn-classical-prime-is-continuous
     (implies (and (inside-interval-p x0 (rcdfn-classical-domain))
		   ;(standardp x0)
		   (realp eps)
		   ;(standardp eps)
		   (< 0 eps))
	      (exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime x0 eps))
     :hints (("Goal"
	      :use ((:instance exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-suff
			       (delta 1))
		    (:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime
			       (x0 x0)
			       (eps eps)
			       (delta 1)))
	      :in-theory (disable abs))))

   )

(defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime (x0 eps)
  (exists (delta)
	  (implies (and (inside-interval-p x0 (rcdfn-classical-domain))
			(standardp x0)
			(realp eps)
			(standardp eps)
			(< 0 eps))
		   (and (standardp delta)
			(realp delta)
			(< 0 delta)
			(forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime x0 eps delta))))
     :classicalp nil)

(encapsulate
 nil

 (local
  (defthm-std lemma-1
    (implies (and (standardp x0)
		  (standardp eps))
	     (standardp (exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-witness x0 eps)))))

 (defthmd rcdfn-classical-prime-is-continuous-classically
   (implies (and (inside-interval-p x0 (rcdfn-classical-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime x0 eps))
   :hints (("Goal"
	    :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-suff
			     (delta (exists-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-witness x0 eps)))
		  (:instance rcdfn-classical-prime-is-continuous))
	    :in-theory (disable abs))))
 )

(defthm rcdfn-classical-prime-is-derivative-nonstd
  (implies (and (standardp x)
		(inside-interval-p x (rcdfn-classical-domain))
		(inside-interval-p x1 (rcdfn-classical-domain))
		(i-close x x1) (not (= x x1)))
	   (i-close (/ (- (rcdfn-classical x) (rcdfn-classical x1)) (- x x1))
		    (rcdfn-classical-prime x)))
  :hints (("Goal"
	   :use ((:functional-instance rdfn-classic-is-differentiable
				       (rdfn-classical-domain rcdfn-classical-domain)
				       (rdfn-classical rcdfn-classical)
				       (derivative-rdfn-classical rcdfn-classical-prime)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works
					exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
					exists-delta-for-x-and-eps-so-deriv-rcdfn-classical-works-witness)
				       (forall-x-eps-delta-in-range-deriv-classical-works
					forall-x-eps-delta-in-range-deriv-rcdfn-classical-works)
				       (forall-x-eps-delta-in-range-deriv-classical-works-witness
					forall-x-eps-delta-in-range-deriv-rcdfn-classical-works-witness)
				       )))
	  ("Subgoal 5"
	   :use ((:instance rcdfn-classical-prime-is-derivative)))
	  ("Subgoal 3"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-rcdfn-classical-works-necc)))
	  ("Subgoal 2"
	   :use ((:instance rcdfn-classical-domain-non-trivial)))
	  )
  )

(defthm rcdfn-classical-prime-continuous-nonstd
  (implies (and (standardp x)
		(inside-interval-p x (rcdfn-classical-domain))
		(i-close x x1)
		(inside-interval-p x1 (rcdfn-classical-domain)))
	   (i-close (rcdfn-classical-prime x)
		    (rcdfn-classical-prime x1)))
  :hints (("Goal"
	   :use ((:instance
		  (:functional-instance rcfn-classical-is-continuous-using-nonstandard-criterion
					(rcfn-classical rcdfn-classical-prime)
					(rcfn-classical-domain rcdfn-classical-domain)
					(exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f
					 exists-standard-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime)
					(exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-witness
					 exists-standard-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-witness)
					(forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f
					 forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime)
					(forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f-witness
					 forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime-witness))
		  (x0 x)
		  (x x1)
		  )))
	  ("Subgoal 7"
	   :use ((:instance rcdfn-classical-prime-is-continuous-classically)))
	  ("Subgoal 5"
	   :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-rcdfn-classical-prime-suff)))
	  ("Subgoal 3"
	   :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-rcdfn-classical-prime-necc)))
	  ("Subgoal 2"
	   :use ((:instance rcdfn-classical-domain-non-trivial)))
	  ))

(defun map-rcdfn-classical-prime (p)
  (if (consp p)
      (cons (rcdfn-classical-prime (car p))
	    (map-rcdfn-classical-prime (cdr p)))
    nil))

(defun riemann-rcdfn-classical-prime (p)
  (dotprod (deltas p)
	   (map-rcdfn-classical-prime (cdr p))))

(defthm realp-riemann-rcdfn-classical-prime
  (implies (partitionp p)
	   (realp (riemann-rcdfn-classical-prime p))))

(encapsulate
 nil

 (local
  (defthm limited-riemann-rcdfn-classical-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (rcdfn-classical-domain))
		  (inside-interval-p b (rcdfn-classical-domain))
		  (< a b))
	     (i-limited (riemann-rcdfn-classical-prime (make-small-partition a b))))
    :hints (("Goal"
	     :by (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain rcdfn-classical-domain)
				       (rcfn rcdfn-classical-prime)
				       (map-rcfn map-rcdfn-classical-prime)
				       (riemann-rcfn riemann-rcdfn-classical-prime)))
	    ("Subgoal 2"
	     :use ((:instance rcdfn-classical-domain-non-trivial))))))

 (local (in-theory (disable riemann-rcdfn-classical-prime)))



 (defun-std strict-int-rcdfn-classical-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (rcdfn-classical-domain))
	    (inside-interval-p b (rcdfn-classical-domain))
	    (< a b))
       (standard-part (riemann-rcdfn-classical-prime (make-small-partition a b)))
     0))
 )

(defun int-rcdfn-classical-prime (a b)
  (if (<= a b)
      (strict-int-rcdfn-classical-prime a b)
    (- (strict-int-rcdfn-classical-prime b a))))

(defthm-std realp-strict-int-rcdfn-classical-prime
  (IMPLIES (AND (REALP A) (REALP B))
         (REALP (STRICT-INT-RCDFN-CLASSICAL-PRIME A B)))
; Matt K. v7-1 mod for ACL2 mod on 2/13/2015: "Goal'" changed to "Goal".
  :hints (("Goal"
	   :use ((:instance realp-riemann-rcdfn-classical-prime
			    (p (make-small-partition a b))))
	   :in-theory (disable realp-riemann-rcdfn-classical-prime
			       riemann-rcdfn-classical-prime)))
  )

(defun-sk forall-partitions-riemann-sum-is-close-to-int-rcdfn-classical-prime (a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rcdfn-classical-prime p)
			       (strict-int-rcdfn-classical-prime a b)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rcdfn-classical-prime (a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (rcdfn-classical-domain))
			 (inside-interval-p b (rcdfn-classical-domain))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rcdfn-classical-prime a b eps delta)))))

(defthm strict-int-rcdfn-classical-prime-is-integral-of-rcdfn-classical-prime
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (rcdfn-classical-domain))
		(inside-interval-p b (rcdfn-classical-domain))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rcdfn-classical-prime p)
		    (strict-int-rcdfn-classical-prime a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :by (:functional-instance strict-int-rcdfn-prime-is-integral-of-rcdfn-prime
				     (rcdfn rcdfn-classical)
				     (rcdfn-prime rcdfn-classical-prime)
				     (rcdfn-domain rcdfn-classical-domain)
				     (map-rcdfn-prime map-rcdfn-classical-prime)
				     (riemann-rcdfn-prime riemann-rcdfn-classical-prime)
				     (strict-int-rcdfn-prime strict-int-rcdfn-classical-prime)
				     (int-rcdfn-prime int-rcdfn-classical-prime)))
	   ("Subgoal 3"
	    :use ((:instance rcdfn-classical-prime-is-derivative-nonstd)))
	   ("Subgoal 2"
	    :use ((:instance rcdfn-classical-domain-non-trivial)))
	   ))

(defthm rcdfn-classical-prime-is-integrable-hyperreal
  (implies (and (<= a b)
		(inside-interval-p a (rcdfn-classical-domain))
		(inside-interval-p b (rcdfn-classical-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-so-that-riemann-sum-is-close-to-int-rcdfn-classical-prime a b eps))
  :hints (("Goal" :do-not-induct t
	   :by (:functional-instance rifn-is-integrable-hyperreal
				     (rifn rcdfn-classical-prime)
				     (domain-rifn rcdfn-classical-domain)
				     (map-rifn map-rcdfn-classical-prime)
				     (riemann-rifn riemann-rcdfn-classical-prime)
				     (strict-int-rifn strict-int-rcdfn-classical-prime)
				     (int-rifn int-rcdfn-classical-prime)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn
				      forall-partitions-riemann-sum-is-close-to-int-rcdfn-classical-prime)
				     (forall-partitions-riemann-sum-is-close-to-int-rifn-witness
				      forall-partitions-riemann-sum-is-close-to-int-rcdfn-classical-prime-witness)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn
				      exists-delta-so-that-riemann-sum-is-close-to-int-rcdfn-classical-prime)
				     (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-witness
				      exists-delta-so-that-riemann-sum-is-close-to-int-rcdfn-classical-prime-witness)))
	  ("Subgoal 8"
	   :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rcdfn-classical-prime-suff)))
	  ("Subgoal 6"
	   :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rcdfn-classical-prime-necc)))
	  ("Subgoal 4"
	   :use ((:instance strict-int-rcdfn-classical-prime-is-integral-of-rcdfn-classical-prime)))
	  ("Subgoal 3"
	   :use ((:instance rcdfn-classical-domain-non-trivial)))
	  ))

(defthm ftc-2-for-rcdfn-classical
  (implies (and (inside-interval-p a (rcdfn-classical-domain))
		(inside-interval-p b (rcdfn-classical-domain)))
	   (equal (int-rcdfn-classical-prime a b)
		  (- (rcdfn-classical b)
		     (rcdfn-classical a))))
   :hints (("Goal"
	    :by (:functional-instance ftc-2
				      (rcdfn rcdfn-classical)
				      (rcdfn-prime rcdfn-classical-prime)
				      (rcdfn-domain rcdfn-classical-domain)
				      (map-rcdfn-prime map-rcdfn-classical-prime)
				      (riemann-rcdfn-prime riemann-rcdfn-classical-prime)
				      (strict-int-rcdfn-prime strict-int-rcdfn-classical-prime)
				      (int-rcdfn-prime int-rcdfn-classical-prime)))
	   )
   )

