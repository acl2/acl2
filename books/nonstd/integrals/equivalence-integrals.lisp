(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(include-book "integrable-functions")

(encapsulate
 ( ((rifn-classical *) => *)
   ((strict-int-rifn-classical * *) => *)
   ((domain-rifn-classical) => *)
   ;((map-rifn *) => *)
   ;((riemann-rifn *) => *)
   )

 (local
  (defun rifn-classical (x)
    (declare (ignore x))
    0))

 (defthm rifn-classical-real
   (implies (realp x)
	    (realp (rifn-classical x))))

 (local
  (defun strict-int-rifn-classical (a b)
    (declare (ignore a b))
    0))

 (defthm strict-int-rifn-classical-real
   (implies (and (realp a)
		 (realp b))
	    (realp (strict-int-rifn-classical a b))))

 (local
  (defun domain-rifn-classical ()
    (interval nil nil)))

 (defthm domain-rifn-classical-is-non-trivial-interval
   (and (interval-p (domain-rifn-classical))
	(implies (and (interval-left-inclusive-p (domain-rifn-classical))
		      (interval-right-inclusive-p (domain-rifn-classical)))
		 (not (equal (interval-left-endpoint (domain-rifn-classical))
			     (interval-right-endpoint (domain-rifn-classical)))))))

 (defun map-rifn-classical (p)
   ;; map rifn over the list p
   (if (consp p)
       (cons (rifn-classical (car p))
	     (map-rifn-classical (cdr p)))
     nil))

 (defun riemann-rifn-classical (p)
   ;; for partition p, take the Riemann sum of rifn over p using right
   ;; endpoints
   (dotprod (deltas p)
	    (map-rifn-classical (cdr p))))

 (defun int-rifn-classical (a b)
   (if (<= a b)
       (strict-int-rifn-classical a b)
     (- (strict-int-rifn-classical b a))))

 (local
  (defthm map-rifn-classical-zero
    (implies (consp p)
	     (equal (car (map-rifn-classical p)) 0))))

 (local
  (defthm riemann-rifn-classical-zero
    (implies (partitionp p)
	     (equal (riemann-rifn-classical p) 0))))

 (defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn-classical (a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn-classical p)
			       (strict-int-rifn-classical a b)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical (a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn-classical))
			 (inside-interval-p b (domain-rifn-classical))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn-classical a b eps delta)))))

 (defthm strict-int-rifn-classical-is-integral-of-rifn-classical
   (implies (and (inside-interval-p a (domain-rifn-classical))
		 (inside-interval-p b (domain-rifn-classical))
		 (<= a b)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical a b eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-suff
			     (delta 1)))))
   )
 )

(defun-sk exists-standard-delta-so-that-riemann-sum-is-close-to-int-rifn-classical (a b eps)
  (exists (delta)
	  (implies (and (inside-interval-p a (domain-rifn-classical))
			(inside-interval-p b (domain-rifn-classical))
			(<= a b)
			(standardp a)
			(standardp b)
			(realp eps)
			(< 0 eps)
			(standardp eps))
		   (and (standardp delta)
			(realp delta)
			(< 0 delta)
			(forall-partitions-riemann-sum-is-close-to-int-rifn-classical a b eps delta))))
   :classicalp nil)

(local
 (defthm-std classical-exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness
   (implies (and (standardp a)
		 (standardp b)
		 (standardp eps))
	    (standardp (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness a b eps)))))

(defthm strict-int-rifn-classical-is-integral-of-rifn-classical-for-standards
   (implies (and (inside-interval-p a (domain-rifn-classical))
		 (inside-interval-p b (domain-rifn-classical))
		 (standardp a)
		 (standardp b)
		 (<= a b)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-so-that-riemann-sum-is-close-to-int-rifn-classical a b eps))
   :hints (("Goal"
	    :use ((:instance strict-int-rifn-classical-is-integral-of-rifn-classical)
		  (:instance exists-standard-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-suff
			     (delta (exists-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness a b eps))))
	    :in-theory (disable strict-int-rifn-classical-is-integral-of-rifn-classical))))

(local
 (defthmd forall-partitiona-riemann-sum-monotonic
   (implies (and (forall-partitions-riemann-sum-is-close-to-int-rifn-classical a b eps delta)
		 (realp delta)
		 (realp gamma)
		 (< 0 gamma)
		 (< gamma delta))
	    (forall-partitions-riemann-sum-is-close-to-int-rifn-classical a b eps gamma))
   :hints (("Goal"
	    :use ((:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-necc
			     (p (forall-partitions-riemann-sum-is-close-to-int-rifn-classical-witness a b eps gamma))))
	    :in-theory (disable abs riemann-rifn-classical partitionp mesh)))
   ))

(local
 (defthmd rifn-classical-is-integrable-step-1
   (implies (and (inside-interval-p a (domain-rifn-classical))
		 (inside-interval-p b (domain-rifn-classical))
		 (standardp a)
		 (standardp b)
		 (<= a b)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps)
		 (i-small delta)
		 (realp delta)
		 (< 0 delta))
	    (forall-partitions-riemann-sum-is-close-to-int-rifn-classical a b eps delta))
   :hints (("Goal"
	    :use ((:instance strict-int-rifn-classical-is-integral-of-rifn-classical-for-standards)
		  (:instance forall-partitiona-riemann-sum-monotonic
			     (delta (exists-standard-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness a b eps))
			     (gamma delta))
		  (:instance small-<-non-small
			     (x delta)
			     (y (exists-standard-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness a b eps)))
		  (:instance standard-small-is-zero
			     (x (exists-standard-delta-so-that-riemann-sum-is-close-to-int-rifn-classical-witness a b eps))))
	    :in-theory (disable strict-int-rifn-classical-is-integral-of-rifn-classical-for-standards
				small-<-non-small)))))

(local
 (defthmd rifn-classical-is-integrable-step-2
   (implies (and (inside-interval-p a (domain-rifn-classical))
		 (inside-interval-p b (domain-rifn-classical))
		 (standardp a)
		 (standardp b)
		 (<= a b)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps)
		 (i-small delta)
		 (realp delta)
		 (< 0 delta)
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (< (mesh p) delta))
	    (< (abs (- (riemann-rifn-classical p)
		       (strict-int-rifn-classical a b)))
	       eps))
   :hints (("Goal"
	    :use ((:instance rifn-classical-is-integrable-step-1)
		  (:instance forall-partitions-riemann-sum-is-close-to-int-rifn-classical-necc))
	    :in-theory (disable)
	    ))))

(local
 (defun standard-lower-bound-of-diff (x y)
   (if (i-limited y)
       (/ (abs (- x (standard-part y))) 2)
     1)))

(local
 (defthmd standards-are-in-order-2
   (implies (and (realp x)
		 (standardp x)
		 (realp y)
		 (< y x)
		 (realp z)
		 (standardp z)
		 (< (standard-part y) z))
	    (<= y z))
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			     (x z)
			     (y y)))
	    :in-theory (disable standard-part-<=)))))

(local
 (defthmd standards-are-in-order
   (implies (and (realp x)
		 (standardp x)
		 (realp y)
		 (< x y)
		 (realp z)
		 (standardp z)
		 (< z (standard-part y)))
	    (<= z y))
   :hints (("Goal"
	    :use ((:instance standard-part-<=
			     (x Y)
			     (y z)))
	    :in-theory (disable standard-part-<=)))))

(local
 (defthmd rifn-classical-is-integrable-step-3
   (implies (and (realp x)
		 (standardp x)
		 (realp y)
		 (not (i-close x y)))
	    (and (realp (standard-lower-bound-of-diff x y))
		 (< 0 (standard-lower-bound-of-diff x y))
		 (standardp (standard-lower-bound-of-diff x y))
		 (<= (standard-lower-bound-of-diff x y) (abs (- x y)))))
   :hints (("Subgoal 6"
	    :use ((:instance standard-part-<= (x y) (y x)))
	    :in-theory (disable standard-part-<=))
	   ("Subgoal 5"
	    :use ((:instance standard-part-<=))
	    :in-theory (disable standard-part-<=))
	   ("Subgoal 4"
	    :use ((:instance standards-are-in-order-2
			     (x x)
			     (y y)
			     (z (/ (+ x (standard-part y)) 2)))))
	   ("Subgoal 3"
	    :use ((:instance standards-are-in-order
			     (x x)
			     (y y)
			     (z (+ x (* -1/2 x) (* 1/2 (standard-part y)))))))
	   ("Subgoal 2"
	    :use ((:instance large->-non-large
			     (x y)
			     (y (+ x 1)))
		  (:instance large->-non-large
			     (x y)
			     (y x))))
	   ("Subgoal 1"
	    :use ((:instance large->-non-large
			     (x (- y 1))
			     (y x))
		  (:instance large->-non-large
			     (x (+ y 1))
			     (y x))
		  (:instance large->-non-large
			     (x y)
			     (y x))
		  (:instance large->-non-large
			     (x y)
			     (y 1))))
	   )
   ))

(local
 (defthm-std standard-riemann-rifn-classical
   (implies (standardp p)
	    (standardp (riemann-rifn-classical p)))))

(local
 (defthm-std standard-strict-int-rifn-classical
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (strict-int-rifn-classical a b)))))

(local
 (defthm large-abs
   (implies (realp x)
	    (equal (i-large (abs x))
		   (i-large x)))))

(local
 (defthm swap-abs-difference
   (equal (abs (+ x (- y)))
	  (abs (+ (- x) y)))))

(local
 (defthmd close-small-abs-2x
   (implies (and (realp x)
		 (realp y)
		 (i-close x y))
	    (i-small (* 2 (abs (- y x)))))
   :hints (("Goal"
	    :use ((:instance small*limited->small
			     (x (abs (- y x)))
			     (y 2))
		  )
	    :in-theory (e/d (i-close)
			    (small*limited->small))))))

(defthm realp-riemann-rifn-classical
  (implies (partitionp p)
	   (REALP (RIEMANN-RIFN-CLASSICAL P))))

(defun realpos-listp (l)
  (if (consp l)
      (and (realp (car l))
	   (< 0 (car l))
	   (realpos-listp (cdr l)))
    t))

(defthm deltas-positive-for-partition
  (implies (partitionp p)
	   (realpos-listp (deltas p))))

(defthm maxlist-realpos
  (implies (and (consp l)
		(realpos-listp l))
	   (< 0 (maxlist l))))

(defthm non-trivial-partition-=>-non-trivial-deltas
  (implies (and (partitionp p)
		(not (equal (car p) (car (last p)))))
	   (consp (deltas p)))
  )

(defthm partition-ascending
  (implies (partitionp p)
	   (<= (car p)
	       (car (last p)))))

(encapsulate
 nil

 (local
  (defthmd lemma-1
    (implies (and (partitionp p)
		  (consp (cdr p)))
	     (< (car p)
		(car (last p))))
    :hints (("Goal"
	     :expand ((partitionp p))
	     :use ((:instance partition-ascending (p (cdr p))))))))

 (local
  (defthm lemma-2
    (implies (and (partitionp p)
		  (equal (car p) (car (last p))))
	     (equal p (list (car p))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-1))
	     :expand ((partitionp p)
		      (partitionp (cdr p)))))
    :rule-classes nil))

  (defthm trivial-partition-=>-trivial-deltas
   (implies (and (partitionp p)
		 (equal (car p) (car (last p))))
	    (equal (deltas p) nil))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-2))))
   )
 )

(defthm mesh-non-negative
  (implies (partitionp p)
	   (<= 0 (mesh p)))
  :hints (("Goal"
	   :cases ((equal (car p) (car (last p))))
	   :in-theory (disable maxlist deltas partitionp))
	  )
  )

(defthmd mesh-positive
  (implies (and (partitionp p)
		(not (equal (car p) (car (last p)))))
	   (< 0 (mesh p)))
  :hints (("Goal"
	   ;:cases ((equal (car p) (car (last p))))
	   :in-theory (disable maxlist deltas partitionp))
	  )
  )

(defthmd when-mesh-is-not-positive
  (implies (and (partitionp p)
		(<= (mesh p) 0))
	   (equal (equal (car p) (car (last p)))
		  t))
  :hints (("Goal"
	   :use ((:instance mesh-non-negative)
		 (:instance mesh-positive))
	   :in-theory nil)
	  )
  )

(defthm realp-mesh
    (implies (partitionp p)
	     (realp (mesh p))))

(encapsulate
 nil

 (local
  (defthm lemma-1
    (implies (and (partitionp p)
		  (equal (car p) (car (last p))))
	     (equal (riemann-rifn-classical p) 0))))

 (local
  (defthmd lemma-2
    (implies (and (inside-interval-p a (domain-rifn-classical))
		  (inside-interval-p b (domain-rifn-classical))
		  (standardp a)
		  (standardp b)
		  (<= a b)
		  (realp eps)
		  (standardp eps)
		  (< 0 eps)
		  (i-small delta)
		  (realp delta)
		  (< 0 delta)
		  (partitionp p)
		  (equal (car p) a)
		  (equal (car (last p)) b)
		  (<= (mesh p) 0))
	     (< (abs (strict-int-rifn-classical a b)) eps))
    :hints (("Goal"
	     :use ((:instance rifn-classical-is-integrable-step-2)
		   (:instance when-mesh-is-not-positive))))))

 (local
  (defthmd lemma-3
    (implies (and (realp x)
		  (< 0 x)
		  (standardp x))
	     (< (/ x 2) x))))

 (local
  (defthmd lemma-4
    (implies (and (inside-interval-p a (domain-rifn-classical))
		  (inside-interval-p b (domain-rifn-classical))
		  (standardp a)
		  (standardp b)
		  (<= a b)
		  (partitionp p)
		  (equal (car p) a)
		  (equal (car (last p)) b)
		  (<= (mesh p) 0))
	     (i-small (abs (strict-int-rifn-classical a b))))
    :hints (("Goal"
	     :use ((:instance lemma-2
			      (eps (/ (abs (strict-int-rifn-classical a b)) 2))
			      (delta (/ (i-large-integer))))
		   (:instance lemma-3
			      (x (abs (strict-int-rifn-classical a b)))))))))

 (local
  (defthmd lemma-5
    (implies (and (inside-interval-p a (domain-rifn-classical))
		  (inside-interval-p b (domain-rifn-classical))
		  (standardp a)
		  (standardp b)
		  (<= a b)
		  (partitionp p)
		  (equal (car p) a)
		  (equal (car (last p)) b)
		  (<= (mesh p) 0))
	     (equal (strict-int-rifn-classical a b) 0))
    :hints (("Goal"
	     :use ((:instance lemma-4)
		   (:instance standard-small-is-zero
			      (x (abs (strict-int-rifn-classical a b)))))))))

 (defthm strict-int-rifn-classical-is-integral-of-rifn-classical-using-nonstandard-criterion
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn-classical))
		 (inside-interval-p b (domain-rifn-classical))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rifn-classical p)
		     (strict-int-rifn-classical a b)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance rifn-classical-is-integrable-step-2
			     (eps (standard-lower-bound-of-diff (strict-int-rifn-classical a b)
								(riemann-rifn-classical p)))
			     (delta (* 2 (mesh p))))
		  (:instance rifn-classical-is-integrable-step-3
			     (x (strict-int-rifn-classical a b))
			     (y (riemann-rifn-classical p))))
	    :in-theory (disable standard-lower-bound-of-diff abs
				riemann-rifn-classical partitionp mesh))
	   ("Subgoal 2"
	    :use ((:instance lemma-5
			     (a (car p))
			     (b (car (last p))))
		  (:instance when-mesh-is-not-positive)))
	   ("Subgoal 1"
	    :use ((:instance lemma-5
			     (a (car p))
			     (b (car (last p))))
		  (:instance when-mesh-is-not-positive)))
	   ))
 )

;; We close the loop by showing that the non-classical integrable function satisfies the
;; hyperreal definition of integrability

(local
 (defthmd close-<-abs-small-eps
   (implies (and (realp x)
		 (realp y)
		 (i-close x y)
		 (realp eps)
		 (< 0 eps)
		 (standardp eps))
	    (< (abs (- x y)) eps))
   :hints (("Goal"
	    :use ((:instance small-<-non-small
			     (x (- x y))
			     (y eps))
		  (:instance standard-small-is-zero
			     (x eps)))
	    :in-theory (e/d (i-close)
			     (small-<-non-small))))
   ))

(defthm realp-riemann-rifn
  (implies (partitionp p)
	   (REALP (RIEMANN-RIFN P))))

(local
 (defthmd rifn-is-integrable-hyperreal-step-1
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn))
		 (inside-interval-p b (domain-rifn))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs (- (riemann-rifn p)
		       (strict-int-rifn a b)))
	       eps))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance strict-int-rifn-is-integral-of-rifn)
		  (:instance close-<-abs-small-eps
			     (x (riemann-rifn p))
			     (y (strict-int-rifn a b))
			     (eps eps))
		  )
	    :in-theory (disable strict-int-rifn-is-integral-of-rifn
				riemann-rifn
				abs)
	    )
	   )))

(local
 (defthm abs-mesh
   (implies (partitionp p)
	    (equal (abs (mesh p)) (mesh p)))))

(local
 (defthm linear-abs
   (<= x (abs x))
   :rule-classes (:linear)))

(local
 (defthm realp-abs
   (implies (realp x)
	    (realp (abs x)))
   :rule-classes (:type-prescription)))

(local
 (defthmd rifn-is-integrable-hyperreal-step-2
   (implies (and (standardp a)
		 (standardp b)
		 (<= a b)
		 (inside-interval-p a (domain-rifn))
		 (inside-interval-p b (domain-rifn))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (realp delta)
		 (i-small delta)
		 (< (mesh p) delta)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs (- (riemann-rifn p)
		       (strict-int-rifn a b)))
	       eps))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance rifn-is-integrable-hyperreal-step-1)
		  (:instance (:instance small-if-<-small
			     (x delta)
			     (y (mesh p))))
		  )
	    :in-theory (e/d (i-close)
			    (small-if-<-small
			     small-<-non-small
			     riemann-rifn
			     mesh
			     partitionp
			     abs)
	    )
	   ))))

(defun-sk forall-partitions-riemann-sum-is-close-to-int-rifn (a b eps delta)
   (forall (p)
	   (implies (and (<= a b)
			 (partitionp p)
			 (equal (car p) a)
			 (equal (car (last p)) b)
			 (< (mesh p) delta))
		    (< (abs (- (riemann-rifn p)
			       (strict-int-rifn a b)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-so-that-riemann-sum-is-close-to-int-rifn (a b eps)
   (exists (delta)
	   (implies (and (inside-interval-p a (domain-rifn))
			 (inside-interval-p b (domain-rifn))
			 (<= a b)
			 (realp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-partitions-riemann-sum-is-close-to-int-rifn a b eps delta)))))

(defthm-std rifn-is-integrable-hyperreal
  (implies (and (<= a b)
		(inside-interval-p a (domain-rifn))
		(inside-interval-p b (domain-rifn))
		(realp eps)
		(< 0 eps))
	   (exists-delta-so-that-riemann-sum-is-close-to-int-rifn a b eps))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance rifn-is-integrable-hyperreal-step-2
			    (p (forall-partitions-riemann-sum-is-close-to-int-rifn-witness
				a b eps (/ (i-large-integer))))
			    (delta (/ (i-large-integer))))
		 (:instance exists-delta-so-that-riemann-sum-is-close-to-int-rifn-suff
			    (delta (/ (i-large-integer))))
		 )
	   :in-theory (e/d (i-close)
			   (riemann-rifn
			    mesh
			    partitionp
			    abs)
			   )
	   )))
