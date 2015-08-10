(in-package "ACL2")

(include-book "nonstd/nsa/continuity" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

(include-book "integrable-functions")
(include-book "make-partition")


(defun map-rcfn (p)
  (if (consp p)
      (cons (rcfn (car p))
	    (map-rcfn (cdr p)))
    nil))

(defun riemann-rcfn (p)
  (dotprod (deltas p)
	   (map-rcfn (cdr p))))

(local
 (defun map-const (p y)
   (if (consp p)
       (cons y
	     (map-const (cdr p) y))
     nil)))

(defun rcfn-max-x (a b)
  (if (and (realp a)
	   (realp b))
      (if (< a b)
	  (find-max-rcfn-x a b)
	(if (< b a)
	    (find-max-rcfn-x b a)
	  b))
    b))

(defthm max-x-is-max
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(<= a b))
	   (<= (rcfn x)
	       (rcfn (rcfn-max-x a b)))))

(defthm realp-max
  (implies (and (realp a)
		(realp b))
	   (realp (rcfn-max-x a b))))

(defthm max-between-a-and-b-1
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(<= a b)
		)
	   (and (<= a (rcfn-max-x a b))
		(<= (rcfn-max-x a b) b)))
  :rule-classes (:linear :rewrite)
  )

(defthm max-between-a-and-b-2
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(< b a)
		)
	   (and (<= b (rcfn-max-x a b))
		(<= (rcfn-max-x a b) a)))
  :rule-classes (:linear :rewrite)
  )

(local
 (defthmd find-max-rcfn-x-sub-interval-1
   (implies (and (realp a1)
		 (realp a2)
		 (realp b1)
		 (realp b2)
		 (<= a1 a2)
		 (<= b2 b1)
		 (< a2 b2)
		 (inside-interval-p a1 (rcfn-domain))
		 (inside-interval-p b1 (rcfn-domain)))
	    (<= (rcfn (find-max-rcfn-x a2 b2))
		(rcfn (find-max-rcfn-x a1 b1))))
   :hints (("Goal"
	    :use ((:instance find-max-rcfn-x-inside-interval
			     (a a2)
			     (b b2)
			     (interval (interval a1 b1)))
		  (:instance find-max-rcfn-is-maximum
			     (a a1)
			     (b b1)
			     (x (find-max-rcfn-x a2 b2))))
	    :in-theory (e/d (interval-definition-theory)
				       (find-max-rcfn-x-inside-interval
					find-max-rcfn-is-maximum))))))

(local
 (defthmd max-x-sub-interval
   (implies (and (realp a1)
		 (realp a2)
		 (realp b1)
		 (realp b2)
		 (<= a1 a2)
		 (<= b2 b1)
		 (<= a2 b2)
		 (inside-interval-p a1 (rcfn-domain))
		 (inside-interval-p b1 (rcfn-domain)))
	    (<= (rcfn (rcfn-max-x a2 b2))
		(rcfn (rcfn-max-x a1 b1))))
   :hints (("Goal"
	    :use ((:instance find-max-rcfn-x-sub-interval-1))))))

(in-theory (disable rcfn-max-x))

(local
 (defun riemann-max-rcfn (p)
   (dotprod (deltas p)
	    (map-const (cdr p)
		       (rcfn (rcfn-max-x (car p)
				    (car (last p))))))))

(local
 (defun point-wise-<= (xs ys)
   (if (consp xs)
       (and (realp (car xs))
	    (realp (car ys))
	    (<= (car xs)
		(car ys))
	    (point-wise-<= (cdr xs) (cdr ys)))
     (not (consp ys)))))

(local
 (defun nonneg-listp (l)
   (if (atom l)
       (eq l nil)
     (and (realp (car l))
	  (<= 0 (car l))
	  (nonneg-listp (cdr l))))))

(local
 (defthm sumlist-point-wise-<=
   (implies (point-wise-<= xs ys)
	    (<= (sumlist xs)
		(sumlist ys)))))

(local
 (defthm maptimes-point-wise-<=
   (implies (and (nonneg-listp xs)
		 (point-wise-<= ys zs))
	    (point-wise-<= (map-times xs ys)
			   (map-times xs zs)))
   ))

(local
 (defthm point-wise-<=-implies-dotprod-bounded-2
   (implies (and (point-wise-<= ys zs)
		 (nonneg-listp xs))
	    (<= (dotprod xs ys)
		(dotprod xs zs)))
   ))

(local
 (defthm nonneg-listp-deltas
   (implies (partitionp p)
	    (nonneg-listp (deltas p)))))

(local
 (defthm real-last-partition
   (implies (partitionp p)
	    (realp (car (last p))))))

(local
 (defthm partition-first-inside-domain-hint
   (implies (and (partitionp p)
		 (consp p))
	    (<= (car p) (car (last p))))))

(local
 (defthm partition-second-inside-domain-hint
   (implies (and (partitionp p)
		 (consp p)
		 (consp (cdr p)))
	    (and (< (car p) (cadr p))
		 (<= (cadr p) (car (last p)))))))


(local
 (defthm partition-second-inside-domain
   (implies (and (partitionp p)
		 (interval-p interval)
		 (inside-interval-p (car p) interval)
		 (inside-interval-p (car (last p)) interval)
		 (consp p)
		 (consp (cdr p)))
	    (inside-interval-p (cadr p) interval))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance inside-interval-p-squeeze
			     (a (car p))
			     (b (car (last p)))
			     (c (cadr p)))
		  (:instance partition-second-inside-domain-hint)
		  )))
   ))

(local
 (defthm expand-map-const-nil
   (implies (and (consp p)
		 (not (consp (cdr p))))
	    (equal (map-const p y)
		   (list y)))))

(local
 (defthm point-wise-<=-transitive
   (implies (and (point-wise-<= xs ys)
		 (point-wise-<= ys zs))
	    (point-wise-<= xs zs))))

(local
 (defthm point-wise-<=-map-const
   (implies (and (realp y1)
		 (realp y2)
		 (<= y1 y2))
	    (point-wise-<= (map-const p y1)
			   (map-const p y2)))))

(local
 (defthm point-wise-<=-map-rcfn-map-max-rcfn
   (implies (and (partitionp p)
		 (inside-interval-p (car p) (rcfn-domain))
		 (inside-interval-p (car (last p)) (rcfn-domain)))
	    (point-wise-<= (map-rcfn p)
			   (map-const p
				      (rcfn (rcfn-max-x (car p)
						   (car (last p)))))))
   :hints (("Subgoal *1/2"
	    :use ((:instance max-x-is-max
			     (a (car p))
			     (b (car (last (cdr p))))
			     (x (car p)))
		  (:instance partition-first-inside-domain-hint)
		  (:instance point-wise-<=-transitive
			     (xs (map-rcfn (cdr p)))
			     (ys (map-const (cdr p)
					    (rcfn (rcfn-max-x (cadr p) (car (last (cdr p)))))))
			     (zs (map-const (cdr p)
					    (rcfn (rcfn-max-x (car p) (car (last (cdr p))))))))
		  (:instance point-wise-<=-map-const
			     (p p)
			     (y1 (rcfn (rcfn-max-x (cadr p) (car (last (cdr p))))))
			     (y2 (rcfn (rcfn-max-x (car p) (car (last (cdr p)))))))
		  (:instance partition-second-inside-domain-hint)
		  (:instance max-x-sub-interval
			     (a1 (car p))
			     (a2 (cadr p))
			     (b1 (car (last (cdr p))))
			     (b2 (car (last (cdr p)))))
		  )
	    :in-theory (disable max-x-is-max
				partition-first-inside-domain-hint
				point-wise-<=-transitive
				point-wise-<=-map-const
				partition-second-inside-domain-hint)
	    ))
   ))

(local
 (defun dotprod-bounded-hint (xs ys zs)
   (if (consp xs)
       (dotprod-bounded-hint (cdr xs) (cdr ys) (cdr zs))
     (list xs ys zs))))

(local
 (defthm riemann-rcfn-bounded-above-lemma
   (implies (and (partitionp p)
		 (inside-interval-p (car p) (rcfn-domain))
		 (inside-interval-p (car (last p)) (rcfn-domain)))
	    (<= (riemann-rcfn p)
		(riemann-max-rcfn p)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance point-wise-<=-implies-dotprod-bounded-2
			     (xs (deltas p))
			     (ys (map-rcfn (cdr p)))
			     (zs (map-const (cdr p)
					    (rcfn (rcfn-max-x (car p)
							 (car (last p)))))))
		  (:instance point-wise-<=-map-rcfn-map-max-rcfn
			     (p p))
		  )
	    :in-theory (disable deltas
				rcfn-max-x)
	    ))
   ))

(local
 (defthmd dotprod-recursion
   (implies (consp xs)
	    (equal (dotprod xs ys)
		   (+ (* (car xs) (car ys))
		      (dotprod (cdr xs) (cdr ys)))))))


(local
 (defthmd simplify-riemann-max-rcfn-lemma
   (implies (partitionp p)
	    (equal (dotprod (deltas p)
			    (map-const (cdr p) k))
		   (* k
		      (- (car (last p))
			 (car p)))))
   ))

(local
 (defthmd simplify-riemann-max-rcfn
   (implies (partitionp p)
	    (equal (riemann-max-rcfn p)
		   (* (rcfn (rcfn-max-x (car p) (car (last p))))
		      (- (car (last p))
			 (car p)))))
   :hints (("goal"
	    :use ((:instance simplify-riemann-max-rcfn-lemma
			     (p p)
			     (k (rcfn (rcfn-max-x (car p) (car (last p)))))))))
   ))


(defthm riemann-rcfn-bounded-above
  (implies (and (partitionp p)
		(inside-interval-p (car p) (rcfn-domain))
		(inside-interval-p (car (last p)) (rcfn-domain)))
	   (<= (riemann-rcfn p)
	       (* (rcfn (rcfn-max-x (car p) (car (last p))))
		  (- (car (last p))
		     (car p)))))
  :hints (("Goal"
	   :use ((:instance simplify-riemann-max-rcfn)
		 (:instance riemann-rcfn-bounded-above-lemma))))
  )

(defun rcfn-min-x (a b)
  (if (and (realp a)
	   (realp b))
      (if (< a b)
	  (find-min-rcfn-x a b)
	(if (< b a)
	    (find-min-rcfn-x b a)
	  b))
    b))

(defthm min-x-is-min
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(realp x)
		(<= a x)
		(<= x b)
		(<= a b))
	   (<= (rcfn (rcfn-min-x a b))
	       (rcfn x))))

(defthm realp-min
  (implies (and (realp a)
		(realp b))
	   (realp (rcfn-min-x a b))))

(defthm min-between-a-and-b-1
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(<= a b)
		)
	   (and (<= a (rcfn-min-x a b))
		(<= (rcfn-min-x a b) b)))
  :rule-classes (:linear :rewrite)
  )

(defthm min-between-a-and-b-2
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(< b a)
		)
	   (and (<= b (rcfn-min-x a b))
		(<= (rcfn-min-x a b) a)))
  :rule-classes (:linear :rewrite)
  )

(local
 (defthmd find-min-rcfn-x-sub-interval-1
   (implies (and (realp a1)
		 (realp a2)
		 (realp b1)
		 (realp b2)
		 (<= a1 a2)
		 (<= b2 b1)
		 (< a2 b2)
		 (inside-interval-p a1 (rcfn-domain))
		 (inside-interval-p b1 (rcfn-domain)))
	    (<= (rcfn (find-min-rcfn-x a1 b1))
		(rcfn (find-min-rcfn-x a2 b2))))
   :hints (("Goal"
	    :use ((:instance find-min-rcfn-x-inside-interval
			     (a a2)
			     (b b2)
			     (interval (interval a1 b1)))
		  (:instance find-min-rcfn-is-minimum
			     (a a1)
			     (b b1)
			     (x (find-min-rcfn-x a2 b2))))
	    :in-theory (e/d (interval-definition-theory)
				       (find-min-rcfn-x-inside-interval
					find-min-rcfn-is-minimum))))))

(local
 (defthmd min-x-sub-interval
   (implies (and (realp a1)
		 (realp a2)
		 (realp b1)
		 (realp b2)
		 (<= a1 a2)
		 (<= b2 b1)
		 (<= a2 b2)
		 (inside-interval-p a1 (rcfn-domain))
		 (inside-interval-p b1 (rcfn-domain)))
	    (<= (rcfn (rcfn-min-x a1 b1))
		(rcfn (rcfn-min-x a2 b2))))
   :hints (("Goal"
	    :use ((:instance find-min-rcfn-x-sub-interval-1))))))


(in-theory (disable rcfn-min-x))

(local
 (defun riemann-min-rcfn (p)
   (dotprod (deltas p)
	    (map-const (cdr p)
		       (rcfn (rcfn-min-x (car p)
				    (car (last p))))))))

(local
 (defthm point-wise-<=-map-rcfn-map-min-rcfn
   (implies (and (partitionp p)
		 (inside-interval-p (car p) (rcfn-domain))
		 (inside-interval-p (car (last p)) (rcfn-domain)))
	    (point-wise-<= (map-const p
				      (rcfn (rcfn-min-x (car p)
						   (car (last p)))))
			   (map-rcfn p)))
   :hints (("Subgoal *1/2"
	    :use ((:instance min-x-is-min
			     (a (car p))
			     (b (car (last (cdr p))))
			     (x (car p)))
		  (:instance partition-first-inside-domain-hint)
		  (:instance point-wise-<=-transitive
			     (xs (map-const (cdr p)
					    (rcfn (rcfn-min-x (car p) (car (last (cdr p)))))))
			     (ys (map-const (cdr p)
					    (rcfn (rcfn-min-x (cadr p) (car (last (cdr p)))))))
			     (zs (map-rcfn (cdr p))))
		  (:instance point-wise-<=-map-const
			     (p p)
			     (y1 (rcfn (rcfn-min-x (car p) (car (last (cdr p))))))
			     (y2 (rcfn (rcfn-min-x (cadr p) (car (last (cdr p)))))))
		  (:instance partition-second-inside-domain-hint)
		  (:instance min-x-sub-interval
			     (a1 (car p))
			     (a2 (cadr p))
			     (b1 (car (last (cdr p))))
			     (b2 (car (last (cdr p)))))
		  )
	    :in-theory (disable min-x-is-min
				partition-first-inside-domain-hint
				point-wise-<=-transitive
				point-wise-<=-map-const
				partition-second-inside-domain-hint)
	    ))
   ))

(local
 (defthm riemann-rcfn-bounded-below-lemma
   (implies (and (partitionp p)
		 (inside-interval-p (car p) (rcfn-domain))
		 (inside-interval-p (car (last p)) (rcfn-domain)))
	    (<= (riemann-min-rcfn p)
		(riemann-rcfn p)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance point-wise-<=-implies-dotprod-bounded-2
			     (xs (deltas p))
			     (ys (map-const (cdr p)
					    (rcfn (rcfn-min-x (car p)
							 (car (last p))))))
			     (zs (map-rcfn (cdr p))))
		  (:instance point-wise-<=-map-rcfn-map-min-rcfn
			     (p p))
		  )
	    :in-theory (disable deltas
				rcfn-max-x)
	    ))
   ))

(local
 (defthmd simplify-riemann-min-rcfn
   (implies (partitionp p)
	    (equal (riemann-min-rcfn p)
		   (* (rcfn (rcfn-min-x (car p) (car (last p))))
		      (- (car (last p))
			 (car p)))))
   :hints (("goal"
	    :use ((:instance simplify-riemann-max-rcfn-lemma
			     (p p)
			     (k (rcfn (rcfn-min-x (car p) (car (last p)))))))))
   ))


(defthm riemann-rcfn-bounded-below
  (implies (and (partitionp p)
		(inside-interval-p (car p) (rcfn-domain))
		(inside-interval-p (car (last p)) (rcfn-domain)))
	   (<= (* (rcfn (rcfn-min-x (car p) (car (last p))))
		  (- (car (last p))
		     (car p)))
	       (riemann-rcfn p)))
  :hints (("Goal"
	   :use ((:instance simplify-riemann-min-rcfn)
		 (:instance riemann-rcfn-bounded-below-lemma))))
  )

(local
 (defthm-std lower-bound-is-standard
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (* (rcfn (rcfn-min-x a b))
			  (- b a))))))


(local
 (defthm-std upper-bound-is-standard
      (implies (and (standardp a)
		    (standardp b))
	       (standardp (* (rcfn (rcfn-max-x a b))
			     (- b a))))))

(local
 (defthmd strict-int-rcfn-body-bounded
   (implies (and (realp a)
		 (realp b)
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (< a b))
	    (and (<= (* (rcfn (rcfn-min-x a b))
			(- b a))
		     (riemann-rcfn (make-small-partition a b)))
		 (<= (riemann-rcfn (make-small-partition a b))
		     (* (rcfn (rcfn-max-x a b))
			(- b a)))))
   :hints (("Goal"
	    :use ((:instance riemann-rcfn-bounded-below
			     (p (make-small-partition a b)))
		  (:instance riemann-rcfn-bounded-above
			     (p (make-small-partition a b)))
		  (:instance car-make-small-partition)
		  (:instance car-last-make-small-partition)
		  (:instance partitionp-make-small-partition))
	    :in-theory (disable car-make-small-partition
				car-last-make-small-partition
				partitionp-make-small-partition)))))

(defthm realp-riemann-rcfn
  (implies (partitionp p)
	   (realp (riemann-rcfn p))))

(defthm limited-riemann-rcfn-small-partition
  (implies (and (realp a) (standardp a)
		(realp b) (standardp b)
		(inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(< a b))
	   (i-limited (riemann-rcfn (make-small-partition a b))))
  :hints (("Goal"
	   :use ((:instance limited-squeeze
			    (a (* (rcfn (rcfn-min-x a b))
				  (- b a)))
			    (b (* (rcfn (rcfn-max-x a b))
				  (- b a)))
			    (x (riemann-rcfn (make-small-partition a b))))
		 (:instance strict-int-rcfn-body-bounded)
		 (:instance lower-bound-is-standard)
		 (:instance upper-bound-is-standard)
		 )
	   :in-theory (disable limited-squeeze
			       rcfn-min-x
			       rcfn-max-x
			       riemann-rcfn))))

(encapsulate
 nil

 (local (in-theory (disable riemann-rcfn)))

 (defun-std strict-int-rcfn (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (rcfn-domain))
	    (inside-interval-p b (rcfn-domain))
	    (< a b))
       (standard-part (riemann-rcfn (make-small-partition a b)))
     0))
 )

(defthm-std strict-int-rcfn-bounded
   (implies (and (realp a)
		 (realp b)
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (< a b))
	    (and (<= (* (rcfn (rcfn-min-x a b))
			(- b a))
		     (strict-int-rcfn a b))
		 (<= (strict-int-rcfn a b)
		     (* (rcfn (rcfn-max-x a b))
			(- b a)))))
   :hints (("Goal"
	    :use ((:instance strict-int-rcfn-body-bounded)
 		  (:instance standard-part-<=
			     (x (* (rcfn (rcfn-min-x a b))
				   (- b a)))
			     (y (riemann-rcfn (make-small-partition a b))))
 		  (:instance standard-part-<=
			     (x (riemann-rcfn (make-small-partition a b)))
			     (y (* (rcfn (rcfn-max-x a b))
				   (- b a))))
		  (:instance lower-bound-is-standard)
		  (:instance upper-bound-is-standard)
		  (:instance standard-part-of-standardp
			     (x (* (rcfn (rcfn-min-x a b))
				   (- b a))))
		  (:instance standard-part-of-standardp
			     (x (* (rcfn (rcfn-max-x a b))
				   (- b a))))
		  )
	    :in-theory (disable strict-int-rcfn-body-bounded
				standard-part-<=
				standard-part-of-standardp
				lower-bound-is-standard
				upper-bound-is-standard
				riemann-rcfn))
	   ))



(defun next-gte (x p)
  ;; next member of partition p that is greater than or equal to x
  (if (<= x (car p))
      (car p)
    (if (consp p)
        (next-gte x (cdr p))
      nil)))

(defun map-rcfn-refinement (p1 p2)
  ;; p1 should be a refinement of p2
  (if (consp p1)
      (cons (rcfn (next-gte (car p1) p2))
            (map-rcfn-refinement (cdr p1) p2))
    nil))

(defun riemann-rcfn-refinement (p1 p2)
  ;; p1 should be a refinement of p2
  (dotprod (deltas p1)
           (map-rcfn-refinement (cdr p1) p2)))

(defun abslist (x)
  ;; pointwise absolute values of list x
  (if (consp x)
      (cons (abs (car x))
            (abslist (cdr x)))
    nil))

(defthm abslist-deltas
  ;; trivial lemma saying that each delta is non-negative
  (implies (partitionp p)
           (equal (abslist (deltas p)) (deltas p))))

(defun difflist (x y)
  (if (consp x)
      (cons (- (car x) (car y))
            (difflist (cdr x) (cdr y)))
    nil))

(defun bounded-by (lst a)
  (if (consp lst)
      (and (<= (abs (car lst)) a)
           (bounded-by (cdr lst) a))
    t))

(local
 (defthm cdr-difflist
   (equal (cdr (difflist ys zs))
	  (difflist (cdr ys) (cdr zs)))))

(local
 (defthm car-difflist
   (equal (car (difflist ys zs))
	  (if (consp ys)
	      (- (car ys) (car zs))
	    nil)
	  )))

(local
 (defthm dotprod-deltas-bounded-by
   (implies (and (real-listp xs)
		 (real-listp ys)
		 (real-listp zs)
		 (equal (len xs) (len ys)))
	    (equal (- (dotprod xs ys)
		      (dotprod xs zs))
		   (dotprod xs
			    (difflist ys zs))))
   :hints (("Goal"
	    :induct (dotprod-bounded-hint xs ys zs))
	   ("Subgoal *1/1"
	    :use ((:instance dotprod-recursion
			     (xs xs)
			     (ys (difflist ys zs))
			     )
		  (:instance dotprod-recursion
			     (xs xs)
			     (ys ys)
			     )
		  (:instance dotprod-recursion
			     (xs xs)
			     (ys zs)
			     ))
	    :in-theory (disable dotprod)))
   ))

(local
 (defthm nth-index-map-rcfn
   (implies (and (<= 0 index)
		 (< index (len p)))
	    (equal (nth index (map-rcfn p))
		   (rcfn (nth index p))))))

(local
 (defthm nth-index-map-rcfn-refinement
   (implies (and (<= 0 index)
		 (< index (len p1)))
	    (equal (nth index (map-rcfn-refinement p1 p2))
		   (rcfn (next-gte (nth index p1) p2))))))

(local
 (defthm next-gte-is-within-mesh
   (implies (and (partitionp p)
		 (<= (car p) x)
		 (<= x (car (last p)))
		 (realp x))
	    (<= (abs (- x (next-gte x p)))
		(mesh p)))
   :rule-classes (:linear :rewrite)))

(local
 (defthm next-gte-lower-bound
   (implies (and (partitionp p)
		 (<= (car p) x)
		 (<= x (car (last p)))
		 (realp x))
	    (<= x (next-gte x p)))
   :rule-classes (:linear :rewrite)))

(local
 (defthm next-gte-case-2
   (implies (and (< (car p) x)
		 (< x (cadr p)))
	    (equal (next-gte x p)
		   (cadr p)))))

(local
 (defthm next-gte-upper-bound
   (implies (and (partitionp p)
		 (<= (car p) x)
		 (<= x (car (last p)))
		 (realp x))
	    (<= (next-gte x p)
		(car (last p))))
   :rule-classes (:linear :rewrite)))

(local
 (defthm realp-next-gte-type-prescription
   (implies (and (partitionp p)
		 (<= a (car (last p))))
	    (realp (next-gte a p)))
   :rule-classes :type-prescription))

(local
 (defthm realp-mesh
   (implies (partitionp p)
	    (realp (mesh p)))))

(local
 (defthm abs-mesh
   (implies (partitionp p)
	    (equal (abs (mesh p))
		   (mesh p)))))

(local
 (defthmd next-gte-close
   (implies (and (partitionp p2)
		 (realp (car p2))
		 (realp (car (last p2)))
		 (standardp (car p2))
		 (standardp (car (last p2)))
		 (i-small (mesh p2))
		 (<= (car p2) x)
		 (<= x (car (last p2)))
		 (realp x))
	    (i-close x (next-gte x p2)))
   :hints (("Goal"
	    :use ((:instance small-if-<-small
			     (x (mesh p2))
			     (y (- x (next-gte x p2))))
		  (:instance next-gte-is-within-mesh
			     (p p2)
			     (x x)))
	    :in-theory (e/d (i-close)
			    (abs
			     mesh
			     last
			     next-gte
			     partitionp
			     small-if-<-small
			     next-gte-is-within-mesh))))))



(local
 (defthm subinterval-is-interval
   (implies (subinterval-p subinterval interval)
	    (interval-p subinterval))
   :hints (("Goal"
	    :in-theory '(subinterval-p)))))

(defthm rcfn-uniformly-continuous-2
  (implies (and (standardp interval)
		(subinterval-p interval (rcfn-domain))
		(interval-left-inclusive-p interval)
		(interval-right-inclusive-p interval)
		(inside-interval-p x interval)
		(i-close x y)
		(inside-interval-p y interval))
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
			    (interval interval))
		 (:instance inside-standard-bounded-intervals-are-limited
			    (x x)
			    (interval interval))
		 )
	   :in-theory (disable rcfn-continuous i-close-transitive
			       i-close-symmetric
			       standard-part-inside-interval
			       inside-standard-bounded-intervals-are-limited))))

(local
 (defthm-std standard-interval
   (implies (and (standardp a)
		 (standardp b))
	    (standardp (interval a b)))))

(local
 (defthm endpoint-inside-closed-interval
   (implies (and (realp a)
		 (realp b)
		 (realp x)
		 (<= a x)
		 (<= x b)
		 )
	    (inside-interval-p x (interval a b)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthmd rcfn-next-gte-close
   (implies (and (partitionp p2)
		 (standardp (car p2))
		 (standardp (car (last p2)))
		 (inside-interval-p (car p2) (rcfn-domain))
		 (inside-interval-p (car (last p2)) (rcfn-domain))
		 (i-small (mesh p2))
		 (<= (car p2) x)
		 (<= x (car (last p2)))
		 (realp x))
	    (i-close (rcfn x) (rcfn (next-gte x p2))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance next-gte-close
			     (p2 p2)
			     (x x))
		  (:instance rcfn-uniformly-continuous-2
			     (x x)
			     (y (next-gte x p2))
			     (interval (interval (car p2)
						 (car (last p2))))
			     )
		  )
	    :in-theory (disable next-gte partitionp2 mesh
				rcfn-uniformly-continuous)))
   ))

(local
 (defun dotprod-bounded-2-hint (xs ys)
   (if (consp xs)
       (dotprod-bounded-2-hint (cdr xs) (cdr ys))
     (list xs ys))))

#|
(local
 (defthm cdr-abslist
   (implies (consp xs)
	    (equal (cdr (abslist xs))
		   (abslist (cdr xs))))))

(local
 (defthm car-abslist
   (implies (consp xs)
	    (equal (car (abslist xs))
		   (abs (car xs))))))

(local
 (defthm nil-abslist
   (implies (not (consp xs))
	    (equal (abslist xs)
		   nil))))

(local
 (defthm consp-abslist
   (equal (consp (abslist xs))
	  (consp xs))))
|#

(local
 (defthm abslist-sumlist
   (<= (abs (sumlist xs))
       (sumlist (abslist xs)))))

(local
 (defthm abslist-map-times
   (implies (and (real-listp xs)
		 (real-listp ys)
		 )
	    (equal (map-times (abslist xs)
			      (abslist ys))
		   (abslist (map-times xs ys))))
   ))

(local
 (defthmd abs-dotprod-1
   (implies (and (real-listp xs)
		 (real-listp ys))
	    (<= (abs (dotprod xs ys))
		(dotprod (abslist xs)
			 (abslist ys))))
   :hints (("Goal"
	    :do-not-induct t
	    :in-theory (disable abs sumlist map-times)
	    ))
   ))

(local
 (defthm real-listp-deltas
   (implies (partitionp p)
	    (real-listp (deltas p)))))

(local
 (defthm real-listp-difflist
   (implies (and (real-listp xs)
		 (real-listp ys))
	    (real-listp (difflist xs ys)))))

(local
 (defthm real-listp-abslist
   (implies (real-listp xs)
	    (real-listp (abslist xs)))))

(local
 (defthm abs-dotprod-deltas-1
   (implies (and (partitionp p)
		 (real-listp ys)
		 (real-listp zs)
		 (equal (len (deltas p)) (len ys)))
	    (<= (abs (- (dotprod (deltas p) ys)
			(dotprod (deltas p) zs)))
		(dotprod (deltas p)
			 (abslist (difflist ys zs)))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-1
			     (xs (deltas p))
			     (ys (difflist ys zs)))
		  (:instance dotprod-deltas-bounded-by
			     (xs (deltas p))
			     (ys ys)
			     (zs zs)))
	    :in-theory (disable abs
				dotprod-deltas-bounded-by
				abs-dotprod-1)))))

#|
(local
 (defthm point-wise-<=-implies-dotprod-bounded-2
   (implies (and (point-wise-<= ys zs)
		 (nonneg-listp xs))
	    (<= (dotprod xs ys)
		(dotprod xs zs)))
   ))
|#

(local
 (defthm real-maxlist
   (implies (real-listp xs)
	    (realp (maxlist xs)))))

(local
 (defthm list-point-lise-<=-const-maxlist
   (implies (real-listp xs)
	    (point-wise-<= xs
			   (map-const xs
				      (maxlist xs))))))

(local
 (defthm abs-dotprod-deltas-2
   (implies (and (partitionp p)
		 (real-listp ys)
		 (real-listp zs)
		 (equal (len (deltas p)) (len ys)))
	    (<= (abs (- (dotprod (deltas p) ys)
			(dotprod (deltas p) zs)))
		(dotprod (deltas p)
			 (map-const (abslist (difflist ys zs))
				    (maxlist (abslist (difflist ys zs)))))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-deltas-1)
		  (:instance list-point-lise-<=-const-maxlist
			     (xs (abslist (difflist ys zs))))
		  (:instance point-wise-<=-implies-dotprod-bounded-2
			     (xs (deltas p))
			     (ys (abslist (difflist ys zs)))
			     (zs (map-const (abslist (difflist ys zs))
					    (maxlist (abslist (difflist ys zs)))))))
	    :in-theory (disable dotprod
				maxlist
				abslist
				abs
				difflist
				deltas
				abs-dotprod-deltas-1
				point-wise-<=-implies-dotprod-bounded-2)))))

(local
 (defthmd map-const-equal-len
   (implies (equal (len xs) (len ys))
	    (equal (map-const xs k)
		   (map-const ys k)))
   :hints (("Goal"
	    :induct (dotprod-bounded-2-hint xs ys)))
   ))

(local
 (defthm len-abslist
   (equal (len (abslist xs))
	  (len xs))))



(local
 (defthm len-difflist
   (equal (len (difflist xs ys))
	  (len xs))))

(local
 (defthm len-deltas
   (implies (partitionp p)
	    (equal (len (deltas p))
		   (len (cdr p))))))

(local
 (defthm abs-dotprod-deltas-3
   (implies (and (partitionp p)
		 (real-listp ys)
		 (real-listp zs)
		 (equal (len (deltas p)) (len ys)))
	    (<= (abs (- (dotprod (deltas p) ys)
			(dotprod (deltas p) zs)))
		(dotprod (deltas p)
			 (map-const (cdr p)
				    (maxlist (abslist (difflist ys zs)))))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-deltas-2)
		  (:instance map-const-equal-len
			     (xs (cdr p))
			     (ys (abslist (difflist ys zs)))
			     (k (maxlist (abslist (difflist ys zs)))))
		  )
	    :in-theory (disable dotprod
				maxlist
				abslist
				abs
				difflist
				deltas
				abs-dotprod-deltas-1
				abs-dotprod-deltas-2)))))

(local
 (defun span (p)
   (- (car (last p)) (car p))))

(local
 (defthm span-nonneg
   (implies (partitionp p)
	    (and (realp (span p))
		 (<= 0 (span p))))
   :rule-classes (:type-prescription :rewrite)
   ))

(local
 (defthm span-positive
   (implies (and (partitionp p)
		 (consp (cdr p)))
	    (and (realp (span p))
		 (< 0 (span p))))
   :rule-classes (:type-prescription :rewrite)))

(local
 (defthm span-zero
   (implies (and (partitionp p)
		 (not (consp (cdr p))))
	    (and (realp (span p))
		 (equal (span p) 0)))
   :rule-classes (:type-prescription :rewrite)))

(local
 (defthm span-limited
   (implies (and (partitionp p)
		 (standardp (car p))
		 (standardp (car (last p))))
	    (i-limited (span p)))))

(local
 (in-theory (disable span)))

(local
 (defthm abs-dotprod-deltas-4
   (implies (and (partitionp p)
		 (real-listp ys)
		 (real-listp zs)
		 (equal (len (deltas p)) (len ys)))
	    (<= (abs (- (dotprod (deltas p) ys)
			(dotprod (deltas p) zs)))
		(* (maxlist (abslist (difflist ys zs)))
		   (span p))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-deltas-3)
		  (:instance simplify-riemann-max-rcfn-lemma
			     (p p)
			     (k (maxlist (abslist (difflist ys zs))))))
	    :in-theory '(span)))))

(local
 (defun index-for-large-element (list bound)
   (if (consp list)
       (if (>= (car list) bound)
	   0
	 (1+ (index-for-large-element (cdr list) bound)))
     0)))

(local
 (defthmd index-for-large-element-works
   (let ((index (index-for-large-element list bound)))
     (implies (< 0 bound)
	      (iff (< (maxlist list) bound)
		   (or (not (< index (len list)))
		       (< (nth index list)
			  bound)))))))

(local
 (defthm index-for-large-element-works-better-lemma
   (implies (and (consp list)
		 (real-listp list)
		 (<= (maxlist list) (car list)))
	    (equal (maxlist list) (car list)))))

(local
 (defthm index-for-large-element-works-better-lemma-2
   (implies (and (consp list)
		 (real-listp list)
		 (< (car list) (maxlist list)))
	    (equal (maxlist list) (maxlist (cdr list))))))

(local
 (defthm index-for-large-element-works-better
   (implies (and (consp list)
		 (nonneg-listp list))
	    (equal (maxlist list)
		   (nth (index-for-large-element list (maxlist list))
			list)))))


(local
 (defthm nonneg-abslist
   (implies (real-listp xs)
	    (nonneg-listp (abslist xs)))))

(local
 (defthm nth-abslist
   (implies (and (<= 0 index)
		 (< index (len list))
		 (real-listp list))
	    (equal (nth index (abslist list))
		   (abs (nth index list))))))

(local
 (defthm nth-difflist
   (implies (and (<= 0 index)
		 (< index (len xs))
		 (real-listp xs)
		 (equal (len xs) (len ys))
		 )
	    (equal (nth index (difflist xs ys))
		   (- (nth index xs)
		      (nth index ys)
		      )))))


(local
 (defthm consp-deltas
   (implies (and (partitionp p)
		 (consp (cdr p)))
	    (consp (deltas p)))))

(local
 (defthm consp-abslist-difflist
   (implies (and (partitionp p)
		 (consp (cdr p))
		 (equal (len (deltas p)) (len ys))
		 (equal (len ys) (len zs)))
	    (consp (abslist (difflist ys zs))))))

(local
 (defthm real-dotprod
   (implies (and (real-listp xs)
		 (real-listp ys))


	    (realp (dotprod xs ys)))))

(local
 (defthm real-abs-dotprod
   (implies (and (real-listp xs)
		 (real-listp ys))
	    (realp (abs (dotprod xs ys))))
   :hints (("Goal"
	    :use ((:instance real-dotprod))
	    :in-theory (disable real-dotprod dotprod)))))

(local
 (defthm dotprod-x-nil
   (implies (and (equal (len xs) (len ys))
		 (not (consp ys)))
	    (equal (dotprod xs ys)
		   0))))

(local
 (defthm dotprod-x-abslist-nil
   (implies (and (equal (len xs) (len ys))
		 (not (consp (abslist ys))))
	    (equal (dotprod xs ys)
		   0))))

(local
 (defthm car-last-single-list
   (implies (and (partitionp p)
		 (not (consp (abslist ys)))
		 (equal (len ys) (len (cdr p))))
	    (equal (car (last p))
		   (car p)))))

(local
 (in-theory (disable index-for-large-element-works-better)))

(local
 (defthmd index-for-large-element-upper-bound
   (implies (and (<= element (maxlist xs))
		 (consp xs)
		 (nonneg-listp xs))
	    (< (index-for-large-element xs element)
	       (len xs)))
   :hints (("Goal"
	    :use ((:instance index-for-large-element-works
			     (list xs)
			     (bound element)))
	    ))))

(local
 (defthm index-for-large-element-upper-bound-better
   (implies (and (consp xs)
		 (nonneg-listp xs))
	    (< (index-for-large-element xs (maxlist xs)) (len xs)))
   :hints (("Goal"
	    :use ((:instance index-for-large-element-upper-bound
			     (element (maxlist xs))))
	    ))))

(local
 (defthm consp-abs-span
   (implies (and (partitionp p)
		 (not (consp (abslist (difflist ys zs))))
		 (equal (len (cdr p)) (len ys)))
	    (equal (span p) 0))))

(local
 (defthm abs-dotprod-deltas-5
   (implies (and (partitionp p)
		 (real-listp ys)
		 (real-listp zs)
		 (equal (len (deltas p)) (len ys))
		 (equal (len ys) (len zs)))
	    (<= (abs (- (dotprod (deltas p) ys)
			(dotprod (deltas p) zs)))
		(* (abs (- (nth (index-for-large-element (abslist (difflist ys zs))
							 (maxlist (abslist (difflist ys zs))))
				ys)
			   (nth (index-for-large-element (abslist (difflist ys zs))
							 (maxlist (abslist (difflist ys zs))))
				zs)))
		   (span p))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-deltas-4)
		  (:instance index-for-large-element-works-better
			     (list (abslist (difflist ys zs))))
		  (:instance index-for-large-element-upper-bound-better
			     (xs (abslist (difflist ys zs))))
		  )
	    :in-theory (disable nth last partitionp real-listp
				deltas dotprod index-for-large-element
				maxlist abs abs-dotprod-deltas-4
				index-for-large-element-works-better
				index-for-large-element-upper-bound-better
				)))))




(local
 (defthm real-listp-map-rcfn
   (real-listp (map-rcfn p1))))

(local
 (defthm real-listp-map-rcfn-refinement
   (real-listp (map-rcfn-refinement p1 p2))))

(local
 (defthm len-map-rcfn
   (equal (len (map-rcfn p))
	  (len p))))

(local
 (defthm len-map-rcfn-refinement
   (equal (len (map-rcfn-refinement p1 p2))
	  (len p1))))

(local
 (defthm abs-dotprod-deltas-6
   (implies (strong-refinement-p p1 p2)
	    (<= (abs (- (dotprod (deltas p1)
				 (map-rcfn (cdr p1)))
			(dotprod (deltas p1)
				 (map-rcfn-refinement (cdr p1) p2))))
		(* (abs (- (nth (index-for-large-element
				 (abslist (difflist (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))
				 (maxlist (abslist (difflist
						    (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))))
				(map-rcfn (cdr p1)))
			   (nth (index-for-large-element
				 (abslist (difflist (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))
				 (maxlist (abslist (difflist
						    (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))))
				(map-rcfn-refinement (cdr p1) p2))))
		   (span p1))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-deltas-5
			     (p p1)
			     (ys (map-rcfn (cdr p1)))
			     (zs (map-rcfn-refinement (cdr p1) p2)))
		  )
	    :in-theory (disable nth last partitionp real-listp
				deltas dotprod index-for-large-element
				maxlist abs abs-dotprod-deltas-5
				index-for-large-element-works-better
				index-for-large-element-upper-bound-better
				)))))

(local
 (defthm abs-dotprod-deltas-7
   (implies (strong-refinement-p p1 p2)
	    (<= (abs (- (dotprod (deltas p1)
				 (map-rcfn (cdr p1)))
			(dotprod (deltas p1)
				 (map-rcfn-refinement (cdr p1) p2))))
		(* (abs (- (rcfn (nth (index-for-large-element
				       (abslist (difflist (map-rcfn (cdr p1))
							  (map-rcfn-refinement (cdr p1) p2)))
				       (maxlist (abslist (difflist
							  (map-rcfn (cdr p1))
							  (map-rcfn-refinement (cdr p1) p2)))))
				      (cdr p1)))
			   (rcfn (next-gte (nth (index-for-large-element
						 (abslist (difflist
							   (map-rcfn (cdr p1))
							   (map-rcfn-refinement (cdr p1) p2)))
						 (maxlist (abslist
							   (difflist
							    (map-rcfn (cdr p1))
							    (map-rcfn-refinement (cdr p1) p2)))))
						(cdr p1))
					   p2))))
		   (span p1))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance abs-dotprod-deltas-6)
		  (:instance nth-index-map-rcfn
			     (index (index-for-large-element
				     (abslist (difflist (map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2)))
				     (maxlist (abslist (difflist
							(map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2))))))
			     (p (cdr p1)))
		  (:instance nth-index-map-rcfn-refinement
			     (index (index-for-large-element
				     (abslist (difflist (map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2)))
				     (maxlist (abslist (difflist
							(map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2))))))
			     (p1 (cdr p1))
			     (p2 p2))
		  (:instance index-for-large-element-upper-bound-better
			     (xs (abslist (difflist (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))))
		  )
	    :in-theory (disable nth last partitionp real-listp
				deltas dotprod index-for-large-element
				maxlist abs abs-dotprod-deltas-6
				index-for-large-element-works-better
				index-for-large-element-upper-bound-better
				nth-index-map-rcfn
				nth-index-map-rcfn-refinement
				next-gte
				abslist difflist
				map-rcfn
				map-rcfn-refinement
				)))))

(local
 (defthm nth-of-partition-in-range
   (implies (and (<= 0 index)
		 (< index (len p))
		 (partitionp p))
	    (and (realp (nth index p))
		 (<= (car p) (nth index p))
		 (<= (nth index p) (car (last p)))))))

#|
(local
 (defthm fine-partition-not-trivial
   (implies (and (partitionp p)
		 (standardp (car p))
		 (standardp (car (last p)))
		 (i-small (mesh p)))
	    (and (consp p)
		 (consp (cdr p))))
   ))
|#

(local
 (defthm trivial-partition
   (implies (and (partitionp p)
		 (not (realp (nth 0 (cdr p)))))
	    (equal (cdr p)
		   nil))))

#|
(local
 (defthm next-gte-nil
   (implies (partitionp p)
	    (equal (next-gte nil p) nil))))
|#

(local
 (defthm realp-nth
   (implies (and (<= 0 index)
		 (< index (len list))
		 (real-listp list))
	    (realp (nth index list)))))

(local
 (defthm real-listp-cdr-partition
   (implies (partitionp p)
	    (real-listp (cdr p)))))

(local
 (defthmd nth-cdr-partition-lower-bound-lemma
   (implies (and (<= 0 index)
		 (< index (len p))
		 (partitionp p))
	    (<= (car p)
		(nth index p))
	    )))

(local
 (defthm nth-cdr-partition-lower-bound
   (implies (and (<= 0 index)
		 (< index (len (cdr p)))
		 (partitionp p))
	    (< (car p)
	       (nth index (cdr p))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance nth-cdr-partition-lower-bound-lemma (p (cdr p))))))
   ))

(local
 (defthmd nth-cdr-partition-upper-bound-lemma
   (implies (and (<= 0 index)
		 (< index (len p))
		 (partitionp p))
	    (<= (nth index p)
		(car (last p)))
	    )))

(local
 (defthm nth-cdr-partition-upper-bound
   (implies (and (<= 0 index)
		 (< index (len (cdr p)))
		 (partitionp p))
	    (<= (nth index (cdr p))
		(car (last p))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance nth-cdr-partition-upper-bound-lemma (p (cdr p))))))
   ))

(local
 (defthmd rcfn-next-gte-close-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (i-close (rcfn (nth (index-for-large-element
				 (abslist (difflist (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))
				 (maxlist (abslist (difflist
						    (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))))
				(cdr p1)))
		     (rcfn (next-gte (nth (index-for-large-element
					   (abslist (difflist
						     (map-rcfn (cdr p1))
						     (map-rcfn-refinement (cdr p1) p2)))
					   (maxlist (abslist
						     (difflist
						      (map-rcfn (cdr p1))
						      (map-rcfn-refinement (cdr p1) p2)))))
					  (cdr p1))
				     p2))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance rcfn-next-gte-close
			     (x (nth (index-for-large-element
				      (abslist (difflist
						(map-rcfn (cdr p1))
						(map-rcfn-refinement (cdr p1) p2)))
				      (maxlist (abslist
						(difflist
						 (map-rcfn (cdr p1))
						 (map-rcfn-refinement (cdr p1) p2)))))
				     (cdr p1)))
			     (p2 p2))
		  (:instance index-for-large-element-upper-bound-better
			     (xs (abslist (difflist (map-rcfn (cdr p1))
						    (map-rcfn-refinement (cdr p1) p2)))))
		  (:instance realp-nth
			     (list (cdr p1))
			     (index (index-for-large-element
				     (abslist (difflist (map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2)))
				     (maxlist (abslist (difflist (map-rcfn (cdr p1))
								 (map-rcfn-refinement (cdr p1) p2)))))))
		  (:instance nth-cdr-partition-lower-bound
			     (p p1)
			     (index (index-for-large-element
				     (abslist (difflist (map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2)))
				     (maxlist (abslist (difflist (map-rcfn (cdr p1))
								 (map-rcfn-refinement (cdr p1) p2)))))))
		  (:instance nth-cdr-partition-upper-bound
			     (p p1)
			     (index (index-for-large-element
				     (abslist (difflist (map-rcfn (cdr p1))
							(map-rcfn-refinement (cdr p1) p2)))
				     (maxlist (abslist (difflist (map-rcfn (cdr p1))
								 (map-rcfn-refinement (cdr p1) p2))))))))
	    :in-theory (disable nth last partitionp real-listp
				deltas dotprod index-for-large-element
				maxlist abs abs-dotprod-deltas-6
				index-for-large-element-works-better
				index-for-large-element-upper-bound-better
				nth-index-map-rcfn
				nth-index-map-rcfn-refinement
				next-gte
				abslist difflist
				map-rcfn
				map-rcfn-refinement
				rcfn-next-gte-close
				nth-cdr-partition-lower-bound
				nth-cdr-partition-upper-bound
				)))))

(local
 (defthmd small-abs-close-diff
   (implies (and (realp x1)
		 (realp x2)
		 (i-close x1 x2))
	    (i-small (abs (- x1 x2))))
   :hints (("Goal"
	    :in-theory (enable i-small i-close)))))


(local
 (defthmd rcfn-next-gte-abs-small-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (i-small (abs (- (rcfn (nth (index-for-large-element
					 (abslist (difflist (map-rcfn (cdr p1))
							    (map-rcfn-refinement (cdr p1) p2)))
					 (maxlist (abslist (difflist
							    (map-rcfn (cdr p1))
							    (map-rcfn-refinement (cdr p1) p2)))))
					(cdr p1)))
			     (rcfn (next-gte (nth (index-for-large-element
						   (abslist (difflist
							     (map-rcfn (cdr p1))
							     (map-rcfn-refinement (cdr p1) p2)))
						   (maxlist (abslist
							     (difflist
							      (map-rcfn (cdr p1))
							      (map-rcfn-refinement (cdr p1) p2)))))
						  (cdr p1))
					     p2))))))
      :hints (("Goal"
	       :do-not-induct t
	       :use ((:instance rcfn-next-gte-close-in-partition)
		     (:instance small-abs-close-diff
				(x1 (rcfn (nth (index-for-large-element
						(abslist (difflist (map-rcfn (cdr p1))
								   (map-rcfn-refinement (cdr p1) p2)))
						(maxlist (abslist (difflist
								   (map-rcfn (cdr p1))
								   (map-rcfn-refinement (cdr p1) p2)))))
					       (cdr p1))))
				(x2 (rcfn (next-gte (nth (index-for-large-element
							  (abslist (difflist
								    (map-rcfn (cdr p1))
								    (map-rcfn-refinement (cdr p1) p2)))
							  (maxlist (abslist
								    (difflist
								     (map-rcfn (cdr p1))
								     (map-rcfn-refinement (cdr p1) p2)))))
							 (cdr p1))
						    p2))))
		     )
	       :in-theory (disable strong-refinement-p
				   inside-interval-p
				   mesh
				   abs
				   nth
				   index-for-large-element
				   abslist
				   maxlist
				   difflist
				   map-rcfn
				   map-rcfn-refinement)
))))

(local
 (defthmd rcfn-next-gte-abs-times-span-small-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (i-small (* (abs (- (rcfn (nth (index-for-large-element
					    (abslist (difflist (map-rcfn (cdr p1))
							       (map-rcfn-refinement (cdr p1) p2)))
					    (maxlist (abslist (difflist
							       (map-rcfn (cdr p1))
							       (map-rcfn-refinement (cdr p1) p2)))))
					   (cdr p1)))
				(rcfn (next-gte (nth (index-for-large-element
						      (abslist (difflist
								(map-rcfn (cdr p1))
								(map-rcfn-refinement (cdr p1) p2)))
						      (maxlist (abslist
								(difflist
								 (map-rcfn (cdr p1))
								 (map-rcfn-refinement (cdr p1) p2)))))
						     (cdr p1))
						p2))))
			(span p1))))
      :hints (("Goal"
	       :do-not-induct t
	       :use ((:instance rcfn-next-gte-abs-small-in-partition)
		     (:instance limited*small->small
				(x (span p1))
				(y (abs (- (rcfn (nth (index-for-large-element
						       (abslist (difflist (map-rcfn (cdr p1))
									  (map-rcfn-refinement (cdr p1) p2)))
						       (maxlist (abslist (difflist
									  (map-rcfn (cdr p1))
									  (map-rcfn-refinement (cdr p1) p2)))))
						      (cdr p1)))
					   (rcfn (next-gte (nth (index-for-large-element
								 (abslist (difflist
									   (map-rcfn (cdr p1))
									   (map-rcfn-refinement (cdr p1) p2)))
								 (maxlist (abslist
									   (difflist
									    (map-rcfn (cdr p1))
									    (map-rcfn-refinement (cdr p1) p2)))))
								(cdr p1))
							   p2))))))
		     (:instance span-limited
				(p p1))
		     )
	       :in-theory (disable inside-interval-p
				   mesh
				   abs
				   nth
				   index-for-large-element
				   abslist
				   maxlist
				   difflist
				   map-rcfn
				   map-rcfn-refinement
				   limited*small->small
				   span-limited)
))))

(local
 (defthmd small-if-abs-<=-small
   (implies (and (realp x)
		 (realp y)
		 (<= (abs x) y)
		 (i-small y))
	    (i-small x))
   :hints (("Goal"
	    :use ((:instance small-if-<-small (x y) (y x)))
	    :in-theory (disable small-if-<-small)))
   ))

(local
 (defthm acl2-numberp-abs-+
   (acl2-numberp (abs (+ x y)))))


(local
 (defthmd realp-abs-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (realp (* (abs (- (rcfn (nth (index-for-large-element
					  (abslist (difflist (map-rcfn (cdr p1))
							     (map-rcfn-refinement (cdr p1) p2)))
					  (maxlist (abslist (difflist
							     (map-rcfn (cdr p1))
							     (map-rcfn-refinement (cdr p1) p2)))))
					 (cdr p1)))
			      (rcfn (next-gte (nth (index-for-large-element
						    (abslist (difflist
							      (map-rcfn (cdr p1))
							      (map-rcfn-refinement (cdr p1) p2)))
						    (maxlist (abslist
							      (difflist
							       (map-rcfn (cdr p1))
							       (map-rcfn-refinement (cdr p1) p2)))))
						   (cdr p1))
					      p2))))
		      (span p1))))))

(local
 (defthmd dotprods-close-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (i-close (dotprod (deltas p1)
			      (map-rcfn (cdr p1)))
		     (dotprod (deltas p1)
			      (map-rcfn-refinement (cdr p1) p2))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance small-if-abs-<=-small
			     (x (- (dotprod (deltas p1)
					    (map-rcfn (cdr p1)))
				   (dotprod (deltas p1)
					    (map-rcfn-refinement (cdr p1) p2))))
			     (y (* (abs (- (rcfn (nth (index-for-large-element
						       (abslist (difflist (map-rcfn (cdr p1))
									  (map-rcfn-refinement (cdr p1) p2)))
						       (maxlist (abslist (difflist
									  (map-rcfn (cdr p1))
									  (map-rcfn-refinement (cdr p1) p2)))))
						      (cdr p1)))
					   (rcfn (next-gte (nth (index-for-large-element
								 (abslist (difflist
									   (map-rcfn (cdr p1))
									   (map-rcfn-refinement (cdr p1) p2)))
								 (maxlist (abslist
									   (difflist
									    (map-rcfn (cdr p1))
									    (map-rcfn-refinement (cdr p1) p2)))))
								(cdr p1))
							   p2))))
				   (span p1))))
		  (:instance rcfn-next-gte-abs-times-span-small-in-partition)
		  (:instance abs-dotprod-deltas-7)
		  (:instance realp-abs-in-partition))
	    :in-theory (e/d (i-close)
			    (;strong-refinement-p
			     ;partitionp
				inside-interval-p
				mesh
				abs
				nth
				dotprod
				index-for-large-element
				abslist
				maxlist
				difflist
				map-rcfn
				map-rcfn-refinement
				next-gte
				span-limited))))))

(local
 (defun co-member (a x)
   ;; returns all members of x up to and including a
   (if (consp x)
       (if (equal a (car x))
	   (list a)
	 (cons (car x) (co-member a (cdr x))))
     nil)))

(local
 (defun my-make-list (n elt)
   (if (zp n)
       nil
     (cons elt (my-make-list (1- n) elt)))))

(local
 (defthm my-make-list-1
   (equal (my-make-list 1 x)
	  (list x))
   :hints (("Goal" :expand (my-make-list 1 x)))))

(local
 (defthm next-gte-expand
   (implies (equal (car p2) a)
	    (equal (next-gte a p2)
		   a))))

(local
 (defthmd next-gte-for-last-lemma
   (implies (partitionp p)
	    (<= (car p)
		(car (last p))))))

(local
 (defthmd next-gte-for-last
   (implies (and (partitionp p)
		 (equal (car (last p)) a))
	    (equal (next-gte a p)
		   a))
   :hints (("Goal"
	    :use ((:instance next-gte-for-last-lemma
			     (p (cdr p))))))
   ))

(local
 (defthmd next-gte-for-first
   (implies (and (partitionp p)
		 (<= a (car p)))
	    (equal (next-gte a p)
		   (car p)))
   ))

(local
 (defthm map-rcfn-refinement-for-constant
   (implies
    (and (partitionp p3)
	 (partitionp p2)
	 (consp (cdr p2))
	 (< (car p2) (car p3))
	 (equal (cadr p2) (car (last p3))))
    (equal
     (map-rcfn-refinement p3 p2)
     (my-make-list (len p3)
		   (rcfn (cadr p2)))))
   :hints (("Subgoal *1/1.5"
	    :use ((:instance next-gte-for-first
			     (p (cdr p2))
			     (a (car p3)))
		  (:instance partition-first-inside-domain-hint
			     (p p3))
		  )
	    :in-theory (disable partition-first-inside-domain-hint)
	    ))
   ))

(local
 (defthm partitionp-cdr-co-member
   (implies (partitionp p)
	    (equal (partitionp (cdr (co-member a p)))
		   (and (consp (cdr p))
			(not (equal a (car p)))))))
 )

(local
 (defthm map-rcfn-refinement-cdr-co-member-subgoal-hack-1
   (implies (and (partitionp p1)
		 (consp p2)
		 (< (car p1) (cadr p2))
		 (partitionp (cdr p2))
		 (consp (cdr p2))
		 (equal (car p1) (car p2))
		 (equal (car (last p1))
			(car (last (cdr p2))))
		 (refinement-p p1 p2))
	    (< (car p1)
	       (cadr (co-member (cadr p2) p1))))))

(local
 (defthm car-last-cdr-co-member
   (implies (and (partitionp p1)
		 (not (equal (car p1) a))
		 (member a p1))
	    (equal (car (last (cdr (co-member a p1))))
		   a))))

(local
 (defthm map-rcfn-refinement-cdr-co-member-subgoal-hack-2
   (implies (and (partitionp p1)
		 (consp p2)
		 (< (car p1) (cadr p2))
		 (partitionp (cdr p2))
		 (consp (cdr p2))
		 (equal (car p1) (car p2))
		 (equal (car (last p1))
			(car (last (cdr p2))))
		 (refinement-p p1 p2))
	    (equal (car (last (cdr (co-member (cadr p2) p1))))
		   (cadr p2)))
   :hints (("Goal"
	    :use ((:instance car-last-cdr-co-member
			     (a (cadr p2))
			     (p1 p1)))
	    :in-theory (disable car-last-cdr-co-member)))
   ))

(local
 (defthm partitionp-cdr-co-member-forced
   (implies (and (partitionp p)
		 (not (equal a (car p)))
		 (force (consp (cdr p))))
	    (equal (partitionp (cdr (co-member a p)))
		   t))))

(local
 (defthm map-rcfn-refinement-cdr-co-member
   (implies
    (and (partitionp p1)
	 (partitionp p2)
	 (consp (cdr p2))
	 (strong-refinement-p p1 p2))
    (equal
     (map-rcfn-refinement (cdr (co-member (cadr p2) p1))
			  p2)
     (my-make-list (len (cdr (co-member (cadr p2) p1)))
		   (rcfn (cadr p2)))))))


(local
 (defthm append-member-co-member
   (implies (true-listp x)
	    (equal (append (co-member a x)
			   (cdr (member a x)))
		   x))))

(local
 (defthm cdr-map-rcfn-refinement
   (implies (consp p1)
	    (equal (cdr (map-rcfn-refinement p1 p2))
		   (map-rcfn-refinement (cdr p1) p2)))))

(local
 (defthm len-cdr-map-rcfn-refinement
   (equal (len (cdr (map-rcfn-refinement p1 p2)))
	  (len (cdr p1)))))

(local
 (defthm member-implies-consp-co-member
   (implies (member a x)
	    (consp (co-member a x)))
   :rule-classes :forward-chaining))

(local
 (defthm car-last-co-member
   (implies (member a x)
	    (equal (car (last (co-member a x)))
		   a))))

(local
 (defthm car-member
   (implies (member a x)
	    (equal (car (member a x))
		   a))))


(local
 (defthm partitionp-member
   (implies (and (partitionp p)
		 (member a p))
	    (partitionp (member a p)))
   :rule-classes :forward-chaining))

(local
 (defthm member-cdr-member-implies-member
   (implies (member a (cdr (member b x)))
	    (member a x))
   :rule-classes :forward-chaining))

(local
 (defthm refinement-implies-member-cadr
   (implies (and (refinement-p p1 p2)
		 (consp (cdr p2)))
	    (member (cadr p2) p1))
   :hints (("Goal"
	    :expand
	    ((refinement-p p1 p2)
	     (refinement-p (cdr (member-equal (car p2) p1)) (cdr p2)))
	    ))))

(local
 (defthm consp-co-member
   (equal (consp (co-member a x))
	  (consp x))))

(local
 (defthm sumlist-map-times-deltas-with-constant
   (implies (true-listp lst)
	    (equal (sumlist (map-times (deltas lst)
				       (cdr (my-make-list (len lst) elt))))
		   (* (- (car (last lst)) (car lst))
		      elt)))
   :hints (("Goal"
	    :expand ((my-make-list 1 elt))))))

(local
 (defthm len-non-zero
   (implies (consp x)
	    (< 0 (len x)))
   :rule-classes :forward-chaining))

(local
 (defthm car-my-make-list
   (implies (not (zp n))
	    (equal (car (my-make-list n elt))
		   elt))
   :hints (("Goal" :expand (my-make-list n elt)))))

(local
 (defthm car-co-member
   (equal (car (co-member a x))
	  (car x))))

(local
 (defthm co-member-open
   (implies (and (not (equal a (car x)))
		 (consp x))
	    (equal (co-member a x)
		   (cons (car x)
			 (co-member a (cdr x)))))))

(local
 (defthm refinement-p-forward-to-member-rewrite
   (implies (and (refinement-p p1 p2)
		 (consp p2))
	    (member (car p2) p1))))

(local
 (defthm equal-riemann-rcfn-refinement-reduction-helper-1-back-2
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (consp (cdr p2))
		 (strong-refinement-p p1 p2))
	    (equal (riemann-rcfn-refinement (co-member (cadr p2) p1)
					    p2)
		   (* (- (cadr p2) (car p2))
		      (rcfn (cadr p2)))))))



(local
 (defthm consp-map-rcfn-refinement
   (equal (consp (map-rcfn-refinement p1 p2))
	  (consp p1))))

(local
 (defthm dotprod-append
   (implies (equal (len x1) (len y1))
	    (equal (dotprod (append x1 x2)
			    (append y1 y2))
		   (+ (dotprod x1 y1)
		      (dotprod x2 y2))))))

(local
 (defthm map-rcfn-refinement-append
   (equal (map-rcfn-refinement (append p1 p2) p3)
	  (append (map-rcfn-refinement p1 p3)
		  (map-rcfn-refinement p2 p3)))))

(local
 (defthm map-times-append
   (implies (equal (len x1) (len y1))
	    (equal (map-times (append x1 x2)
			      (append y1 y2))
		   (append (map-times x1 y1)
			   (map-times x2 y2))))))

(local
 (defthm sumlist-append
   (equal (sumlist (append x y))
	  (+ (sumlist x) (sumlist y)))))

(local
 (defthm append-nil
   (implies (true-listp x)
	    (equal (append x nil)
		   x))))

(local
 (defthm cdr-append
   (implies (consp x)
	    (equal (cdr (append x y))
		   (append (cdr x) y)))))

(local
 (defthm sumlist-cons
   (equal (sumlist (cons a x))
	  (+ a (sumlist x)))))

(local
 (defthm riemann-rcfn-cons
  (implies (consp p)
           (equal (riemann-rcfn (cons a p))
                  (+ (* (- (car p) a)
                        (rcfn (car p)))
                     (riemann-rcfn p))))))

(local
 (defthm map-rcfn-refinement-cdr-2
   (implies (and (<= a (car p1))
		 (< (car p2) a)
		 (partitionp p1)
		 (partitionp p2))
	    (equal (map-rcfn-refinement p1 (cdr p2))
		   (map-rcfn-refinement p1 p2)))))

(local
 (defthm riemann-rcfn-refinement-cdr-2
   (implies (and (<= a (car p1))
		 (< (car p2) a)
		 (partitionp p1)
		 (partitionp p2))
	    (equal (riemann-rcfn-refinement p1 (cdr p2))
		   (riemann-rcfn-refinement p1 p2)))
   :hints (("Goal"
	    :cases ((consp (cdr p1))))
	   ("Subgoal 1"
	    :use ((:instance map-rcfn-refinement-cdr-2
			     (a (car p1))
			     (p1 (cdr p1))))
	    :in-theory (disable map-rcfn-refinement-cdr-2))
	   )
   ))

(local
 (defthm deltas-append
   (implies (and (consp p1)
		 (consp p2)
		 (equal (car (last p1)) (car p2)))
	    (equal (deltas (append p1 (cdr p2)))
		   (append (deltas p1)
			   (deltas p2))))))

(local
 (defthm len-deltas-better
   (equal (len (deltas p))
	  (len (cdr p)))))

(local
 (defthm riemann-rcfn-refinement-append
   (implies (and (consp p1)
		 (consp p2)
		 (equal (car (last p1)) (car p2)))
	    (equal (riemann-rcfn-refinement (append p1 (cdr p2)) p3)
		   (+ (riemann-rcfn-refinement p1 p3)
		      (riemann-rcfn-refinement p2 p3))))))

(local
 (defthm equal-riemann-rcfn-refinement-reduction-helper-1-back-1
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (consp (cdr p2))
		 (strong-refinement-p p1 p2))
	    (equal (riemann-rcfn-refinement (member (cadr p2) p1)
					    p2)
		   (- (riemann-rcfn-refinement p1 p2)
		      (* (- (cadr p2) (car p2))
			 (rcfn (cadr p2))))))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory
	    (disable riemann-rcfn-refinement partitionp
					;riemann-rcfn-refinement-append
					;partitionp-implies-first-less-than-second
		     )
	    :use
	    ((:instance riemann-rcfn-refinement-append
			(p1 (co-member (cadr p2) p1))
			(p2 (member (cadr p2) p1))
			(p3 p2)))))))

(local
 (defthm riemann-rcfn-alternative
   (equal (riemann-rcfn p)
	  (if (and (consp p) (consp (cdr p)))
	      (+ (riemann-rcfn (cdr p))
		 (* (- (cadr p) (car p))
		    (rcfn (cadr p))))
	    0))
   :rule-classes :definition))

(local
 (defthm equal-riemann-rcfn-refinement-reduction-helper-1
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (consp (cdr p2))
		 (equal (riemann-rcfn-refinement (member (cadr p2) p1)
						 p2)
			(riemann-rcfn (cdr p2)))
		 (strong-refinement-p p1 p2))
	    (equal (riemann-rcfn-refinement p1 p2)
		   (riemann-rcfn p2)))
   :hints (("Goal" :use equal-riemann-rcfn-refinement-reduction-helper-1-back-1))))

(local
 (defthm partitionp-member-rewrite
  (implies (and (partitionp p)
                (member a p))
           (partitionp (member a p)))))
(local
 (defthm equal-riemann-rcfn-refinement-reduction
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (consp (cdr p2))
		 (equal (riemann-rcfn-refinement (member (cadr p2) p1)
						 (cdr p2))
			(riemann-rcfn (cdr p2)))
		 (strong-refinement-p p1 p2))
	    (equal (riemann-rcfn-refinement p1 p2)
		   (riemann-rcfn p2)))
   :hints (("Goal" :in-theory
	    (disable
	     riemann-rcfn-refinement riemann-rcfn member
	     riemann-rcfn-refinement-cdr-2)
	    :use
	    ((:instance
	      riemann-rcfn-refinement-cdr-2
	      (p1 (member (cadr p2) p1))
	      (p2 p2)
	      (a (cadr p2))))))))

(local
 (defthmd riemann-refinement-close-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (i-close (riemann-rcfn p1)
		     (riemann-rcfn-refinement p1 p2)))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance dotprods-close-in-partition))
	    :in-theory '(riemann-rcfn riemann-rcfn-refinement)))))

(local
 (defun riemann-rcfn-refinement-is-riemann-rcfn-induction (p1 p2)
   (if (consp p2)
       (if (consp (cdr p2))
	   (riemann-rcfn-refinement-is-riemann-rcfn-induction
	    (member (cadr p2) p1)
	    (cdr p2))
	 p1)
     t)))

(local
 (defthm strong-refinement-p-forward
   (implies (strong-refinement-p p1 p2)
	    (and (partitionp p1)
		 (partitionp p2)
		 (equal (car p1) (car p2))
		 (equal (car (last p1))
			(car (last p2)))
		 (refinement-p p1 p2)))
   :rule-classes :forward-chaining))

(local
 (defthm partitionp-forward-to-realp-member
   (implies (and (partitionp p)
		 (member a p))
	    (realp (car (member a p))))
   :rule-classes :forward-chaining))

(local
 (defthm refinement-p-implies-realp-car-member
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (refinement-p p1 p2))
	    (realp (car (member (car p2) p1))))
   :rule-classes :forward-chaining))

(local
 (defthm car-last-member
   (implies (member a x)
	    (equal (car (last (member a x)))
		   (car (last x))))))

(local
 (defthm refinement-p-implies-realp-cadr-member
   (implies (and (partitionp p1)
		 (cdr (member a p1)))
	    (realp (cadr (member a p1))))
   :rule-classes :forward-chaining))

(local
 (defthm partition-same-endpoints
   (implies (and (partitionp p)
		 (consp p)
		 (equal (car (last p)) (car p)))
	    (not (consp (cdr p))))
   :hints (("Goal"
	    :use ((:instance partition-first-inside-domain-hint
			     (p (cdr p))))
	    :in-theory (disable partition-first-inside-domain-hint)))
   ))

(local
 (defthm member-car-last
   (implies (partitionp p)
	    (equal (member (car (last p)) p)
		   (last p)))
   ;:hints (("Goal" :induct t))
   :instructions (:induct :bash :bash :bash)
   ))

(local
 (defthm cdr-last
   (implies (true-listp p)
	    (equal (cdr (last p))
		   nil))))

(local
 (defthm partitionp-implies-less-than-cadr
   (implies (and (partitionp p)
		 (cdr (member a p)))
	    (< a (cadr (member a p))))))

(local
 (defthm strong-refinement-p-preserved
   (implies (and (consp p2)
		 (consp (cdr p2))
		 (strong-refinement-p p1 p2))
	    (strong-refinement-p (member (cadr p2) p1)
				 (cdr p2)))
   :hints (("Goal" :expand (refinement-p p1 p2)))))

(local
 (defthm riemann-rcfn-refinement-of-trivial-interval
   (implies (and (consp p2)
		 (not (consp (cdr p2)))
		 (strong-refinement-p p1 p2))
	    (equal (riemann-rcfn-refinement p1 p2)
		   0))
   ))

(local
 (defthm riemann-rcfn-refinement-is-riemann-rcfn
   (implies (strong-refinement-p p1 p2)
	    (equal (riemann-rcfn-refinement p1 p2)
		   (riemann-rcfn p2)))
   :hints (("Goal"
	    :in-theory (disable strong-refinement-p
				riemann-rcfn-refinement
				riemann-rcfn)
	    :induct
	    (riemann-rcfn-refinement-is-riemann-rcfn-induction p1 p2)))))

(local
 (defthmd riemann-sums-close-in-partition
   (implies (and (strong-refinement-p p1 p2)
		 (standardp (car p1))
		 (standardp (car (last p1)))
		 (< (car p1) (car (last p1)))
		 (inside-interval-p (car p1) (rcfn-domain))
		 (inside-interval-p (car (last p1)) (rcfn-domain))
		 (i-small (mesh p2)))
	    (i-close (riemann-rcfn p1)
		     (riemann-rcfn p2)))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance riemann-refinement-close-in-partition)
		  (:instance riemann-rcfn-refinement-is-riemann-rcfn))
	    :in-theory nil))))

(local
 (defthm common-refinement-is-refinement
   (implies (and (partitionp p1)
		 (partitionp p2))
	    (refinement-p (common-refinement p1 p2) p2))))

(local
 (defthm common-refinement-is-partitionp2-lemma1
   (implies (partitionp2 p1 p2)
	    (equal (car (common-refinement p1 p2))
		   (car p2)))))

(local
 (defthm common-refinement-is-partitionp2-lemma2
   (implies (equal (last p1) (last p2))
	    (equal (last (common-refinement p1 p2))
		   (last p2)))))

(local
 (defthm common-refinement-is-partitionp2
   (implies (partitionp2 p1 p2)
	    (partitionp2 (common-refinement p1 p2) p2))))

(local
 (defthm common-refinement-is-strong-refinement
   (implies (partitionp2 p1 p2)
	    (strong-refinement-p (common-refinement p1 p2) p2))))

(local
 (defthm common-refinement-is-partitionp2-2
   (implies (partitionp2 p1 p2)
	    (partitionp2 (common-refinement p1 p2) p1))))

(local
 (defthm common-refinement-commutative
   (implies (and (partitionp p1)
		 (partitionp p2))
	    (equal (common-refinement p1 p2)
		   (common-refinement p2 p1)))))

(local
 (defthm common-refinement-is-strong-refinement-2
   (implies (partitionp2 p1 p2)
	    (strong-refinement-p (common-refinement p1 p2) p1))
   :hints (("Goal"
	    :use ((:instance common-refinement-is-strong-refinement
			     (p1 p2)
			     (p2 p1)))
	    :in-theory (disable common-refinement-is-strong-refinement
				strong-refinement-p
				common-refinement)))))

(local
 (defthm riemann-sum-close-to-common-in-partition-lemma
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (refinement-p (common-refinement (make-small-partition (car p)
								   (car (last p)))
					     p)
			  (make-small-partition (car p)
						(car (last p)))))
   ))

(local
 (defthmd riemann-sum-close-to-common-in-partition
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rcfn p)
		     (riemann-rcfn (common-refinement (make-small-partition a b) p))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance riemann-sums-close-in-partition
			     (p1 (common-refinement (make-small-partition a b) p))
			     (p2 p))
		  )
	    :in-theory (disable riemann-sums-close-in-partition
				make-small-partition
				common-refinement
				riemann-rcfn
				mesh)))))

(local
 (defthmd common-refinement-p-p
   (implies (partitionp p)
	    (equal (common-refinement p p) p))))


(local
 (defthmd riemann-sum-small-partition-close-to-common-in-partition
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rcfn (make-small-partition a b))
		     (riemann-rcfn (common-refinement (make-small-partition a b) p))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance riemann-sums-close-in-partition
			     (p1 (common-refinement (make-small-partition a b) p))
			     (p2 (make-small-partition a b)))
		  )
	    :in-theory (disable riemann-sums-close-in-partition
				make-small-partition
				common-refinement
				riemann-rcfn
				mesh)))))


(local
 (defthmd riemann-sum-close-to-small-in-partition
   (implies (and (standardp a)
		 (standardp b)
		 (< a b)
		 (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) b)
		 (i-small (mesh p)))
	    (i-close (riemann-rcfn (make-small-partition a b))
		     (riemann-rcfn p)))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance riemann-sum-small-partition-close-to-common-in-partition)
		  (:instance riemann-sum-close-to-common-in-partition)
		  )
	    :in-theory (disable ;riemann-sum-close-to-common-in-partition
				;riemann-sum-small-partition-close-to-common-in-partition
				make-small-partition
				common-refinement
				riemann-rcfn
				mesh)))))
(local
 (defthm riemann-rcfn-trivial-partition
   (implies (and (partitionp p)
		 (equal (car p) (car (last p))))
	    (equal (riemann-rcfn p) 0))))

(defthm strict-int-rcfn-is-integral-of-rcfn
  (implies (and (standardp a)
		(standardp b)
		(<= a b)
		(inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(partitionp p)
		(equal (car p) a)
		(equal (car (last p)) b)
		(i-small (mesh p)))
	   (i-close (riemann-rcfn p)
		    (strict-int-rcfn a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance riemann-sum-close-to-small-in-partition))
	   :in-theory (disable ;riemann-sum-close-to-common-in-partition
					;riemann-sum-small-partition-close-to-common-in-partition
		       make-small-partition
		       common-refinement
		       riemann-rcfn
		       riemann-rcfn-alternative
		       mesh))
	  ("Subgoal 2"
	   :do-not-induct t
	   :use ((:instance standard-part-close
			    (x (riemann-rcfn (make-small-partition (car p)
								   (car (last p)))))))
	   :in-theory (disable standard-part-close
			       make-small-partition
			       common-refinement
			       riemann-rcfn
			       riemann-rcfn-alternative
			       mesh))
	  )
  )

(defthm-std strict-int-a-a
  (implies (inside-interval-p a (rcfn-domain))
	   (equal (strict-int-rcfn a a) 0))
  :hints (("Goal"
	   :use ((:instance strict-int-rcfn-is-integral-of-rcfn
			    (a a)
			    (b a)
			    (p (make-small-partition a a)))
		 (:instance riemann-rcfn-trivial-partition
			    (p (make-small-partition a a))))
	   :in-theory (disable strict-int-rcfn-is-integral-of-rcfn
			       riemann-rcfn-trivial-partition))))



(defun int-rcfn (a b)
  (if (<= a b)
      (strict-int-rcfn a b)
    (- (strict-int-rcfn b a))))

(defthm-std realp-strict-int-rcfn
  (implies (and (realp a)
		(realp b))
	   (realp (strict-int-rcfn a b)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance realp-riemann-rcfn
			    (p (make-small-partition a b))))
	   :in-theory (disable riemann-rcfn
			       realp-riemann-rcfn)))
  )

(defthm int-rcfn-bounded
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (<= a b))
	    (and (<= (* (rcfn (rcfn-min-x a b))
			(- b a))
		     (int-rcfn a b))
		 (<= (int-rcfn a b)
		     (* (rcfn (rcfn-max-x a b))
			(- b a)))))
   :hints (("Goal"
	    :use ((:instance strict-int-rcfn-bounded))
	    :in-theory (disable strict-int-rcfn)
	    )))

(defthm min-x-commutative
  (implies (and (realp a)
		(realp b))
	   (equal (rcfn-min-x b a)
		  (rcfn-min-x a b)))
  :hints (("Goal"
	   :in-theory (enable rcfn-min-x)))
  )

(defthm max-x-commutative
  (implies (and (realp a)
		(realp b))
	   (equal (rcfn-max-x b a)
		  (rcfn-max-x a b)))
  :hints (("Goal"
	   :in-theory (enable rcfn-max-x)))
  )

(defthm int-rcfn-bounded-2
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (< b a))
	    (and (<= (* (rcfn (rcfn-max-x a b))
			(- b a))
		     (int-rcfn a b))
		 (<= (int-rcfn a b)
		     (* (rcfn (rcfn-min-x a b))
			(- b a)))))
   :hints (("Goal"
	    :use ((:instance int-rcfn-bounded (a b) (b a)))
	    :in-theory (disable strict-int-rcfn))
	   ))

(deflabel continuous-functions-are-integrable)

(local (include-book "split-integral-by-subintervals"))

(defthm split-rcfn-integral-by-subintervals
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(inside-interval-p c (rcfn-domain)))
	   (equal (+ (int-rcfn a c)
		     (int-rcfn c b))
		  (int-rcfn a b)))
  :hints (("Goal"
	   :use ((:functional-instance split-integral-by-subintervals
				       (rifn rcfn)
				       (strict-int-rifn strict-int-rcfn)
				       (domain-rifn rcfn-domain)
				       (map-rifn map-rcfn)
				       (riemann-rifn riemann-rcfn)
				       (int-rifn int-rcfn))))
	  ("Subgoal 4"
	   :use ((:instance strict-int-rcfn-is-integral-of-rcfn))
	   :in-theory '(mesh))
	  ("Subgoal 3"
	   :use ((:instance rcfn-domain-non-trivial))
	   )
	  )
  )

(defthm realp-int-rcfn
  (implies (and (realp a)
		(realp b))
	   (realp (int-rcfn a b)))
  )

(in-theory (disable int-rcfn))
