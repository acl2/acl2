(in-package "ACL2")

(include-book "integrable-functions")
(include-book "make-partition")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))

#|
(local
 (defthmd partition-is-monotonic
   (implies (and (partitionp p)
		 (< a (car p)))
	    (< a (car (last p))))))

(local
 (defthmd partition-of-single-point-lemma
   (implies (and (partitionp p)
		 (consp (cdr p)))
	    (not (equal (car p)
			(car (last p)))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance partition-is-monotonic
			     (p (cdr p))
			     (a (car p))))))
   ))

(local
 (defthm partition-of-single-point
   (implies (and (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) a))
	    (equal p (list a)))
   :hints (("Goal"
	    :use ((:instance partition-of-single-point-lemma))))
   :rule-classes nil))

(local
 (defthm deltas-partition-of-single-point
   (implies (and (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) a))
	    (equal (deltas p) nil))
   :hints (("Goal"
	    :use ((:instance partition-of-single-point))))
   :rule-classes nil))

(local
 (defthm riemann-rifn-of-single-point
   (implies (and (partitionp p)
		 (equal (car p) a)
		 (equal (car (last p)) a))
	    (equal (riemann-rifn p) 0))
   :hints (("Goal"
	    :use ((:instance deltas-partition-of-single-point))))
   :rule-classes nil))
|#


(local
 (defthmd close-to-standard-is-close-1
   (implies (and (i-close x y)
		 (standardp x)
		 (standardp y))
	    (equal (equal x y) t))
   :hints (("Goal"
	    :in-theory (enable i-close i-small)))))

(defthm-std integral-of-single-point
  (implies (and (realp a)
		(inside-interval-p a (domain-rifn)))
	   (equal (strict-int-rifn context a a) 0))
  :hints (("Goal'"
	   :use ((:instance strict-int-rifn-is-integral-of-rifn
			    (a a)
			    (b a)
			    (p (list a)))
		 (:instance close-to-standard-is-close-1
			    (x 0)
			    (y (strict-int-rifn context a a)))
		 )
	   :in-theory (disable strict-int-rifn-is-integral-of-rifn)))
  )


(local
 (defthm-std split-integral-by-subintervals-1
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (inside-interval-p a (domain-rifn))
		 (inside-interval-p b (domain-rifn))
		 (or (equal c a)
		     (equal c b)))
	    (equal (+ (strict-int-rifn context a c)
		      (strict-int-rifn context c b))
		   (strict-int-rifn context a b)))))

(local
 (defthm riemann-sum-append
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (equal (car (last p1)) (car p2)))
	    (equal (riemann-rifn context (append p1 (cdr p2)))
		   (+ (riemann-rifn context p1)
		      (riemann-rifn context p2))))
   ))

(local
 (defthmd i-close-plus
  (implies (and (i-close x1 x2)
		(i-close y1 y2))
	   (i-close (+ x1 y1)
		    (+ x2 y2)))
  :hints (("Goal"
	   :in-theory (enable i-close i-small)))))


(local
 (defthm car-append
   (equal (car (append x y))
	  (if (endp x)
	      (car y)
	    (car x)))))

(local
 (defthm last-append
   (implies (consp y)
	    (equal (last (append x y))
		   (last y)))))

(local
 (defthm-std split-integral-by-subintervals-2
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (inside-interval-p a (domain-rifn))
		 (inside-interval-p b (domain-rifn))
		 (< a c)
		 (< c b))
	    (equal (+ (strict-int-rifn context a c)
		      (strict-int-rifn context c b))
		   (strict-int-rifn context a b)))
   :hints (("Goal"
	    :use ((:instance strict-int-rifn-is-integral-of-rifn
			     (a a)
			     (b b)
			     (p (append (make-small-partition a c)
					(cdr (make-small-partition c b)))))
		  (:instance strict-int-rifn-is-integral-of-rifn
			     (a a)
			     (b c)
			     (p (make-small-partition a c)))
		  (:instance strict-int-rifn-is-integral-of-rifn
			     (a c)
			     (b b)
			     (p (make-small-partition c b)))
		  (:instance i-close-plus
			     (x1 (riemann-rifn context (make-small-partition a c)))
			     (x2 (strict-int-rifn context a c))
			     (y1 (riemann-rifn context (make-small-partition c b)))
			     (y2 (strict-int-rifn context c b)))
		  (:instance close-to-standard-is-close-1
			     (x (+ (strict-int-rifn context a c) (strict-int-rifn context c b)))
			     (y (strict-int-rifn context a b)))
		  (:instance i-close-transitive
			     (x (+ (strict-int-rifn context a c) (strict-int-rifn context c b)))
			     (y (+ (riemann-rifn context (make-small-partition a c))
				   (riemann-rifn context (make-small-partition c b))))
			     (z (strict-int-rifn context a b)))
		  (:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c c)
			     (interval (domain-rifn)))
		  )
	    :in-theory (disable strict-int-rifn-is-integral-of-rifn
				riemann-rifn
				mesh
				i-close-transitive
				inside-interval-p-squeeze)))))

(local
 (defthmd split-integral-by-subintervals-lemma
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (< a b)
		 (inside-interval-p a (domain-rifn))
		 (inside-interval-p b (domain-rifn))
		 (inside-interval-p c (domain-rifn)))
	    (equal (+ (int-rifn context a c)
		      (int-rifn context c b))
		   (int-rifn context a b)))
   :hints (("Goal"
	    :cases ((or (= a c) (= b c))
		    (and (< a c) (< c b))
		    (< c a)
		    (< b c))))))

(defthmd integral-reverse-interval
  (implies (and (realp a)
		(realp b)
		(inside-interval-p a (domain-rifn))
		(inside-interval-p b (domain-rifn)))
	   (equal (- (int-rifn context a b))
		  (int-rifn context b a))))

(defthmd split-integral-by-subintervals
  (implies (and (realp a)
		(realp b)
		(realp c)
		(inside-interval-p a (domain-rifn))
		(inside-interval-p b (domain-rifn))
		(inside-interval-p c (domain-rifn)))
	   (equal (+ (int-rifn context a c)
		     (int-rifn context c b))
		  (int-rifn context a b)))
  :hints (("Goal"
	   :cases ((< a b) (< b a)))
	  ("Subgoal 3"
	   :use ((:instance integral-reverse-interval
			    (a a)
			    (b c))))
	  ("Subgoal 2"
	   :use ((:instance split-integral-by-subintervals-lemma)))
	  ("Subgoal 1"
	   :use ((:instance split-integral-by-subintervals-lemma
			    (a b)
			    (b a))
		 (:instance integral-reverse-interval
			    (a b)
			    (b c))
		 (:instance integral-reverse-interval
			    (a c)
			    (b a))
		 (:instance integral-reverse-interval
			    (a b)
			    (b a)))
	   :in-theory (disable int-rifn))
	  ))
