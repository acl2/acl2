(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))

(include-book "continuous-function")

(local
 (defthmd multiply-inequalities-by-positive
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (< 0 c)
		 (<= a b))
	    (<= (* a c) (* b c)))))

(local
 (defthmd differential-int-rcfn-bounded-1
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (< a b))
	    (and (<= (rcfn (rcfn-min-x a b))
		     (/ (int-rcfn a b)
			(- b a)))
		 (<= (/ (int-rcfn a b)
			(- b a))
		     (rcfn (rcfn-max-x a b)))))
   :hints (("Goal"
	    :use ((:instance int-rcfn-bounded))
	    :in-theory (disable int-rcfn-bounded
				int-rcfn
				|(* (+ x y) z)|
				))
	   ("Subgoal 2"
	    :use ((:instance multiply-inequalities-by-positive
			     (a (* (rcfn (rcfn-min-x a b))
				   (- b a)))
			     (b (int-rcfn a b))
			     (c (/ (- b a)))))
	    :in-theory (disable |(* (+ x y) z)|))
	   ("Subgoal 1"
	    :use ((:instance multiply-inequalities-by-positive
			     (a (int-rcfn a b))
			     (b (* (rcfn (rcfn-max-x a b))
				   (- b a)))
			     (c (/ (- b a)))))
	    :in-theory (disable |(* (+ x y) z)|))
	   )))

(defthm int-rcfn-b-a
  (implies (< b a)
	   (equal (int-rcfn a b)
		  (- (int-rcfn b a))))
  :hints (("Goal"
	   :in-theory (enable int-rcfn)))
  )

(local
 (defthm push-sign-to-denominator
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (not (equal a b)))
	    (equal (- (* c (/ (+ (- a) b))))
		   (* c (/ (+ a (- b))))))
   :hints (("Goal"
	    :use ((:instance |(/ (- x))|
			     (x (+ (- a) b))))
	    :in-theory (disable |(/ (- x))|)))
   ))

(local
 (defthmd differential-int-rcfn-bounded-2
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (< b a))
	    (and (<= (rcfn (rcfn-min-x a b))
		     (/ (int-rcfn a b)
			(- b a)))
		 (<= (/ (int-rcfn a b)
			(- b a))
		     (rcfn (rcfn-max-x a b)))))
   :hints (("Goal"
	    :use ((:instance differential-int-rcfn-bounded-1 (a b) (b a))
		  )
	    :in-theory (disable differential-int-rcfn-bounded-1
				int-rcfn
				))
	   )))

(local
 (defthmd differential-int-rcfn-bounded
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain))
		 (not (equal a b)))
	    (and (<= (rcfn (rcfn-min-x a b))
		     (/ (int-rcfn a b)
			(- b a)))
		 (<= (/ (int-rcfn a b)
			(- b a))
		     (rcfn (rcfn-max-x a b)))))
   :hints (("Goal"
	    :use ((:instance differential-int-rcfn-bounded-1)
		  (:instance differential-int-rcfn-bounded-2)
		  )))))

(local
 (defthmd small-squeeze
   (implies (and (realp x)
		 (realp y)
		 (realp z)
		 (<= x y)
		 (<= y z)
		 (i-small x)
		 (i-small z))
	    (i-small y))
   :hints (("Goal"
	    :use ((:instance standard-part-squeeze))
	    :in-theory (enable i-small)))))

(local
 (defthmd close-squeeze
   (implies (and (realp x)
		 (realp y)
		 (realp z)
		 (<= x y)
		 (<= y z)
		 (i-close x z))
	    (and (i-close x y)
		 (i-close y z)))
   :hints (("Goal"
	    :use ((:instance small-squeeze
			     (x 0)
			     (y (- y x))
			     (z (- z x))))
	    :in-theory (enable i-close)))))

(local
 (defthm rcfn-min-inside-interval
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain)))
	    (inside-interval-p (rcfn-min-x a b) (rcfn-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (rcfn-min-x a b))
			     (interval (rcfn-domain)))
		  (:instance inside-interval-p-squeeze
			     (a b)
			     (b a)
			     (c (rcfn-min-x a b))
			     (interval (rcfn-domain)))
		  (:instance min-between-a-and-b-1)
		  (:instance min-between-a-and-b-2))
	    :in-theory (disable inside-interval-p-squeeze)))))

(local
 (defthm rcfn-max-inside-interval
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain)))
	    (inside-interval-p (rcfn-max-x a b) (rcfn-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (rcfn-max-x a b))
			     (interval (rcfn-domain)))
		  (:instance inside-interval-p-squeeze
			     (a b)
			     (b a)
			     (c (rcfn-max-x a b))
			     (interval (rcfn-domain)))
		  (:instance max-between-a-and-b-1)
		  (:instance max-between-a-and-b-2))
	    :in-theory (disable inside-interval-p-squeeze)))))

(defthm rcfn-min-close-to-x
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(standardp a)
		(i-close a b))
	   (i-close (rcfn a)
		    (rcfn (rcfn-min-x a b))))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (x a)
			    (y (rcfn-min-x a b)))
		 (:instance close-squeeze
			    (x a)
			    (y (rcfn-min-x a b))
			    (z b))
		 (:instance close-squeeze
			    (x b)
			    (y (rcfn-min-x a b))
			    (z a))
		 (:instance min-between-a-and-b-1)
		 (:instance min-between-a-and-b-2)
		 )
	   :in-theory (disable rcfn-continuous
			       close-squeeze
			       min-between-a-and-b-1
			       min-between-a-and-b-2)
	   )
	  ))

(defthm rcfn-max-close-to-x
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(standardp a)
		(i-close a b))
	   (i-close (rcfn a)
		    (rcfn (rcfn-max-x a b))))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (x a)
			    (y (rcfn-max-x a b)))
		 (:instance close-squeeze
			    (x a)
			    (y (rcfn-max-x a b))
			    (z b))
		 (:instance close-squeeze
			    (x b)
			    (y (rcfn-max-x a b))
			    (z a))
		 (:instance max-between-a-and-b-1)
		 (:instance max-between-a-and-b-2)
		 )
	   :in-theory (disable rcfn-continuous
			       close-squeeze
			       max-between-a-and-b-1
			       max-between-a-and-b-2)
	   )
	  ))

(local
 (defthmd ftc-1-lemma
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(standardp a)
		(i-close a b)
		(not (equal a b)))
	   (i-close (/ (int-rcfn a b)
		       (- b a))
		    (rcfn a)))
  :hints (("Goal"
	   :use ((:instance differential-int-rcfn-bounded)
		 (:instance close-squeeze
			    (x (rcfn (rcfn-min-x a b)))
			    (y (/ (int-rcfn a b)
				  (- b a)))
			    (z (rcfn (rcfn-max-x a b))))
		 (:instance i-close-transitive
			    (x (rcfn (rcfn-min-x a b)))
			    (y (rcfn a))
			    (z (rcfn (rcfn-max-x a b))))
		 (:instance i-close-transitive
			    (x (rcfn a))
			    (y (rcfn (rcfn-min-x a b)))
			    (z (/ (int-rcfn a b)
				  (- b a)))))
	   :in-theory (disable i-close-transitive)))))

(defthmd ftc-1
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(inside-interval-p c (rcfn-domain))
		(standardp b)
		(i-close b c)
		(not (equal b c)))
	   (i-close (/ (- (int-rcfn a b) (int-rcfn a c))
		       (- b c))
		    (rcfn b)))
  :hints (("Goal"
	   :use ((:instance ftc-1-lemma
			    (a b)
			    (b c))
		 (:instance split-rcfn-integral-by-subintervals
			    (a a)
			    (b c)
			    (c b))
		 (:instance push-sign-to-denominator
			    (a c)
			    (b b)
			    (c (int-rcfn b c)))
		 )
	   :in-theory (disable split-rcfn-integral-by-subintervals
			       |(* x (+ y z))|))))
