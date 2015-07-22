(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))

(include-book "continuous-function-2")

(local
 (defthmd multiply-inequalities-by-positive
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (< 0 c)
		 (<= a b))
	    (<= (* a c) (* b c)))))

(local
 (defthmd differential-int-rcfn-2-bounded-1
   (implies (and (inside-interval-p a (rcfn-2-domain))
		 (inside-interval-p b (rcfn-2-domain))
		 (< a b))
	    (and (<= (rcfn-2 (rcfn-2-min-x a b arg) arg)
		     (/ (int-rcfn-2 a b arg)
			(- b a)))
		 (<= (/ (int-rcfn-2 a b arg)
			(- b a))
		     (rcfn-2 (rcfn-2-max-x a b arg) arg))))
   :hints (("Goal"
	    :use ((:instance int-rcfn-2-bounded))
	    :in-theory (disable int-rcfn-2-bounded
				int-rcfn-2
				|(* (+ x y) z)|
				))
	   ("Subgoal 2"
	    :use ((:instance multiply-inequalities-by-positive
			     (a (* (rcfn-2 (rcfn-2-min-x a b arg) arg)
				   (- b a)))
			     (b (int-rcfn-2 a b arg))
			     (c (/ (- b a)))))
	    :in-theory (disable |(* (+ x y) z)|))
	   ("Subgoal 1"
	    :use ((:instance multiply-inequalities-by-positive
			     (a (int-rcfn-2 a b arg))
			     (b (* (rcfn-2 (rcfn-2-max-x a b arg) arg)
				   (- b a)))
			     (c (/ (- b a)))))
	    :in-theory (disable |(* (+ x y) z)|))
	   )))

(defthm int-rcfn-2-b-a
  (implies (< b a)
	   (equal (int-rcfn-2 a b arg)
		  (- (int-rcfn-2 b a arg))))
  :hints (("Goal"
	   :in-theory (enable int-rcfn-2)))
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
 (defthmd differential-int-rcfn-2-bounded-2
   (implies (and (inside-interval-p a (rcfn-2-domain))
		 (inside-interval-p b (rcfn-2-domain))
		 (< b a))
	    (and (<= (rcfn-2 (rcfn-2-min-x a b arg) arg)
		     (/ (int-rcfn-2 a b arg)
			(- b a)))
		 (<= (/ (int-rcfn-2 a b arg)
			(- b a))
		     (rcfn-2 (rcfn-2-max-x a b arg) arg))))
   :hints (("Goal"
	    :use ((:instance differential-int-rcfn-2-bounded-1 (a b) (b a))
                  (:instance push-sign-to-denominator
                             (c (int-rcfn-2 b a arg)))
		  )
	    :in-theory (disable differential-int-rcfn-2-bounded-1
				int-rcfn-2
				))
	   )))

(local
 (defthmd differential-int-rcfn-2-bounded
   (implies (and (inside-interval-p a (rcfn-2-domain))
		 (inside-interval-p b (rcfn-2-domain))
		 (not (equal a b)))
	    (and (<= (rcfn-2 (rcfn-2-min-x a b arg) arg)
		     (/ (int-rcfn-2 a b arg)
			(- b a)))
		 (<= (/ (int-rcfn-2 a b arg)
			(- b a))
		     (rcfn-2 (rcfn-2-max-x a b arg) arg))))
   :hints (("Goal"
	    :use ((:instance differential-int-rcfn-2-bounded-1)
		  (:instance differential-int-rcfn-2-bounded-2)
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
 (defthm rcfn-2-min-inside-interval
   (implies (and (inside-interval-p a (rcfn-2-domain))
		 (inside-interval-p b (rcfn-2-domain)))
	    (inside-interval-p (rcfn-2-min-x a b arg) (rcfn-2-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (rcfn-2-min-x a b arg))
			     (interval (rcfn-2-domain)))
		  (:instance inside-interval-p-squeeze
			     (a b)
			     (b a)
			     (c (rcfn-2-min-x a b arg))
			     (interval (rcfn-2-domain)))
		  (:instance min-between-a-and-b-2-1)
		  (:instance min-between-a-and-b-2-2))
	    :in-theory (disable inside-interval-p-squeeze)))))

(local
 (defthm rcfn-2-max-inside-interval
   (implies (and (inside-interval-p a (rcfn-2-domain))
		 (inside-interval-p b (rcfn-2-domain)))
	    (inside-interval-p (rcfn-2-max-x a b arg) (rcfn-2-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (rcfn-2-max-x a b arg))
			     (interval (rcfn-2-domain)))
		  (:instance inside-interval-p-squeeze
			     (a b)
			     (b a)
			     (c (rcfn-2-max-x a b arg))
			     (interval (rcfn-2-domain)))
		  (:instance max-between-a-and-b-2-1)
		  (:instance max-between-a-and-b-2-2))
	    :in-theory (disable inside-interval-p-squeeze)))))

(defthm rcfn-2-min-close-to-x
  (implies (and (standardp arg)
                (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(standardp a)
		(i-close a b))
	   (i-close (rcfn-2 a arg)
		    (rcfn-2 (rcfn-2-min-x a b arg) arg)))
  :hints (("Goal"
	   :use ((:instance rcfn-2-continuous
			    (x a)
			    (y (rcfn-2-min-x a b arg)))
		 (:instance close-squeeze
			    (x a)
			    (y (rcfn-2-min-x a b arg))
			    (z b))
		 (:instance close-squeeze
			    (x b)
			    (y (rcfn-2-min-x a b arg))
			    (z a))
		 (:instance min-between-a-and-b-2-1)
		 (:instance min-between-a-and-b-2-2)
		 )
	   :in-theory (disable rcfn-2-continuous
			       close-squeeze
			       min-between-a-and-b-2-1
			       min-between-a-and-b-2-2)
	   )
	  ))

(defthm rcfn-2-max-close-to-x
  (implies (and (standardp arg)
                (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(standardp a)
		(i-close a b))
	   (i-close (rcfn-2 a arg)
		    (rcfn-2 (rcfn-2-max-x a b arg) arg)))
  :hints (("Goal"
	   :use ((:instance rcfn-2-continuous
			    (x a)
			    (y (rcfn-2-max-x a b arg)))
		 (:instance close-squeeze
			    (x a)
			    (y (rcfn-2-max-x a b arg))
			    (z b))
		 (:instance close-squeeze
			    (x b)
			    (y (rcfn-2-max-x a b arg))
			    (z a))
		 (:instance max-between-a-and-b-2-1)
		 (:instance max-between-a-and-b-2-2)
		 )
	   :in-theory (disable rcfn-2-continuous
			       close-squeeze
			       max-between-a-and-b-2-1
			       max-between-a-and-b-2-2)
	   )
	  ))

(local
 (defthmd ftc-1-2-lemma
  (implies (and (standardp arg)
                (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(standardp a)
		(i-close a b)
		(not (equal a b)))
	   (i-close (/ (int-rcfn-2 a b arg)
		       (- b a))
		    (rcfn-2 a arg)))
  :hints (("Goal"
	   :use ((:instance differential-int-rcfn-2-bounded)
		 (:instance close-squeeze
			    (x (rcfn-2 (rcfn-2-min-x a b arg) arg))
			    (y (/ (int-rcfn-2 a b arg)
				  (- b a)))
			    (z (rcfn-2 (rcfn-2-max-x a b arg) arg)))
		 (:instance i-close-transitive
			    (x (rcfn-2 (rcfn-2-min-x a b arg) arg))
			    (y (rcfn-2 a arg))
			    (z (rcfn-2 (rcfn-2-max-x a b arg) arg)))
		 (:instance i-close-transitive
			    (x (rcfn-2 a arg))
			    (y (rcfn-2 (rcfn-2-min-x a b arg) arg))
			    (z (/ (int-rcfn-2 a b arg)
				  (- b a)))))
	   :in-theory (disable i-close-transitive)))))

(defthmd ftc-1-2
  (implies (and (standardp arg)
                (inside-interval-p a (rcfn-2-domain))
		(inside-interval-p b (rcfn-2-domain))
		(inside-interval-p c (rcfn-2-domain))
		(standardp b)
		(i-close b c)
		(not (equal b c)))
	   (i-close (/ (- (int-rcfn-2 a b arg) (int-rcfn-2 a c arg))
		       (- b c))
		    (rcfn-2 b arg)))
  :hints (("Goal"
	   :use ((:instance ftc-1-2-lemma
			    (a b)
			    (b c))
		 (:instance split-rcfn-2-integral-by-subintervals
			    (a a)
			    (b c)
			    (c b))
		 (:instance push-sign-to-denominator
			    (a c)
			    (b b)
			    (c (int-rcfn-2 b c arg)))
		 )
	   :in-theory (disable split-rcfn-2-integral-by-subintervals
			       |(* x (+ y z))|))))
