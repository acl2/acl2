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
	    (and (<= (rcfn context (rcfn-min-x context a b))
		     (/ (int-rcfn context a b)
			(- b a)))
		 (<= (/ (int-rcfn context a b)
			(- b a))
		     (rcfn context (rcfn-max-x context a b)))))
   :hints (("Goal"
	    :use ((:instance int-rcfn-bounded))
	    :in-theory (disable int-rcfn-bounded
				int-rcfn
				|(* (+ x y) z)|
				))
	   ("Subgoal 2"
	    :use ((:instance multiply-inequalities-by-positive
			     (a (* (rcfn context (rcfn-min-x context a b))
				   (- b a)))
			     (b (int-rcfn context a b))
			     (c (/ (- b a)))))
	    :in-theory (disable |(* (+ x y) z)|))
	   ("Subgoal 1"
	    :use ((:instance multiply-inequalities-by-positive
			     (a (int-rcfn context a b))
			     (b (* (rcfn context (rcfn-max-x context a b))
				   (- b a)))
			     (c (/ (- b a)))))
	    :in-theory (disable |(* (+ x y) z)|))
	   )))

(defthm int-rcfn-b-a
  (implies (< b a)
	   (equal (int-rcfn context a b)
		  (- (int-rcfn context b a))))
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
 (defthm push-sign-to-denominator-2
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (not (equal a b)))
	    (equal (- (* (/ (+ (- a) b)) c))
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
	    (and (<= (rcfn context (rcfn-min-x context a b))
		     (/ (int-rcfn context a b)
			(- b a)))
		 (<= (/ (int-rcfn context a b)
			(- b a))
		     (rcfn context (rcfn-max-x context a b)))))
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
	    (and (<= (rcfn context (rcfn-min-x context a b))
		     (/ (int-rcfn context a b)
			(- b a)))
		 (<= (/ (int-rcfn context a b)
			(- b a))
		     (rcfn context (rcfn-max-x context a b)))))
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
	    (inside-interval-p (rcfn-min-x context a b) (rcfn-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (rcfn-min-x context a b))
			     (interval (rcfn-domain)))
		  (:instance inside-interval-p-squeeze
			     (a b)
			     (b a)
			     (c (rcfn-min-x context a b))
			     (interval (rcfn-domain)))
		  (:instance min-between-a-and-b-1)
		  (:instance min-between-a-and-b-2))
	    :in-theory (disable inside-interval-p-squeeze)))))

(local
 (defthm rcfn-max-inside-interval
   (implies (and (inside-interval-p a (rcfn-domain))
		 (inside-interval-p b (rcfn-domain)))
	    (inside-interval-p (rcfn-max-x context a b) (rcfn-domain)))
   :hints (("Goal"
	    :use ((:instance inside-interval-p-squeeze
			     (a a)
			     (b b)
			     (c (rcfn-max-x context a b))
			     (interval (rcfn-domain)))
		  (:instance inside-interval-p-squeeze
			     (a b)
			     (b a)
			     (c (rcfn-max-x context a b))
			     (interval (rcfn-domain)))
		  (:instance max-between-a-and-b-1)
		  (:instance max-between-a-and-b-2))
	    :in-theory (disable inside-interval-p-squeeze)))))

(defthm rcfn-min-close-to-x
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(standardp a)
		(i-close a b)
                (standardp context))
	   (i-close (rcfn context a)
		    (rcfn context (rcfn-min-x context a b))))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (x a)
			    (y (rcfn-min-x context a b)))
		 (:instance close-squeeze
			    (x a)
			    (y (rcfn-min-x context a b))
			    (z b))
		 (:instance close-squeeze
			    (x b)
			    (y (rcfn-min-x context a b))
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
		(i-close a b)
                (standardp context))
	   (i-close (rcfn context a)
		    (rcfn context (rcfn-max-x context a b))))
  :hints (("Goal"
	   :use ((:instance rcfn-continuous
			    (x a)
			    (y (rcfn-max-x context a b)))
		 (:instance close-squeeze
			    (x a)
			    (y (rcfn-max-x context a b))
			    (z b))
		 (:instance close-squeeze
			    (x b)
			    (y (rcfn-max-x context a b))
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
                (standardp context)
		(not (equal a b)))
	   (i-close (/ (int-rcfn context a b)
		       (- b a))
		    (rcfn context a)))
  :hints (("Goal"
	   :use ((:instance differential-int-rcfn-bounded)
		 (:instance close-squeeze
			    (x (rcfn context (rcfn-min-x context a b)))
			    (y (/ (int-rcfn context a b)
				  (- b a)))
			    (z (rcfn context (rcfn-max-x context a b))))
		 (:instance i-close-transitive
			    (x (rcfn context (rcfn-min-x context a b)))
			    (y (rcfn context a))
			    (z (rcfn context (rcfn-max-x context a b))))
		 (:instance i-close-transitive
			    (x (rcfn context a))
			    (y (rcfn context (rcfn-min-x context a b)))
			    (z (/ (int-rcfn context a b)
				  (- b a)))))
	   :in-theory (disable i-close-transitive)))))

(defthmd ftc-1
  (implies (and (inside-interval-p a (rcfn-domain))
		(inside-interval-p b (rcfn-domain))
		(inside-interval-p c (rcfn-domain))
		(standardp b)
                (standardp context)
		(i-close b c)
		(not (equal b c)))
	   (i-close (/ (- (int-rcfn context a b) (int-rcfn context a c))
		       (- b c))
		    (rcfn context b)))
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
			    (c (int-rcfn context b c)))
		 )
	   :in-theory (disable split-rcfn-integral-by-subintervals
			       |(* x (+ y z))|))))
