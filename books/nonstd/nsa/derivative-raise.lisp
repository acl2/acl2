(in-package "ACL2")

(include-book "nonstd/nsa/raise" :dir :system)
(include-book "nonstd/nsa/derivatives" :dir :system)
(include-book "nonstd/nsa/intervals" :dir :system)
(local (include-book "nonstd/nsa/equivalence-derivatives" :dir :system))
(local (include-book "nonstd/nsa/equivalence-derivatives-composition" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(encapsulate
 nil

 (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-minimal" :dir :system))

 (defthm acl2-exp-derivative
   (implies (and (acl2-numberp x) (standardp x)
		 (acl2-numberp y)
		 (i-close x y) (not (equal x y)))
	    (i-close (/ (- (acl2-exp x) (acl2-exp y))
			(- x y))
		     (acl2-exp x))))
 )

(encapsulate
 nil

 (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real" :dir :system))

(defthm acl2-ln-real-derivative
  (implies (and (realp x) (< 0 x)
                (realp y) (< 0 y)
                (standardp x)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-ln x) (acl2-ln y))
                       (- x y))
                    (/ x))))
 )

(local
 (defun posfix (x)
   (if (and (realp x)
	    (< 0 x))
       x
     1)))


(local
 (defun raise1-fn1 (x)
   (acl2-exp (realfix x))))

(local
 (defun raise1-fn1-domain ()
   (interval nil nil)))

(local
 (defun differential-raise1-fn1 (x eps)
   (/ (- (raise1-fn1 (+ x eps))
	 (raise1-fn1 x) )
      eps)))

(local
 (defun derivative-raise1-fn1 (x)
   (raise1-fn1 x)))

(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fn1-works (x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn1-domain))
			 (inside-interval-p x (raise1-fn1-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fn1 x) (raise1-fn1 x1)) (- x x1))
			       (derivative-raise1-fn1 x)))
		       eps)))
   :rewrite :direct))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works (x eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn1-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fn1-works x eps delta))))))

(local
 (defthm inside-interval-p-nil
   (equal (inside-interval-p x '(nil))
	  (realp x))
   :hints (("Goal"
	    :expand ((inside-interval-p x '(nil)))))))

(local
 (defthm inside-interval-p-0
   (equal (inside-interval-p x '((0)))
	  (and (realp x)
	       (< 0 x)))
   :hints (("Goal"
	    :expand ((inside-interval-p x '((0))))))))

(local
 (defthmd raise1-fn1-differentiable-classical-using-hyperreal-criterion
   (implies (and (inside-interval-p x (raise1-fn1-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works x eps))
   :hints (("Goal"
	    :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				      (rdfn raise1-fn1)
				      (rdfn-domain raise1-fn1-domain)
				      (differential-rdfn differential-raise1-fn1)
				      (derivative-rdfn derivative-raise1-fn1)
				      (forall-x-eps-delta-in-range-deriv-works
				       forall-x-eps-delta-in-range-deriv-raise1-fn1-works)
				      (forall-x-eps-delta-in-range-deriv-works-witness
				       forall-x-eps-delta-in-range-deriv-raise1-fn1-works-witness)
				      (exists-delta-for-x-and-eps-so-deriv-works
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works)
				      (exists-delta-for-x-and-eps-so-deriv-works-witness
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works-witness)))
	   ("Subgoal 7"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn1-works))
	   ("Subgoal 5"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn1-works-necc))
	    )
	   ("Subgoal 3"
	    :use ((:instance acl2-exp-derivative
			     (x x)
			     (y (+ x (/ (i-large-integer)))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance close-x-y->same-standard-part
			     (x (acl2-exp x))
			     (y (/ (- (raise1-fn1 x) (raise1-fn1 (+ x (/ (i-large-integer)))))
				   (- (/ (i-large-integer))))))
		  )
	    :in-theory (disable acl2-exp-derivative
				i-close-to-small-sum
				standard-part-of-plus)
	    )
	   ("Subgoal 1"
	    :use ((:instance acl2-exp-derivative
			     (x x)
			     (y y1))
		  (:instance acl2-exp-derivative
			     (x x)
			     (y y2))
		  (:instance i-close-limited
			     (x (acl2-exp x))
			     (y (/ (- (acl2-exp x) (acl2-exp y1))
				   (- x y1))))
		  (:instance i-close-transitive
			     (x (/ (- (acl2-exp x) (acl2-exp y1))
				   (- x y1)))
			     (y (acl2-exp x))
			     (z (/ (- (acl2-exp x) (acl2-exp y2))
				   (- x y2)))))
	    :in-theory (disable acl2-exp-derivative
				i-close-limited
				i-close-transitive))
	   )))

(local
 (defun raise1-fn2a (x n)
   (declare (ignore x))
   (realfix n)))

(local
 (defun raise1-fn2b (x)
   (acl2-ln (posfix x))))

(local
 (defun raise1-fn2a*fn2b (x n)
   (* (realfix n)
      (acl2-ln (posfix x)))))

(local
 (defun raise1-fn2 (x n)
   (* (realfix n)
      (acl2-ln (posfix x)))))

(local
 (defun raise1-fn2-domain ()
   (interval '(0) nil)))

(local
 (defun raise1-fn2-range ()
   (interval nil nil)))

(local
 (defun differential-raise1-fn2a (x n eps)
   (declare (ignore x))
   (/ (- (realfix n)
	 (realfix n))
      eps)))

(local
 (defun differential-raise1-fn2b (x eps)
   (/ (- (raise1-fn2b (+ x eps))
	 (raise1-fn2b x))
      eps)))

(local
 (defun differential-raise1-fn2a*fn2b (x n eps)
   (+ (* (raise1-fn2a (+ x eps) n)
	 (differential-raise1-fn2b x eps))
      (* (raise1-fn2b x)
	 (differential-raise1-fn2a x n eps)))))

(local
 (defun derivative-raise1-fn2a (x n)
   (declare (ignore x n))
   0))

(local
 (defun derivative-raise1-fn2b (x)
   (/ (posfix x))))

(local
 (defun derivative-raise1-fn2a*fn2b (x n)
   (+ (* (raise1-fn2a x n)
	 (derivative-raise1-fn2b x))
      (* (raise1-fn2b x)
	 (derivative-raise1-fn2a x n)))))

(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fn2a-works (x n eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn2-domain))
			 (inside-interval-p x (raise1-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fn2a x n) (raise1-fn2a x1 n)) (- x x1))
			       (derivative-raise1-fn2a x n)))
		       eps)))
   :rewrite :direct))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works (x n eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn2-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fn2a-works x n eps delta))))))

(local
 (defthmd raise1-fn2a-differentiable-classical-using-hyperreal-criterion
   (implies (and (inside-interval-p x (raise1-fn1-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works x n eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works-suff
			     (delta 1)))))))

(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fn2b-works (x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn2-domain))
			 (inside-interval-p x (raise1-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fn2b x) (raise1-fn2b x1)) (- x x1))
			       (derivative-raise1-fn2b x)))
		       eps)))
   :rewrite :direct))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works (x eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn2-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fn2b-works x eps delta))))))

(local
 (defthm-std standard-/
   (implies (standardp x)
	    (standardp (/ x)))))

(local
 (defthmd raise1-fn2b-differentiable-classical-using-hyperreal-criterion
   (implies (and (inside-interval-p x (raise1-fn2-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works x eps))
   :hints (("Goal"
	    :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				      (rdfn raise1-fn2b)
				      (rdfn-domain raise1-fn2-domain)
				      (differential-rdfn differential-raise1-fn2b)
				      (derivative-rdfn derivative-raise1-fn2b)
				      (forall-x-eps-delta-in-range-deriv-works
				       forall-x-eps-delta-in-range-deriv-raise1-fn2b-works)
				      (forall-x-eps-delta-in-range-deriv-works-witness
				       forall-x-eps-delta-in-range-deriv-raise1-fn2b-works-witness)
				      (exists-delta-for-x-and-eps-so-deriv-works
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works)
				      (exists-delta-for-x-and-eps-so-deriv-works-witness
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works-witness)))
	   ("Subgoal 7"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2b-works))
	   ("Subgoal 5"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn2b-works-necc))
	    )
	   ("Subgoal 3"
	    :use ((:instance acl2-ln-real-derivative
			     (x x)
			     (y (+ x (/ (i-large-integer)))))
		  (:instance acl2-ln-real-derivative
			     (x x)
			     (y (- x (/ (i-large-integer)))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (- (/ (i-large-integer)))))
		  (:instance close-x-y->same-standard-part
			     (x (/ x))
			     (y (/ (- (raise1-fn2b x) (raise1-fn2b (+ x (/ (i-large-integer)))))
				   (- (/ (i-large-integer))))))
		  (:instance close-x-y->same-standard-part
			     (x (/ x))
			     (y (/ (- (raise1-fn2b x) (raise1-fn2b (- x (/ (i-large-integer)))))
				   (- (/ (i-large-integer))))))
		  (:instance standards-are-limited
			     (x (/ x)))
		  )
	    :in-theory (disable acl2-ln-real-derivative
				i-close-to-small-sum
				standard-part-of-plus
				standards-are-limited)
	    )
	   ("Subgoal 1"
	    :use ((:instance acl2-ln-real-derivative
			     (x x)
			     (y y1))
		  (:instance acl2-ln-real-derivative
			     (x x)
			     (y y2))
		  (:instance i-close-limited
			     (x (/ x))
			     (y (/ (- (acl2-ln x) (acl2-ln y1))
				   (- x y1))))
		  (:instance i-close-transitive
			     (x (/ (- (acl2-ln x) (acl2-ln y1))
				   (- x y1)))
			     (y (/ x))
			     (z (/ (- (acl2-ln x) (acl2-ln y2))
				   (- x y2))))
		  (:instance standards-are-limited
			     (x (/ x))))
	    :in-theory (disable acl2-ln-real-derivative
				i-close-limited
				i-close-transitive
				standards-are-limited)))))


(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works (x n eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn2-domain))
			 (inside-interval-p x (raise1-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fn2a*fn2b x n) (raise1-fn2a*fn2b x1 n)) (- x x1))
			       (derivative-raise1-fn2a*fn2b x n)))
		       eps)))
   :rewrite :direct))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works (x n eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn2-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works x n eps delta))))))

(local
 (defun raise1-fnz (x)
   (declare (ignore x))
   1))

(local
 (defun derivative-raise1-fnz (x)
   (declare (ignore x))
   0))

(local
 (defun differential-raise1-fnz (x eps)
   (/ (- (raise1-fnz (+ x eps)) (raise1-fnz x))
      eps)))

(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fnz-works (x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn2-domain))
			 (inside-interval-p x (raise1-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fnz x) (raise1-fnz x1)) (- x x1))
			       (derivative-raise1-fnz x)))
		       eps)))
   :rewrite :direct))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works (x  eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn2-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fnz-works x eps delta))))))


(local
 (defthmd raise1-fn2a*fn2b-differentiable-classical-using-hyperreal-criterion
   (implies (and (inside-interval-p x (raise1-fn2-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works x n eps))
   :hints (("Goal"
	    :by (:functional-instance
		 dcc-fn1*fn2-differentiable-classical-using-hyperreal-criterion
		 (dcc-fn1 (lambda (x) (raise1-fn2a x n)))
		 (dcc-fn2 raise1-fn2b)
		 (differential-dcc-fn1
		  (lambda (x eps) (differential-raise1-fn2a x n eps)))
		 (differential-dcc-fn2 differential-raise1-fn2b)
		 (differential-dcc-fn1*fn2 (lambda (x eps) (differential-raise1-fn2a*fn2b x n eps)))
		 (derivative-dcc-fn1
		  (lambda (x) (derivative-raise1-fn2a x n)))
		 (derivative-dcc-fn2 derivative-raise1-fn2b)
		 (dcc-fn1*fn2 (lambda (x) (raise1-fn2a*fn2b x n)))
		 (derivative-dcc-fn1*fn2 (lambda (x) (derivative-raise1-fn2a*fn2b x n)))
		 (dcc-fnz raise1-fnz)
		 (differential-dcc-fnz differential-raise1-fnz)
		 (derivative-dcc-fnz derivative-raise1-fnz)
		 (dcc-fn-domain raise1-fn2-domain)
		 (forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1
		  (lambda (x eps delta)
		    (forall-x-eps-delta-in-range-deriv-raise1-fn2a-works x n eps delta)))
		 (forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1-witness
		  (lambda (x eps delta)
		    (forall-x-eps-delta-in-range-deriv-raise1-fn2a-works-witness x n eps delta)))
		 (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1
		  (lambda (x eps)
		    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works x n eps)))
		 (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1-witness
		  (lambda (x eps)
		    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works-witness x n eps)))
		 (forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2
		  forall-x-eps-delta-in-range-deriv-raise1-fn2b-works)
		 (forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2-witness
		  forall-x-eps-delta-in-range-deriv-raise1-fn2b-works-witness)
		 (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2
		  exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works)
		 (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2-witness
		  exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works-witness)
		 (forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz
		  forall-x-eps-delta-in-range-deriv-raise1-fnz-works)
		 (forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz-witness
		  forall-x-eps-delta-in-range-deriv-raise1-fnz-works-witness)
		 (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz
		  exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works)
		 (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz-witness
		  exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works-witness)
		 (forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works
		  (lambda (x eps delta)
		    (forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works x n eps delta)))
		 (forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works-witness
		  (lambda (x eps delta)
		    (forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works-witness x n eps delta)))
		 (exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works
		  (lambda (x eps)
		    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works x n eps)))
		 (exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works-witness
		  (lambda (x eps)
		    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works-witness x n eps)))
		 )
	    )
	   ("Subgoal 21"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works))
	   ("Subgoal 19"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works-necc))
	    )
	   ("Subgoal 17"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works-suff
			     (delta 1))))
	   ("Subgoal 16"
	    :use ((:instance raise1-fn2b-differentiable-classical-using-hyperreal-criterion)))
	   ("Subgoal 15"
	    :use ((:instance raise1-fn2a-differentiable-classical-using-hyperreal-criterion)))
	   ("Subgoal 13"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fnz-works))
	   ("Subgoal 11"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2b-works))
	   ("Subgoal 9"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2a-works))
	   ("Subgoal 6"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn2b-works-necc)))
	   )))

(local
 (defthmd expand-raise1-fn2a*fn2b
   (equal (raise1-fn2a*fn2b x n)
	  (raise1-fn2 x n))))

(local (in-theory (disable raise1-fn2a*fn2b)))

(local
 (defun differential-raise1-fn2 (x n eps)
   (/ (- (raise1-fn2 (+ x eps) n)
	 (raise1-fn2 x n))
      eps)))

(local
 (defthmd expand-differential-raise1-fn2a*fn2b
   (implies (and (inside-interval-p x (raise1-fn2-domain))
		 (inside-interval-p (+ x eps) (raise1-fn2-domain)))
	    (equal (differential-raise1-fn2a*fn2b x n eps)
		   (differential-raise1-fn2 x n eps)))
   :hints (("Goal"
	    :use ((:functional-instance expand-differential-dcc-fn1*fn2
					(dcc-fn1 (lambda (x) (raise1-fn2a x n)))
					(dcc-fn2 raise1-fn2b)
					(differential-dcc-fn1
					 (lambda (x eps) (differential-raise1-fn2a x n eps)))
					(differential-dcc-fn2 differential-raise1-fn2b)
					(differential-dcc-fn1*fn2 (lambda (x eps) (differential-raise1-fn2a*fn2b x n eps)))
					(derivative-dcc-fn1
					 (lambda (x) (derivative-raise1-fn2a x n)))
					(derivative-dcc-fn2 derivative-raise1-fn2b)
					(dcc-fn1*fn2 (lambda (x) (raise1-fn2a*fn2b x n)))
					(derivative-dcc-fn1*fn2 (lambda (x) (derivative-raise1-fn2a*fn2b x n)))
					(dcc-fnz raise1-fnz)
					(differential-dcc-fnz differential-raise1-fnz)
					(derivative-dcc-fnz derivative-raise1-fnz)
					(dcc-fn-domain raise1-fn2-domain)
					(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1
					 (lambda (x eps delta)
					   (forall-x-eps-delta-in-range-deriv-raise1-fn2a-works x n eps delta)))
					(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1-witness
					 (lambda (x eps delta)
					   (forall-x-eps-delta-in-range-deriv-raise1-fn2a-works-witness x n eps delta)))
					(exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1
					 (lambda (x eps)
					   (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works x n eps)))
					(exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1-witness
					 (lambda (x eps)
					   (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a-works-witness x n eps)))
					(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2
					 forall-x-eps-delta-in-range-deriv-raise1-fn2b-works)
					(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2-witness
					 forall-x-eps-delta-in-range-deriv-raise1-fn2b-works-witness)
					(exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2
					 exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works)
					(exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2-witness
					 exists-delta-for-x-and-eps-so-deriv-raise1-fn2b-works-witness)
					(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz
					 forall-x-eps-delta-in-range-deriv-raise1-fnz-works)
					(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz-witness
					 forall-x-eps-delta-in-range-deriv-raise1-fnz-works-witness)
					(exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz
					 exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works)
					(exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz-witness
					 exists-delta-for-x-and-eps-so-deriv-raise1-fnz-works-witness)					)))
	   )
   ))

(local (in-theory (disable differential-raise1-fn2a*fn2b)))

(local
 (defun derivative-raise1-fn2 (x n)
   (+ (* (raise1-fn2a x n)
	 (derivative-raise1-fn2b x))
      (* (raise1-fn2b x)
	 (derivative-raise1-fn2a x n)))))


(local
 (defthmd expand-derivative-raise1-fn2a*fn2b
   (equal (derivative-raise1-fn2a*fn2b x n)
	  (derivative-raise1-fn2 x n))))

(local (in-theory (disable derivative-raise1-fn2a*fn2b)))

(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fn2-works (x n eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn2-domain))
			 (inside-interval-p x (raise1-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fn2 x n) (raise1-fn2 x1 n)) (- x x1))
			       (derivative-raise1-fn2 x n)))
		       eps)))
   :rewrite :direct))

(local
 (defthmd forall-fn2a*fn2b->forall-fn2
   (implies (forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works x n eps delta)
	    (forall-x-eps-delta-in-range-deriv-raise1-fn2-works x n eps delta))
   :hints (("Goal"
	    :expand ((forall-x-eps-delta-in-range-deriv-raise1-fn2-works x n eps delta))
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works-necc
			     (x1 (forall-x-eps-delta-in-range-deriv-raise1-fn2-works-witness x n eps delta)))
		  (:instance expand-raise1-fn2a*fn2b)
		  (:instance expand-raise1-fn2a*fn2b
			     (x (forall-x-eps-delta-in-range-deriv-raise1-fn2-works-witness x n eps delta)))
		  (:instance expand-derivative-raise1-fn2a*fn2b)
		  )
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works-necc
				derivative-raise1-fn2
				forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works)
))))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works (x n eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn2-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fn2-works x n eps delta))))))

(local
 (defthmd exists-fn2a*fn2b->exists-fn2
   (implies (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works x n eps)
	    (exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works x n eps))
   :hints (("Goal"
	    :expand ((exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works x n eps))
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works-suff
			     (delta (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works-witness x n eps)))
		  (:instance forall-fn2a*fn2b->forall-fn2
			     (delta (exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works-witness x n eps))))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2a*fn2b-works
				forall-x-eps-delta-in-range-deriv-raise1-fn2-works)))))


(local
 (defun raise1-fn1-o-fn2 (x n)
   (raise1-fn1 (raise1-fn2 (realfix x) (realfix n)))))

(local
 (defun differential-raise1-fn1-o-fn2 (x n eps)
   (if (equal (raise1-fn2 (+ x eps) n) (raise1-fn2 x n))
       0
     (* (differential-raise1-fn1 (raise1-fn2 x n)
				(- (raise1-fn2 (+ x eps) n)
				   (raise1-fn2 x n)))
	(differential-raise1-fn2 x n eps)))))

(local
 (defun derivative-raise1-fn1-o-fn2 (x n)
   (* (derivative-raise1-fn1 (raise1-fn2 x n))
      (derivative-raise1-fn2 x n))))

(local
 (defun-sk forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works (x n eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (raise1-fn2-domain))
			 (inside-interval-p x (raise1-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (raise1-fn1-o-fn2 x n) (raise1-fn1-o-fn2 x1 n)) (- x x1))
			       (derivative-raise1-fn1-o-fn2 x n)))
		       eps)))
   :rewrite :direct))

(local
 (defun-sk exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works (x n eps)
   (exists delta
	   (implies (and (inside-interval-p x (raise1-fn2-domain))
					;(standardp x)
			 (realp eps)
					;(standardp eps)
			 (< 0 eps))
		    (and (realp delta)
			 (< 0 delta)
			 (forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works x n eps delta))))))


(local
 (defthmd raise1-fn1-o-fn2-differentiable-classical-using-hyperreal-criterion
   (implies (and (inside-interval-p x (raise1-fn2-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works x n eps))
   :hints (("Goal"
	    :by (:functional-instance ccr-fn1-o-fn2-differentiable-classical-using-hyperreal-criterion
				      (ccr-fn1 raise1-fn1)
				      (derivative-ccr-fn1 derivative-raise1-fn1)
				      (differential-ccr-fn1 differential-raise1-fn1)
				      (ccr-fn2
				       (lambda (x) (raise1-fn2 x n)))
				      (derivative-ccr-fn2
				       (lambda (x) (derivative-raise1-fn2 x n)))
				      (differential-ccr-fn2
				       (lambda (x eps) (differential-raise1-fn2 x n eps)))
				      (ccr-fn1-o-fn2
				       (lambda (x) (raise1-fn1-o-fn2 x n)))
				      (derivative-ccr-fn1-o-fn2
				       (lambda (x) (derivative-raise1-fn1-o-fn2 x n)))
				      (differential-ccr-fn1-o-fn2
				       (lambda (x eps) (differential-raise1-fn1-o-fn2 x n eps)))
				      (ccr-fn2-domain raise1-fn2-domain)
				      (ccr-fn2-range raise1-fn2-range)
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1
				       forall-x-eps-delta-in-range-deriv-raise1-fn1-works)
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1-witness
				       forall-x-eps-delta-in-range-deriv-raise1-fn1-works-witness)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1-witness
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn2-works x n eps delta)))
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2-witness
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn2-works-witness x n eps delta)))
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2
				       (lambda (x eps) (exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works x n eps)))
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2-witness
				       (lambda (x eps) (exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works-witness x n eps)))
				      (forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works x n eps delta)))
				      (forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works-witness
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works-witness x n eps delta)))
				      (exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works
				       (lambda (x eps)
					 (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works x n eps)))
				      (exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works-witness
				       (lambda (x eps)
					 (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works-witness x n eps)))
				      ))
	   ("Subgoal 16"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works))
	   ("Subgoal 14"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works-necc))
	    :in-theory (enable raise1-fn1-o-fn2
			       raise1-fn1
			       raise1-fn2))
	   ("Subgoal 11"
	    :use ((:instance exists-fn2a*fn2b->exists-fn2)
		  (:instance raise1-fn2a*fn2b-differentiable-classical-using-hyperreal-criterion))
	    :in-theory (disable exists-delta-for-x-and-eps-so-deriv-raise1-fn2a*fn2b-works
				exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works))
	   ("Subgoal 10"
	    :use ((:instance raise1-fn1-differentiable-classical-using-hyperreal-criterion)))
	   ("Subgoal 8"
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works-suff))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn2-works))
	   ("Subgoal 6"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn2-works-necc))
	    :in-theory (enable raise1-fn2))
	   ("Subgoal 4"
	    :use ((:instance raise1-fn1-differentiable-classical-using-hyperreal-criterion)))
	   ("Subgoal 2"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn1-works-necc))
	    :in-theory (enable raise1-fn1
			       derivative-raise1-fn1))
	   ))
 )


(local
 (defthmd expand-differential-raise1-fn1-o-fn2
   (implies (and (inside-interval-p x (raise1-fn2-domain))
                 (inside-interval-p (+ x eps)
                                    (raise1-fn2-domain)))
            (equal (differential-raise1-fn1-o-fn2 x n eps)
                   (/ (- (raise1-fn1-o-fn2 (+ x eps) n) (raise1-fn1-o-fn2 x n)) eps)))
   :hints (("Goal"
	    :by (:functional-instance expand-differential-ccr-fn1-o-fn2
				      (ccr-fn1 raise1-fn1)
				      (derivative-ccr-fn1 derivative-raise1-fn1)
				      (differential-ccr-fn1 differential-raise1-fn1)
				      (ccr-fn2
				       (lambda (x) (raise1-fn2 x n)))
				      (derivative-ccr-fn2
				       (lambda (x) (derivative-raise1-fn2 x n)))
				      (differential-ccr-fn2
				       (lambda (x eps) (differential-raise1-fn2 x n eps)))
				      (ccr-fn1-o-fn2
				       (lambda (x) (raise1-fn1-o-fn2 x n)))
				      (derivative-ccr-fn1-o-fn2
				       (lambda (x) (derivative-raise1-fn1-o-fn2 x n)))
				      (differential-ccr-fn1-o-fn2
				       (lambda (x eps) (differential-raise1-fn1-o-fn2 x n eps)))
				      (ccr-fn2-domain raise1-fn2-domain)
				      (ccr-fn2-range raise1-fn2-range)
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1
				       forall-x-eps-delta-in-range-deriv-raise1-fn1-works)
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1-witness
				       forall-x-eps-delta-in-range-deriv-raise1-fn1-works-witness)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1-witness
				       exists-delta-for-x-and-eps-so-deriv-raise1-fn1-works-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn2-works x n eps delta)))
				      (forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2-witness
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn2-works-witness x n eps delta)))
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2
				       (lambda (x eps) (exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works x n eps)))
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2-witness
				       (lambda (x eps) (exists-delta-for-x-and-eps-so-deriv-raise1-fn2-works-witness x n eps)))
				      (forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works x n eps delta)))
				      (forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works-witness
				       (lambda (x eps delta)
					 (forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works-witness x n eps delta)))
				      (exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works
				       (lambda (x eps)
					 (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works x n eps)))
				      (exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works-witness
				       (lambda (x eps)
					 (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works-witness x n eps)))
				      ))
	   )))


(local
 (defthm raise1-fn1-o-fn2->raise
   (implies (and (realp x)
		 (< 0 x)
		 (realp n))
	    (equal (raise1-fn1-o-fn2 x n)
		   (raise x n)))
   :hints (("Goal"
	    :expand ((raise1-fn1-o-fn2 x n))))
   ))

(defun positive-domain ()
  (interval '(0) nil))

(defun real-domain ()
  (interval nil nil))

(defun derivative-raise (x n)
  (* n (raise x (1- n))))

(local
 (defthm derivative-raise1-fn1-o-fn2->derivative-raise
   (implies (and (realp x)
		 (< 0 x)
		 (realp n))
	    (equal (derivative-raise1-fn1-o-fn2 x n)
		   (derivative-raise x n)))))

(defun-sk forall-x-eps-delta-in-range-deriv-raise-posp-x-works (x n eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (positive-domain))
			(inside-interval-p x (positive-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (raise x n) (raise x1 n)) (- x x1))
			      (derivative-raise x n)))
		      eps)))
  :rewrite :direct)

(local
 (defthmd forall-raise1-fn1-o-fn2->forall-raise-posp
   (implies (and (realp x)
		 (< 0 x)
		 (realp n)
		 (forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works x n eps delta)
		 )
	    (forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps delta))
   :hints (("Goal"
	    :expand ((forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps delta))
	    :use ((:instance forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works-necc
			     (x1 (forall-x-eps-delta-in-range-deriv-raise-posp-x-works-witness x n eps delta))))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works-necc
				derivative-raise1-fn1-o-fn2
				derivative-raise
				forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works)))
))

(defun-sk exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works (x n eps)
  (exists delta
	  (implies (and (inside-interval-p x (positive-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps delta)))))


(local
 (defthmd exists-raise1-fn1-o-fn2->exists-raise-posp
   (implies (and (realp x)
		 (< 0 x)
		 (realp n)
		 (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works x n eps)
		 )
	    (exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works x n eps))
   :hints (("Goal"
	    :expand ((exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works x n eps))
	    :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works-suff
			     (delta (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works-witness x n eps)))
		  (:instance forall-raise1-fn1-o-fn2->forall-raise-posp
			     (delta (exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works-witness x n eps))))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works
				forall-x-eps-delta-in-range-deriv-raise-posp-x-works)))))

(defun-sk forall-x-eps-delta-in-range-deriv-raise-works (x n eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (real-domain))
			(inside-interval-p x (real-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (raise x n) (raise x1 n)) (- x x1))
			      (derivative-raise x n)))
		      eps)))
  :rewrite :direct)

(defthmd forall-raise-posp->forall-raise
  (implies (and (realp x)
                (< 0 x)
                (realp n)
                (realp delta)
                (< 0 delta)
                (< delta x)
                (forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps delta)
                )
           (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta))
  :hints (("Goal"
           :expand ((forall-x-eps-delta-in-range-deriv-raise-works x n eps
                                                                   delta))
           :use ((:instance  forall-x-eps-delta-in-range-deriv-raise-posp-x-works-necc
                            (x1 (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                 x n eps delta)))
                 )
           :in-theory (disable forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works-necc
                               derivative-raise1-fn1-o-fn2
                               derivative-raise
                               forall-x-eps-delta-in-range-deriv-raise1-fn1-o-fn2-works
                               derivative-raise
                               raise)))
  )


(defun-sk exists-delta-for-x-and-eps-so-deriv-raise-works (x n eps)
  (exists delta
	  (implies (and (inside-interval-p x (real-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-raise-works x n eps delta)))))

(local
 (encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps delta)
		   (realp delta)
		   (< 0 delta)
		   (realp gamma)
		   (< 0 gamma)
		   (< gamma delta))
	      (forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps gamma))
     :hints (("Goal"
	      :use ((:instance forall-x-eps-delta-in-range-deriv-raise-posp-x-works-necc
			       (x1 (forall-x-eps-delta-in-range-deriv-raise-posp-x-works-witness x n eps gamma))))
	      :in-theory (disable abs)))
     ))


  (local
   (defun fix-delta (delta x)
     (if (< delta x)
	 delta
       (/ x 2))))

  (local
   (defthmd fix-delta-works
     (implies (and (realp x)
		   (< 0 x)
		   (realp delta)
		   (< 0 delta))
	      (and (realp (fix-delta delta x))
		   (< 0 (fix-delta delta x))
		   (< (fix-delta delta x) x)))))
  (local
   (defthmd lemma-2
     (implies (and (realp x)
		   (< 0 x)
		   (realp delta)
		   (< 0 delta)
		   (forall-x-eps-delta-in-range-deriv-raise-posp-x-works x n eps delta)
		   )
	      (forall-x-eps-delta-in-range-deriv-raise-posp-x-works
	       x n eps (fix-delta delta x)))
     :hints (("Goal"
	      :use ((:instance fix-delta-works)
		    (:instance lemma-1
			       (gamma (fix-delta delta x))))
	      :in-theory (disable forall-x-eps-delta-in-range-deriv-raise-posp-x-works)
	      ))))



  (defthmd exists-raise-posp->exists-raise
    (implies (and (realp x)
		  (< 0 x)
		  (realp n)
		  (exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works x n eps)
		  )
	     (exists-delta-for-x-and-eps-so-deriv-raise-works x n eps))
    :hints (("Goal"
	     :expand ((exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works x n eps))
	     :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise-works-suff
			      (delta (fix-delta (exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works-witness x n eps)
						x)))
		   (:instance lemma-2
			      (delta (exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works-witness x n eps)))
		   (:instance forall-raise-posp->forall-raise
			      (delta (fix-delta (exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works-witness x n eps)
						x))))
	     :in-theory (disable forall-x-eps-delta-in-range-deriv-raise-works
				 forall-x-eps-delta-in-range-deriv-raise-posp-x-works))))
  ))


(local
 (defthmd raise-differentiable-for-posp-x-using-hyperreal-criterion
   (implies (and (inside-interval-p x (positive-domain))
		 (realp n)
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-raise-works x n eps))
   :hints (("Goal"
	    :use ((:instance raise1-fn1-o-fn2-differentiable-classical-using-hyperreal-criterion)
		  (:instance exists-raise1-fn1-o-fn2->exists-raise-posp)
		  (:instance exists-raise-posp->exists-raise))
	    :in-theory (disable raise1-fn1-o-fn2-differentiable-classical-using-hyperreal-criterion
				exists-raise1-fn1-o-fn2->exists-raise-posp
				exists-raise-posp->exists-raise
				exists-delta-for-x-and-eps-so-deriv-raise-works
				exists-delta-for-x-and-eps-so-deriv-raise-posp-x-works
				exists-delta-for-x-and-eps-so-deriv-raise1-fn1-o-fn2-works)))))


;--------------------------

(local
 (defthmd ln-negative
   (implies (and (realp x)
		 (< 0 x))
	    (equal (acl2-ln (- x))
		   (+ (acl2-ln x)
		      (* #c(0 1)
			 (acl2-pi)))))
   :hints (("Goal"
	    :expand ((acl2-ln (- x))
		     (acl2-ln x))
	    :use ((:instance complex-definition
			     (x (acl2-ln-for-positive x))
			     (y (acl2-pi))))
	    ))
   ))

(local
 (defthm ln-1=0
   (equal (acl2-ln 1) 0)
   :hints (("Goal"
	    :use ((:instance uniqueness-of-ln
			     (y 1)
			     (x 0)))))))

(local
 (defthm exp-i-pi-n
   (equal (acl2-exp (* #c(0 1)
		       (acl2-pi)
		       n))
	  (raise -1 n))
   :hints (("Goal"
	    :in-theory (e/d (ln-negative)
			    (e^ix-cos-i-sin))))
   ))

(local
 (encapsulate
  nil
  (local (include-book "nonstd/nsa/exp-sum" :dir :system))

  (defthm exp-sum
    (implies (and (acl2-numberp x)
		  (acl2-numberp y))
	     (equal (acl2-exp (+ x y))
		    (* (acl2-exp x) (acl2-exp y)))))
  ))

(local
 (defthmd raise-for-negative-x
   (implies (and (realp x)
		 (< x 0))
	    (equal (raise x n)
		   (* (raise (- x) n)
		      (raise -1 n))))
   :hints (("Goal"
	    :use ((:instance ln-negative (x (- x))))
	    ))
   ))

(local
 (defthmd raise-for-negative-x-integer-n
   (implies (and (realp x)
		 (< x 0)
		 (integerp n))
	    (equal (raise x n)
		   (* (raise (- x) n)
		      (expt -1 n))))
   :hints (("Goal"
	    :use ((:instance raise-for-negative-x))))))


(local
 (defun raise-to-int (x n)
   (raise (realfix x) (ifix n))))

(local
 (defthm raise-to-int->raise
   (implies (and (realp x)
		 (integerp n))
	    (equal (raise-to-int x n)
		   (raise x n)))
   :hints (("Goal"
	    :expand ((raise-to-int x n))))
   ))

(local
 (defthmd differential-numer-neg-x
   (implies (and (realp x)
		 (< x 0)
		 (realp x1)
		 (< x1 0)
		 (integerp n))
	    (equal (- (raise x n) (raise x1 n))
		   (* (expt -1 n)
		      (- (raise (- x) n) (raise (- x1) n)))))
   :hints (("Goal"
	    :use ((:instance raise-for-negative-x-integer-n)
		  (:instance raise-for-negative-x-integer-n (x x1)))
	    :in-theory (disable raise
				raise-expt
				expt
				|(expt (- c) n)|)))))

(local
 (defthmd differential-denom-neg-x
   (implies (and (realp x)
		 (< x 0)
		 (realp x1)
		 (< x1 0)
		 (integerp n))
	    (equal (- x x1)
		   (* -1
		      (- (- x) (- x1)))))))

(local
 (defthmd differential-neg-x
   (implies (and (realp x)
		 (< x 0)
		 (realp x1)
		 (< x1 0)
		 (not (equal x x1))
		 (integerp n))
	    (equal (/ (- (raise x n) (raise x1 n))
		      (- x x1))
		   (* -1
		      (expt -1 n)
		      (/ (- (raise (- x) n) (raise (- x1) n))
			 (- (- x) (- x1))))))
        :instructions
        ((:in-theory (disable raise raise-expt expt |(expt (- c) n)|))
         (:use (:instance differential-numer-neg-x))
         (:use (:instance differential-denom-neg-x))
         :promote :promote (:forwardchain 1)
         (:forwardchain 1)
         (:dv 1)
         (:dv 1)
         := (:drop 8)
         :up (:dv 2)
         (:dv 1)
         := (:drop 7)
         :up :up :top
         (:use (:instance (:theorem (equal (/ a (* -1 b)) (/ (* -1 a) b)))
                          (a (* (expt -1 n)
                                (+ (raise (- x) n)
                                   (- (raise (- x1) n)))))
                          (b (+ (- x) (- (- x1))))))
         (:change-goal nil t)
         :bash
         :promote (:dv 1)
         := (:drop 1)
         :top :bash)))

(local
 (defthmd derivative-neg-x
   (implies (and (realp x)
		 (< x 0)
		 (integerp n))
	    (equal (derivative-raise x n)
		   (* -1
		      (expt -1 n)
		      (derivative-raise (- x) n))))
   :hints (("Goal"
	    :use ((:instance raise-for-negative-x-integer-n (n (1- n))))
	    :in-theory (disable raise
				raise-expt
				expt
				raise-a---x
				power-of-sums
				|(expt (- c) n)|)))))

(local
 (defthm realp-raise-to-int
   (implies (and (realp x)
		 (integerp n))
	    (realp (raise x n)))))

(local
 (defthm realp-derivative-raise-to-int
   (implies (and (realp x)
		 (integerp n))
	    (realp (derivative-raise x n)))))

(local
 (defthm expt--1-n
   (implies (integerp n)
	    (or (equal (expt -1 n) 1)
		(equal (expt -1 n) -1)))
   :rule-classes nil))

(local
 (defthm abs-uminus
   (equal (abs (- x))
	  (abs (fix x)))))

(local
 (encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (realp x)
		   (< x 0)
		   (realp x1)
		   (< x1 0)
		   (integerp n))
	      (equal (- (/ (- (raise x n) (raise x1 n))
			   (- x x1))
			(derivative-raise x n))
		     (- (* -1
			   (expt -1 n)
			   (/ (- (raise (- x) n) (raise (- x1) n))
			      (- (- x) (- x1))))
			(* -1
			   (expt -1 n)
			   (derivative-raise (- x) n)))))
     :hints (("Goal"
	      :use ((:instance differential-neg-x)
		    (:instance derivative-neg-x))
	      :in-theory (disable derivative-raise
				  raise
				  raise-expt
				  expt
				  raise-a---x
				  power-of-sums
				  |(expt (- c) n)|)))))

  (local
   (defthmd lemma-2
     (implies (and (realp x)
		   (< x 0)
		   (realp x1)
		   (< x1 0)
		   (integerp n))
	      (equal (- (/ (- (raise x n) (raise x1 n))
			   (- x x1))
			(derivative-raise x n))
		     (* -1
			(expt -1 n)
			(- (/ (- (raise (- x) n) (raise (- x1) n))
			      (- (- x) (- x1)))
			   (derivative-raise (- x) n)))))
     :hints (("Goal"
	      :use ((:instance lemma-1))
	      :in-theory (disable derivative-raise
				  raise
				  raise-expt
				  expt
				  raise-a---x
				  power-of-sums
				  |(expt (- c) n)|)))))

  (local
   (defthm lemma-3
     (implies (and (realp x)
		   (realp y))
	      (equal (abs (* x y))
		     (* (abs x) (abs y))))))

  (defthmd derivative-differential-neg-x
    (implies (and (realp x)
		  (< x 0)
		  (realp x1)
		  (< x1 0)
		  (integerp n))
	     (equal (abs (- (/ (- (raise x n) (raise x1 n))
			       (- x x1))
			    (derivative-raise x n)))
		    (abs (- (/ (- (raise (- x) n) (raise (- x1) n))
			       (- (- x) (- x1)))
			    (derivative-raise (- x) n)))))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance expt--1-n)
		   (:instance (:theorem (implies (equal a b)
						 (equal (abs a) (abs b))))
			      (a (- (/ (- (raise x n) (raise x1 n))
				       (- x x1))
				    (derivative-raise x n)))
			      (b (* -1
				    (expt -1 n)
				    (- (/ (- (raise (- x) n) (raise (- x1) n))
					  (- (- x) (- x1)))
				       (derivative-raise (- x) n)))))
		   (:instance (:theorem (implies (realp a)
						 (equal (abs (* -1 (expt -1 n) a))
							(abs a))))
			      (a (- (/ (- (raise (- x) n) (raise (- x1) n))
				       (- (- x) (- x1)))
				    (derivative-raise (- x) n))))
		   )
	     :in-theory (disable derivative-raise
				 raise
				 raise-expt
				 expt
				 abs
				 raise-a---x
				 power-of-sums
				 |(expt (- c) n)|))
	    ("Subgoal 1"
	     :use ((:instance expt--1-n))
	     :in-theory (disable |(equal (expt x n) 1)|
				 |(equal (expt x n) -1)|)
	     )
	    ))))

(defun negative-domain ()
  (interval nil '(0)))

(defun-sk forall-x-eps-delta-in-range-deriv-raise-neg-x-works (x n eps delta)
 (forall (x1)
	  (implies (and (inside-interval-p x1 (negative-domain))
			(inside-interval-p x (negative-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (raise x n) (raise x1 n)) (- x x1))
			      (derivative-raise x n)))
		      eps)))
  :rewrite :direct)

(local
 (defthm inside-interval-real-domain
   (equal (inside-interval-p x (real-domain))
	  (realp x))))

(local
 (encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (realp x)
		   (realp x1)
		   (< (abs (- x x1)) delta))
	      (< (abs (- (- x) (- x1))) delta))))

  (local
   (defthm lemma-2
     (implies (and (realp x)
		   (realp y))
	      (equal (abs (* x y))
		     (* (abs x) (abs y))))))

  (local
   (defthmd lemma-3
     (implies (and (realp x)
		   (< x 0)
		   (integerp n)
		   (realp delta)
		   (< 0 delta)
		   (< delta (- x))
		   (forall-x-eps-delta-in-range-deriv-raise-works (- x) n eps delta)
		   )
	      (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta))

     :instructions
     ((:use (:instance forall-x-eps-delta-in-range-deriv-raise-works-necc
		       (x (- x))
		       (x1 (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                               x n eps delta)))))
      (:use
       (:instance
	lemma-1 (x x)
	(x1
	 (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))))
      (:use (:instance raise-for-negative-x-integer-n))
      (:use
       (:instance
	raise-for-negative-x-integer-n
	(x
	 (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))))
      (:use (:instance derivative-neg-x))
      (:in-theory (disable forall-x-eps-delta-in-range-deriv-raise-works
			   forall-x-eps-delta-in-range-deriv-raise-works-necc
			   derivative-raise raise raise-expt))
      :promote :promote
      :promote :promote :promote :x-dumb
      (:=
       (implies
	(and
	 (inside-interval-p
	  (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
	  (real-domain))
	 (inside-interval-p x (real-domain))
	 (realp delta)
	 (< 0 delta)
	 (realp eps)
	 (< 0 eps)
	 (not (equal x
		     (forall-x-eps-delta-in-range-deriv-raise-works-witness
                      x n eps delta)))
	 (< (abs (- x
		    (forall-x-eps-delta-in-range-deriv-raise-works-witness
                     x n eps delta)))
	    delta))
	(< (abs (- (/ (- (raise x n)
			 (raise (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                 x n eps delta)
				n))
		      (- x
			 (forall-x-eps-delta-in-range-deriv-raise-works-witness
                          x n eps delta)))
		   (derivative-raise x n)))
	   eps)))
      :promote (:forwardchain 1)
      (:forwardchain 1)
      (:forwardchain 1)
      (:forwardchain 1)
      (:forwardchain 1)
      (:forwardchain 20)
      (:dv 1)
      (:dv 1)
      (:dv 1)
      (:dv 1)
      (:dv 1)
      := :up (:dv 2)
      (:dv 1)
      := :up :up (:dv 2)
      (:=
       (*
	(expt -1 n)
	(-
	 (raise
	  (-
	   (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))
	  n))))
      :up
      (:= (* (expt -1 n)
	     (+ (raise (- x) n)
		(- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                              x n eps delta))
			  n)))))
      :up
      (:= (* (expt -1 n)
	     (* (+ (raise (- x) n)
		   (- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                 x n eps delta))
			     n)))
		(/ (+ x
		      (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                          x n eps delta)))))))
      :up (:dv 2)
      (:dv 1)
      := :up
      (:= (* (expt -1 n)
	     (derivative-raise (- x) n)))
      :up
      (:= (* (expt -1 n)
	     (+ (* (+ (raise (- x) n)
		      (- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                    x n eps delta))
				n)))
		   (/ (+ x
			 (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                             x n eps delta)))))
		(derivative-raise (- x) n))))
      :up (:rewrite lemma-2)
      (:dv 1)
      (:= 1)
      :up
      (:= (abs (+ (* (+ (raise (- x) n)
			(- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                      x n eps delta))
				  n)))
		     (/ (+ x
			   (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                               x n eps delta)))))
		  (derivative-raise (- x) n))))
      (:dv 1)
      (:dv 1)
      (:dv 2)
      (:dv 1)
      (:= (- (+ (- x)
		(- (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                       x n eps delta))))))
      :up
      (:claim (realp (+ (- x)
			(- (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                               x n eps delta))))))
      (:rewrite |(/ (- x))|)
      :up
      (:= (- (* (+ (raise (- x) n)
		   (- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                 x n eps delta))
			     n)))
		(/ (+ (- x)
		      (- (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                             x n eps delta))))))))
      :up (:dv 2)
      (:= (- (- (derivative-raise (- x) n))))
      :up
      (:= (- (+ (* (+ (raise (- x) n)
		      (- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                    x n eps delta))
				n)))
		   (/ (+ (- x)
			 (- (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                x n eps delta))))))
		(- (derivative-raise (- x) n)))))
      :up
      (:= (abs (+ (* (+ (raise (- x) n)
			(- (raise (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                      x n eps delta))
				  n)))
		     (/ (+ (- x)
			   (- (- (forall-x-eps-delta-in-range-deriv-raise-works-witness
                                  x n eps delta))))))
		  (- (derivative-raise (- x) n)))))
      :up
      :bash :bash)))

  (local
   (defthmd lemma-4
     (implies (and (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta)
		   (realp delta)
		   (< 0 delta)
		   (realp gamma)
		   (< 0 gamma)
		   (< gamma delta))
	      (forall-x-eps-delta-in-range-deriv-raise-works x n eps gamma))
     :hints (("Goal"
	      :use ((:instance forall-x-eps-delta-in-range-deriv-raise-works-necc
			       (x1 (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps gamma))))
	      :in-theory (disable abs)))
     ))

  (local
   (defun fix-delta (delta x)
     (if (<= delta (/ (- x) 2))
	 delta
       (/ (- x) 2))))

  (local
   (defthmd fix-delta-works
     (implies (and (realp x)
		   (< x 0)
		   (realp delta)
		   (< 0 delta))
	      (and (realp (fix-delta delta x))
		   (< 0 (fix-delta delta x))
		   (< (fix-delta delta x) (- x))
		   (<= (fix-delta delta x) delta)
		   ))))

  (local
   (defthmd lemma-5
     (implies (and (realp x)
		   (< x 0)
		   (integerp n)
		   (realp delta)
		   (< 0 delta)
		   (forall-x-eps-delta-in-range-deriv-raise-works (- x) n eps delta)
		   )
	      (forall-x-eps-delta-in-range-deriv-raise-works
	       x n eps (fix-delta delta x)))
     :hints (("Goal"
	      :use ((:instance lemma-3 (delta (fix-delta delta x)))
		    (:instance lemma-4 (x (- x)) (gamma (fix-delta delta x)))
		    (:instance fix-delta-works)
		    )
	      :in-theory (disable fix-delta
				  forall-x-eps-delta-in-range-deriv-raise-works)))))

  (defthmd raise-differentiable-for-negp-x-using-hyperreal-criterion
    (implies (and (realp x)
		  (< x 0)
		  (integerp n)
		  (realp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-raise-works x n eps))
    :hints (("Goal"
	     :use ((:instance lemma-5
			      (delta (exists-delta-for-x-and-eps-so-deriv-raise-works-witness (- x) n eps)))
		   (:instance fix-delta-works
			      (delta (exists-delta-for-x-and-eps-so-deriv-raise-works-witness (- x) n eps)))
		   (:instance exists-delta-for-x-and-eps-so-deriv-raise-works-suff
			      (delta (fix-delta
				      (exists-delta-for-x-and-eps-so-deriv-raise-works-witness (- x) n eps) x)))
		   (:instance raise-differentiable-for-posp-x-using-hyperreal-criterion
			      (x (- x))))
	     :in-theory (disable fix-delta
				 forall-x-eps-delta-in-range-deriv-raise-works))))))

(encapsulate
 nil

 (local
  (defthmd lemma-1
    (equal (raise 0 n)
	   (if (= n 0)
	       1
	     0))))

 (local
  (defthmd lemma-2
    (equal (derivative-raise 0 n)
	   (if (= n 1)
	       1
	     0))))

 (local
  (defun natural-induction (n)
    (if (zp n)
	1
      (1+ (natural-induction (1- n))))))

 (local
   (defthmd lemma-3
     (implies (and (realp x)
		   (realp y))
	      (equal (abs (* x y))
		     (* (abs x) (abs y))))))
 (local
  (defthmd lemma-4
    (implies (and (realp x)
		  (<= (abs x) 1)
		  (integerp n)
		  (<= 1 n))
	     (<= (abs (expt x n)) (abs x)))
    :INSTRUCTIONS ((:INDUCT (NATURAL-INDUCTION N))
		   (:CHANGE-GOAL NIL T)
		   :BASH :PROMOTE (:CASESPLIT (= N 1))
		   :BASH (:FORWARDCHAIN 2)
		   (:DV 1)
		   (:DV 1)
		   :X :TOP (:CASESPLIT (= X 0))
		   :BASH (:DV 1)
		   (:DV 1)
		   :S :X :X (:= (* X (EXPT X (+ -1 N))))
		   :UP (:REWRITE LEMMA-3)
		   (:DV 2)
		   :TOP
		   (:CLAIM (<= (ABS (EXPT X (+ -1 N))) 1))
		   :BASH)))

 (local
  (defthmd lemma-5
    (implies (and (realp x)
		  (<= (abs x) 1)
		  (= 0 n))
	     (equal (abs (expt x n)) 1))))


 (local
  (defthmd lemma-6
    (implies (and (= x 0)
		  (integerp n)
		  (<= 0 n)
		  (realp delta)
		  (< 0 delta)
		  (< delta 1)
		  (< delta eps))
	     (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta))
    :instructions
    (:promote
     (:=
      (implies
       (and
	(inside-interval-p

	 (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
	 (real-domain))
	(inside-interval-p x (real-domain))
	(realp delta)
	(< 0 delta)
	(realp eps)
	(< 0 eps)
	(not (equal x
		    (forall-x-eps-delta-in-range-deriv-raise-works-witness
		     x n eps delta)))
	(< (abs (- x
		   (forall-x-eps-delta-in-range-deriv-raise-works-witness
		    x n eps delta)))
	   delta))
       (< (abs (- (/ (- (raise x n)
			(raise (forall-x-eps-delta-in-range-deriv-raise-works-witness
				x n eps delta)
			       n))
		     (- x
			(forall-x-eps-delta-in-range-deriv-raise-works-witness
			 x n eps delta)))
		  (derivative-raise x n)))
	  eps)))
     :promote (:casesplit (< 1 n))
     (:change-goal nil t)
     :bash
     (:claim
      (not
       (equal
        (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
        0)))
     (:claim
      (< (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
	 delta))
     (:claim
      (<
       (abs
	(forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))
       delta))
     (:claim (equal (raise x n) 0))
     (:claim (equal (derivative-raise x n) 0))
     (:=
      (<
       (abs
	(*
	 (raise
	  (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
	  n)
	 (/ (forall-x-eps-delta-in-range-deriv-raise-works-witness
	     x n eps delta))))
       eps))
     (:dv 1)
     (:dv 1)
     (:dv 1)
     (:rewrite raise-expt)
     :up
     (:=
      (expt
       (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
       (1- n)))
     :up :top
     (:use
      (:instance
       lemma-4
       (x (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))
       (n (+ -1 n))))
     :promote (:demote 1)
     (:dv 1)
     (:dv 1)
     (:= t)
     :up
     (:=
      (<=
       (abs
	(expt
	 (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta)
	 (+ -1 n)))
       (abs
	(forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))))
     :up
     :promote :bash)))

 (local
   (defun fix-delta (eps)
     (* 1/2 (min 1 eps))))

 (local
  (defthmd fix-delta-works
    (implies (and (realp eps)
		  (< 0 eps))
	     (and (realp (fix-delta eps))
		  (< 0 (fix-delta eps))
		  (< (fix-delta eps) 1)
		  (< (fix-delta eps) eps)))))

 (defthmd raise-differentiable-for-zero-using-hyperreal-criterion
  (implies (and (= x 0)
		(integerp n)
		(<= 0 n)
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-raise-works x n eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-raise-works-suff
			    (delta (fix-delta eps)))
		 (:instance fix-delta-works)
		 (:instance lemma-6
			    (delta (fix-delta eps)))
		 )
	   )))

  )

(defthmd raise-differentiable-using-hyperreal-criterion
  (implies (and (or (and (inside-interval-p x (positive-domain))
			 (realp n))
		    (and (inside-interval-p x (negative-domain))
			 (integerp n))
		    (and (equal x 0)
			 (integerp n)
			 (<= 0 n)))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-raise-works x n eps))
  :hints (("Goal"
	   :use ((:instance raise-differentiable-for-posp-x-using-hyperreal-criterion)
		 (:instance raise-differentiable-for-negp-x-using-hyperreal-criterion)
		 (:instance raise-differentiable-for-zero-using-hyperreal-criterion))
	   :in-theory (disable exists-delta-for-x-and-eps-so-deriv-raise-works)
)))

(defun derivative-expt (x n)
  (* n (expt x (1- n))))

(defun-sk forall-x-eps-delta-in-range-deriv-expt-works (x n eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (real-domain))
			(inside-interval-p x (real-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (expt x n) (expt x1 n)) (- x x1))
			      (derivative-expt x n)))
		      eps)))
  :rewrite :direct)

(defun-sk exists-delta-for-x-and-eps-so-deriv-expt-works (x n eps)
  (exists delta
	  (implies (and (inside-interval-p x (real-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-expt-works x n eps delta)))))

(encapsulate
 nil

 (local
  (defthm lemma-1
    (implies (integerp n)
	     (equal (derivative-raise x n)
		    (derivative-expt x n)))))


 (local
  (defthmd lemma-2
    (implies (and (integerp n)
		  (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta))
	     (forall-x-eps-delta-in-range-deriv-expt-works x n eps delta))
    :hints (("Goal"
	     :use ((:instance forall-x-eps-delta-in-range-deriv-raise-works-necc
			      (x1 (forall-x-eps-delta-in-range-deriv-expt-works-witness x n eps delta))))
	     :in-theory (disable abs raise expt)
	     ))))

 (local
  (defthmd lemma-3
    (implies (and (integerp n)
		  (forall-x-eps-delta-in-range-deriv-expt-works x n eps delta))
	     (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta))
    :hints (("Goal"
	     :use ((:instance forall-x-eps-delta-in-range-deriv-expt-works-necc
			      (x1 (forall-x-eps-delta-in-range-deriv-raise-works-witness x n eps delta))))
	     :in-theory (disable abs raise expt)
	     ))))

 (local
  (defthmd lemma-4
    (implies (integerp n)
	     (equal (forall-x-eps-delta-in-range-deriv-expt-works x n eps delta)
		    (forall-x-eps-delta-in-range-deriv-raise-works x n eps delta)))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance lemma-3))
	     :in-theory (disable forall-x-eps-delta-in-range-deriv-raise-works
				 forall-x-eps-delta-in-range-deriv-expt-works)))))

 (local
  (defthmd lemma-5
    (implies (and (integerp n)
		  (exists-delta-for-x-and-eps-so-deriv-raise-works x n eps))
	     (exists-delta-for-x-and-eps-so-deriv-expt-works x n eps))
    :hints (("Goal"
	     :use ((:instance exists-delta-for-x-and-eps-so-deriv-expt-works-suff
			      (delta (exists-delta-for-x-and-eps-so-deriv-raise-works-witness x n eps)))
		   (:instance lemma-4
			      (delta (exists-delta-for-x-and-eps-so-deriv-raise-works-witness x n eps))))
	     :in-theory (disable forall-x-eps-delta-in-range-deriv-raise-works
				 forall-x-eps-delta-in-range-deriv-expt-works)))))


 (defthmd expt-differentiable-using-hyperreal-criterion
   (implies (and (integerp n)
		 (or (not (equal x 0))
		     (<= 0 n))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-expt-works x n eps))
   :hints (("Goal"
	    :use ((:instance raise-differentiable-using-hyperreal-criterion)
		  (:instance lemma-5))
	    :in-theory (e/d (inside-interval-p)
			    (forall-x-eps-delta-in-range-deriv-raise-works
			     forall-x-eps-delta-in-range-deriv-expt-works)))))
 )

