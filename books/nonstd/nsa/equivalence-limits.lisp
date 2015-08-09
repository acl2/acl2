(in-package "ACL2")

(include-book "nsa")
(include-book "intervals")

(local (include-book "arithmetic-5/top" :dir :system))

;; Non-classical definition of limits

(encapsulate
 ((rlfn (x) t)
  (rlfn-limit (x) t)
  (rlfn-domain () t))

 (local (defun rlfn (x) (realfix x)))
 (local (defun rlfn-limit (x) (realfix x)))
 (local (defun rlfn-domain () (interval nil nil)))

 (defthm intervalp-rlfn-domain
     (interval-p (rlfn-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm rlfn-domain-real
     (implies (inside-interval-p x (rlfn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 (defthm rlfn-domain-non-trivial
     (or (null (interval-left-endpoint (rlfn-domain)))
	 (null (interval-right-endpoint (rlfn-domain)))
	 (< (interval-left-endpoint (rlfn-domain))
	    (interval-right-endpoint (rlfn-domain))))
   :rule-classes nil)

 (defthm rlfn-real
     (realp (rlfn x))
   :rule-classes (:rewrite :type-prescription))

 (defthm rlfn-limit-real
     (realp (rlfn-limit x))
   :rule-classes (:rewrite :type-prescription))

 (defthm rlfn-has-a-limit
   (implies (and (standardp x0)
		 (inside-interval-p x0 (rlfn-domain))
		 (i-close x x0)
		 (inside-interval-p x (rlfn-domain))
		 (not (equal x x0)))
	    (i-close (rlfn x) (rlfn-limit x0))))
 )

;; Now we show that this function also obeys the classical definition of limits

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

(local
 (defthmd rlfn-has-classic-limits-step-1
   (implies (and (inside-interval-p x (rlfn-domain))
		 (inside-interval-p x0 (rlfn-domain))
		 (standardp x0)
		 (i-close x x0)
		 (not (equal x x0))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs (- (rlfn x) (rlfn-limit x0))) eps))
   :hints (("Goal"
	    :use ((:instance rlfn-has-a-limit)
		  (:instance close-<-abs-small-eps
			     (x (rlfn x))
			     (y (rlfn-limit x0))
			     (eps eps))
		  )
	    :in-theory (disable rlfn-has-a-limit
				abs)
	    )
	   )))

(local
 (defthmd rlfn-has-classic-limits-step-2
   (implies (and (inside-interval-p x (rlfn-domain))
		 (inside-interval-p x0 (rlfn-domain))
		 (standardp x0)
		 (realp delta)
		 (i-small delta)
		 (< (abs (- x x0)) delta)
		 (not (equal x x0))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs (- (rlfn x) (rlfn-limit x0))) eps))
   :hints (("Goal"
	    :use ((:instance rlfn-has-classic-limits-step-1)
		  (:instance small-if-<-small
			     (x delta)
			     (y (abs (- x x0)))))
	    :in-theory (e/d (i-close)
			    (small-if-<-small))))))

(defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-limit (x0 eps delta)
  (forall (x)
	  (implies (and (inside-interval-p x (rlfn-domain))
			(inside-interval-p x0 (rlfn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(< (abs (- x x0)) delta)
			(not (equal x x0)))
		   (< (abs (- (rlfn x) (rlfn-limit x0))) eps)))
  :rewrite :direct)

(defun-sk exists-delta-for-x0-to-make-x-within-epsilon-of-limit (x0 eps)
  (exists (delta)
	  (implies (and (inside-interval-p x0 (rlfn-domain))
			(realp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-within-delta-of-x0-f-x-within-epsilon-of-limit x0 eps delta)))))

(local
 (defthmd rlfn-has-classic-limits-step-3
   (implies (and (inside-interval-p x0 (rlfn-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-delta-for-x0-to-make-x-within-epsilon-of-limit x0 eps))
   :hints (("Goal"
	    :use ((:instance rlfn-has-classic-limits-step-2
			     (x (forall-x-within-delta-of-x0-f-x-within-epsilon-of-limit-witness x0 eps (/ (i-large-integer))))
			     (delta (/ (i-large-integer))))
		  (:instance exists-delta-for-x0-to-make-x-within-epsilon-of-limit-suff
			     (delta (/ (i-large-integer)))))
	    ))))

(local
 (defthm-std rlfn-has-classic-limits-step-4
   (implies (and (standardp x0)
		 (standardp eps))
	    (standardp (exists-delta-for-x0-to-make-x-within-epsilon-of-limit-witness x0 eps)))))

(defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-limit (x0 eps)
  (exists (delta)
	  (implies (and (inside-interval-p x0 (rlfn-domain))
			(standardp x0)
			(realp eps)
			(standardp eps)
			(< 0 eps))
		   (and (standardp delta)
			(realp delta)
			(< 0 delta)
			(forall-x-within-delta-of-x0-f-x-within-epsilon-of-limit x0 eps delta))))
  :classicalp nil)

(defthmd rlfn-classic-has-a-limit-using-classical-criterion
   (implies (and (inside-interval-p x0 (rlfn-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-limit x0 eps))
   :hints (("Goal"
	    :use ((:instance rlfn-has-classic-limits-step-3)
		  (:instance rlfn-has-classic-limits-step-4)
		  (:instance exists-delta-for-x0-to-make-x-within-epsilon-of-limit)
		  (:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-limit-suff
			     (delta (exists-delta-for-x0-to-make-x-within-epsilon-of-limit-witness x0 eps))))
	    )))

;; Classical definition of limits

(encapsulate
 ((rlfn-classical (x) t)
  (rlfn-classical-limit (x) t)
  (rlfn-classical-domain () t))

 (local (defun rlfn-classical (x) (declare (ignore x)) 0))
 (local (defun rlfn-classical-limit (x) (declare (ignore x)) 0))
 (local (defun rlfn-classical-domain () (interval nil nil)))

 (defthm intervalp-rlfn-classical-domain
     (interval-p (rlfn-classical-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm rlfn-classical-domain-real
     (implies (inside-interval-p x (rlfn-classical-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 (defthm rlfn-classical-domain-non-trivial
     (or (null (interval-left-endpoint (rlfn-classical-domain)))
	 (null (interval-right-endpoint (rlfn-classical-domain)))
	 (< (interval-left-endpoint (rlfn-classical-domain))
	    (interval-right-endpoint (rlfn-classical-domain))))
   :rule-classes nil)

 (defthm rlfn-classical-real
     (realp (rlfn-classical x))
   :rule-classes (:rewrite :type-prescription))

 (defthm rlfn-classical-limit-real
     (realp (rlfn-classical-limit x))
   :rule-classes (:rewrite :type-prescription))

 (defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit (x0 eps delta)
   (forall (x)
	   (implies (and (inside-interval-p x (rlfn-classical-domain))
			 (inside-interval-p x0 (rlfn-classical-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (< (abs (- x x0)) delta)
			 (not (equal x x0)))
		    (< (abs (- (rlfn-classical x) (rlfn-classical-limit x0))) eps)))
   :rewrite :direct)

 (defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit (x0 eps)
   (exists (delta)
	  (implies (and (inside-interval-p x0 (rlfn-classical-domain))
			(standardp x0)
			(realp eps)
			(standardp eps)
			(< 0 eps))
		   (and (standardp delta)
			(realp delta)
			(< 0 delta)
			(forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit x0 eps delta))))
   :classicalp nil)

 (defthmd rlfn-classic-has-a-limit
   (implies (and (inside-interval-p x0 (rlfn-classical-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit x0 eps))
   :hints (("Goal"
	    :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit-suff
			     (delta 1))
		  (:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit
			     (x0 x0)
			     (eps eps)
			     (delta 1)))
	    :in-theory (disable abs))))
 )

(local
 (encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit x0 eps delta)
		   (realp delta)
		   (realp gamma)
		   (< 0 gamma)
		   (< gamma delta))
	      (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit x0 eps gamma))
     :hints (("Goal"
	      :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit-necc
			       (x (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit-witness x0 eps gamma))))
	      :in-theory (disable abs)))
     ))

  (defthm rlfn-classic-has-limits-step-1
    (implies (and (inside-interval-p x0 (rlfn-classical-domain))
		  (standardp x0)
		  (realp eps)
		  (standardp eps)
		  (< 0 eps)
		  (i-small delta)
		  (realp delta)
		  (< 0 delta))
	     (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit x0 eps delta))
    :hints (("Goal"
	     :use ((:instance rlfn-classic-has-a-limit)
		   (:instance lemma-1
			      (delta (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit-witness x0 eps))
			      (gamma delta))
		   (:instance small-<-non-small
			      (x delta)
			      (y (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit-witness x0 eps)))
		   (:instance standard-small-is-zero
			      (x (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit-witness x0 eps))))
	     :in-theory (disable rlfn-classic-has-a-limit
				 small-<-non-small))))))

(local
 (defthmd rlfn-classic-has-limits-step-2
   (implies (and (inside-interval-p x0 (rlfn-classical-domain))
		 (standardp x0)
		 (inside-interval-p x (rlfn-classical-domain))
		 (< (abs (- x x0)) delta)
		 (not (equal x x0))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps)
		 (i-small delta)
		 (realp delta)
		 (< 0 delta))
	    (< (abs (- (rlfn-classical x) (rlfn-classical-limit x0))) eps))
   :hints (("Goal"
	    :use ((:instance rlfn-classic-has-limits-step-1)
		  (:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit-necc)
		  )))))

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
 (defthmd rlfn-classic-has-limits-step-3
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
 (defthm-std standard-rlfn-classical
   (implies (standardp x)
	    (standardp (rlfn-classical x)))))

(local
 (defthm-std standard-rlfn-classical-limit
   (implies (standardp x)
	    (standardp (rlfn-classical-limit x)))))

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

(defthm rlfn-classical-has-a-limit-using-nonstandard-criterion
  (implies (and (standardp x0)
		(inside-interval-p x0 (rlfn-classical-domain))
		(i-close x x0)
		(inside-interval-p x (rlfn-classical-domain))
		(not (equal x x0)))
	   (i-close (rlfn-classical x) (rlfn-classical-limit x0)))
  :hints (("Goal"
	   :use ((:instance rlfn-classic-has-limits-step-2
			    (eps (standard-lower-bound-of-diff (rlfn-classical-limit x0)
							       (rlfn-classical x)))
			    (delta (* 2 (abs (- x x0)))))
		 (:instance rlfn-classic-has-limits-step-3
			    (x (rlfn-classical-limit x0))
			    (y (rlfn-classical x))))
	   :in-theory (disable standard-lower-bound-of-diff
			       abs))
	  ("Subgoal 5"
	   :in-theory (enable abs))
	  ("Subgoal 4"
	   :in-theory (enable abs))
	  ("Subgoal 3"
	   :in-theory (enable abs))
	  ("Subgoal 2"
	   :use ((:instance close-small-abs-2x
			    (x x0)
			    (y x))))
	  ("Subgoal 1"
	   :in-theory (enable abs))))


