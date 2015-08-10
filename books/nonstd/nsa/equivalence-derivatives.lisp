(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "equivalence-continuity"))
(include-book "nonstd/nsa/derivatives" :dir :system)
(include-book "nonstd/nsa/intervals" :dir :system)

(add-match-free-override :once t)
(set-match-free-default :once)

;; Part 1: If rdfn is differentiable, then derivative-rdfn is the derivative.
;; This uses only nonstad notions of differentiable and derivative, but it
;; ends up with a classical derivative function.

(encapsulate
 nil

 (local
  (defthm small-close-diff
    (implies (and (acl2-numberp x)
		  (acl2-numberp x1)
		  (i-close x x1))
	     (i-small (+ (- x) x1)))
    :hints (("Goal"
	     :use ((:instance i-small-uminus
			      (x (- x x1))))
	     :in-theory (e/d (i-close)
			     (i-small-uminus))))
    ))

 (local
  (defthm standard-part-same-to-standard-is-close
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (standardp y)
		  (equal (standard-part x) y))
	     (i-close x y))
    :hints (("Goal"
	     :in-theory (enable i-close i-small)))
    ))

 (local
  (defthm-std derivative-is-standard
    (implies (standardp x)
	     (standardp (derivative-rdfn x)))))

 (local
  (defthmd derivative-rdfn-is-derivative-lemma
    (implies (and (standardp x)
		  (inside-interval-p x (rdfn-domain))
		  (inside-interval-p x1 (rdfn-domain))
		  (i-close x x1)
		  (not (= x x1))
		  )
	     (i-close (/ (- (rdfn x1) (rdfn x)) (- x1 x))
		      (derivative-rdfn x)))
    :hints (("Goal"
	     :use ((:instance differential-rdfn-close
			      (eps (- x1 x)))
		   (:instance standard-part-same-to-standard-is-close
			      (x (differential-rdfn x (- x1 x)))
			      (y (derivative-rdfn x)))
		   )
	     :in-theory (e/d (differential-rdfn-definition)
			     (standard-part-same-to-standard-is-close
			      mvt-theorem-lemma))
	     )
	    )
    ))

 (local
  (defthmd derivative-rdfn-is-derivative-lemma-2
    (equal (+ (* x (/ y))
	      (* x (/ (- y))))
	   0)))

 (local
  (defthmd derivative-rdfn-is-derivative-lemma-3
    (equal (+ (* x (/ (+ y (- z))))
	      (* x (/ (+ (- y) z))))
	   0)
    :hints (("Goal"
	     :use ((:instance derivative-rdfn-is-derivative-lemma-2
			      (y (+ y (- z)))))
	     ))
    ))

 (local
  (defthm derivative-rdfn-is-derivative-1
    (implies (and (standardp x)
		  (inside-interval-p x (rdfn-domain))
		  (inside-interval-p x1 (rdfn-domain))
		  (i-close x x1)
		  (not (= x x1)))
	     (i-close (/ (- (rdfn x1) (rdfn x)) (- x1 x))
		      (derivative-rdfn x)))
    :hints (("Goal"
	     :use ((:instance derivative-rdfn-is-derivative-lemma)
		   (:instance derivative-rdfn-is-derivative-lemma-3
			      (x (rdfn x))
			      (y x1)
			      (z x))
		   (:instance derivative-rdfn-is-derivative-lemma-3
			      (x (rdfn x1))
			      (y x1)
			      (z x)))
	     ))
    ))

 (local
  (defthm push-uminus-to-denom-diff
    (implies (acl2-numberp y)
	     (equal (- (* x (/ (+ (- y) z))))
		    (* x (/ (+ y (- z))))))
    :hints (("Goal"
	     :use ((:instance |(/ (- x))|
			      (x (- (+ (- y) z))))
		   (:instance |(* x (- y))|
			      (x x)
			      (y (/ (+ (- y) z)))))
	     :in-theory (disable |(* x (- y))|
				 |(/ (- x))|
				 |(* x (+ y z))|
				 SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
	     ))))

 (defthm derivative-rdfn-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (inside-interval-p x1 (rdfn-domain))
		 (i-close x x1)
		 (not (= x x1)))
	    (i-close (/ (- (rdfn x) (rdfn x1)) (- x x1))
		     (derivative-rdfn x)))
   :hints (("Goal"
	    :use ((:instance derivative-rdfn-is-derivative-lemma)))
	   ("Goal'''"
	    :use ((:instance push-uminus-to-denom-diff
			     (x (rdfn x))
			     (y x)
			     (z x1))
		  (:instance push-uminus-to-denom-diff
			     (x (rdfn x1))
			     (y x)
			     (z x1))
		  )
	    :in-theory (disable push-uminus-to-denom-diff)
	    )))
 )


;; Part 2: Now, we show that derivative-rdfn really is the derivative, according
;; to the classical definition of derivative


(defun-sk forall-x-eps-delta-in-range-deriv-works (x eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (rdfn-domain))
			(inside-interval-p x (rdfn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (rdfn x) (rdfn x1)) (- x x1))
			      (derivative-rdfn x)))
		      eps))))

(defun-sk exists-delta-for-x-and-eps-so-deriv-works (x eps)
  (exists delta
	  (implies (and (inside-interval-p x (rdfn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-works x eps delta)))))

(local
 (defthm small-abs
   (implies (and (realp x)
		 (i-small x)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs x) eps))
   :hints (("Goal"
	    :use ((:instance small-<-non-small
			     (x x)
			     (y eps))
		  (:instance standard-small-is-zero
			     (x eps))
		  )
	    :in-theory (disable small-<-non-small
				small-if-<-small
				i-close-small
				i-close-small-2)))
   ))


(local
 (defthm close-abs-diff
   (implies (and (realp x)
		 (realp y)
		 (i-close x y)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs (- x y)) eps))
   :hints (("Goal"
	    :use ((:instance small-<-non-small
			     (x (- x y))
			     (y eps))
		  (:instance standard-small-is-zero
			     (x eps)))
	    :expand ((i-close x y)
		     (abs eps))
	    :in-theory nil))
   ))

(local
 (defthmd rdfn-classical-derivative-step-1
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (inside-interval-p x1 (rdfn-domain))
		 (i-close x x1)
		 (not (equal x x1))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (< (abs (- (/ (- (rdfn x) (rdfn x1)) (- x x1))
		       (derivative-rdfn x)))
	       eps))
   :hints (("Goal"
	    :use ((:instance close-abs-diff
			     (x (/ (- (rdfn x) (rdfn x1)) (- x x1)))
			     (y (derivative-rdfn x)))
		  (:instance derivative-rdfn-is-derivative)
		  )
	    :in-theory (disable close-abs-diff abs derivative-rdfn-is-derivative)))))

(local
 (defthm close-if-<-abs
   (implies (and (realp x)
		 (realp y)
		 (realp delta)
		 (i-small delta)
		 (< (abs (- x y)) delta))
	    (i-close x y))
   :hints (("Goal"
	    :use ((:instance small-if-<-small
			     (x delta)
			     (y (- x y))))
	    :expand ((abs delta)
		     (i-close x y))
	    :in-theory nil))))

(local
 (defthmd rdfn-classical-derivative-step-2
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (inside-interval-p x1 (rdfn-domain))
		 (not (equal x x1))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps)
		 (realp delta)
		 (i-small delta)
		 (< (abs (- x x1))
		    delta))
	    (< (abs (- (/ (- (rdfn x) (rdfn x1)) (- x x1))
		       (derivative-rdfn x)))
	       eps))
   :hints (("Goal"
	    :use ((:instance rdfn-classical-derivative-step-1)
		  (:instance close-if-<-abs (x x) (y x1)))
	    :in-theory (disable close-if-<-abs)))))

(local
 (defthmd rdfn-classical-derivative-step-3
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-domain))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps)
		 (realp delta)
		 (i-small delta))
	    (forall-x-eps-delta-in-range-deriv-works x eps delta))
   :hints (("Goal"
	    :expand ((forall-x-eps-delta-in-range-deriv-works x eps delta))
	    :use ((:instance rdfn-classical-derivative-step-2
			     (x1 (forall-x-eps-delta-in-range-deriv-works-witness x eps delta)))
			     )
	    :in-theory (disable derivative-rdfn-definition abs)
	    ))))

(defthmd rdfn-classical-derivative-using-classical-criterion
  (implies (and (standardp x)
		(inside-interval-p x (rdfn-domain))
		(realp eps)
		(standardp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-works x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-works-suff
			    (delta (/ (i-large-integer)))
			    )
		 (:instance rdfn-classical-derivative-step-3
			    (delta (/ (i-large-integer)))))
	   :in-theory (disable inside-interval-p-squeeze
			       small-if-<-small
			       i-close-small
			       i-close-small-2)
	   )))

(defthm-std rdfn-differentiable-classical-using-hyperreal-criterion
  (implies (and (inside-interval-p x (rdfn-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-works x eps))
  :hints (("Goal'"
	   :by (:instance rdfn-classical-derivative-using-classical-criterion))))

;; Part 3: Next, we introduce a classically differentiable function, and show that it
;; also satisfies the nonstd version of differentiability

(encapsulate
 ((rdfn-classical (x) t)
  (derivative-rdfn-classical (x) t)
  (rdfn-classical-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun rdfn-classical (x) (declare (ignore x)) 1))
 (local (defun derivative-rdfn-classical (x) (declare (ignore x)) 0))
 (local (defun rdfn-classical-domain () (interval 0 1)))

 ;; The interval really is an interval

 (defthm intervalp-rdfn-classical-domain
     (interval-p (rdfn-classical-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm rdfn-classical-domain-real
     (implies (inside-interval-p x (rdfn-classical-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm rdfn-classical-domain-non-trivial
     (or (null (interval-left-endpoint (rdfn-classical-domain)))
	 (null (interval-right-endpoint (rdfn-classical-domain)))
	 (< (interval-left-endpoint (rdfn-classical-domain))
	    (interval-right-endpoint (rdfn-classical-domain))))
   :rule-classes nil)

 ;; The function returns real values (even for improper arguments).

 (defthm rdfn-classical-real
     (realp (rdfn-classical x))
     :rule-classes (:rewrite :type-prescription))

 (defthm derivative-rdfn-classical-real
     (realp (derivative-rdfn-classical x))
     :rule-classes (:rewrite :type-prescription))


 (defun-sk forall-x-eps-delta-in-range-deriv-classical-works (x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (rdfn-classical-domain))
			 (inside-interval-p x (rdfn-classical-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (rdfn-classical x) (rdfn-classical x1)) (- x x1))
			       (derivative-rdfn-classical x)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-for-x-and-eps-so-deriv-classical-works (x eps)
  (exists delta
	  (implies (and (inside-interval-p x (rdfn-classical-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-classical-works x eps delta)))))

 (defthm derivative-rdfn-classical-is-derivative
  (implies (and (inside-interval-p x (rdfn-classical-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-classical-works x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-suff
			    (delta 1))))
	  ))
 )


(local
 (defthm-std standardp-exists-delta-for-x-and-eps-so-deriv-classical-works-witness
   (implies (and (standardp x)
		 (standardp eps))
	    (standardp
	     (exists-delta-for-x-and-eps-so-deriv-classical-works-witness x eps)))))

(local
 (encapsulate
  nil

  (local
   (defthmd lemma-1
     (implies (and (forall-x-eps-delta-in-range-deriv-classical-works x eps delta)
		   (realp gamma)
		   (realp delta)
		   (< 0 gamma)
		   (< gamma delta))
	      (forall-x-eps-delta-in-range-deriv-classical-works x eps gamma))
     :hints (("Goal"
	      :use ((:instance forall-x-eps-delta-in-range-deriv-classical-works-necc
			       (x1 (forall-x-eps-delta-in-range-deriv-classical-works-witness x eps gamma))))
	      :in-theory (disable abs)))
     ))

  (defthm rdfn-classic-is-differentiable-step-1
    (implies (and (inside-interval-p x (rdfn-classical-domain))
		  (standardp x)
		  (realp eps)
		  (standardp eps)
		  (< 0 eps)
		  (i-small delta)
		  (realp delta)
		  (< 0 delta))
	     (forall-x-eps-delta-in-range-deriv-classical-works x eps delta))
    :hints (("Goal"
	     :use ((:instance derivative-rdfn-classical-is-derivative)
		   (:instance lemma-1
			      (delta (exists-delta-for-x-and-eps-so-deriv-classical-works-witness x eps))
			      (gamma delta))
		   (:instance small-<-non-small
			      (x delta)
			      (y (exists-delta-for-x-and-eps-so-deriv-classical-works-witness x eps)))
		   (:instance standard-small-is-zero
			      (x (exists-delta-for-x-and-eps-so-deriv-classical-works-witness x eps))))
	     :in-theory (disable derivative-rdfn-classical-is-derivative
				 small-<-non-small
				 forall-x-eps-delta-in-range-deriv-classical-works))))))




(local
 (defthmd rdfn-classic-is-differentiable-step-2
   (implies (and (inside-interval-p x (rdfn-classical-domain))
		 (standardp x)
		 (inside-interval-p x1 (rdfn-classical-domain))
		 (< (abs (- x1 x)) delta)
		 (not (equal x1 x))
		 (realp eps)
		 (standardp eps)
		 (< 0 eps)
		 (i-small delta)
		 (realp delta)
		 (< 0 delta))
	    (< (abs (- (/ (- (rdfn-classical x) (rdfn-classical x1)) (- x x1))
		       (derivative-rdfn-classical x)))
	       eps))
   :hints (("Goal"
	    :use ((:instance rdfn-classic-is-differentiable-step-1)
		  (:instance forall-x-eps-delta-in-range-deriv-classical-works-necc)
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
 (defthmd rdfn-classic-is-differentiable-step-3
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
 (defthm-std standard-rdfn-classical
   (implies (standardp x)
	    (standardp (rdfn-classical x)))))

(local
 (defthm-std standard-derivative-rdfn-classical
   (implies (standardp x)
	    (standardp (derivative-rdfn-classical x)))))

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

(encapsulate
 nil

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
		  (acl2-numberp x1))
	     (acl2-numberp (abs (+ (- x) x1))))))

 (local
  (defthm lemma-2
    (equal (abs (+ (- x)
		   y
		   (- z)))
	   (abs (+ x
		   (- y)
		   z)))
    ))

 (local
  (defthm lemma-3
    (implies (and (acl2-numberp x)
		  (acl2-numberp x1)
		  (<= (abs (+ (- x) x1)) 0))
	     (equal (equal x1 x) t))))

 (local
  (defthm lemma-4
    (implies (and (realp x)
		  (realp x1))
	     (realp (abs (+ (- x) x1))))))

 (defthmd rdfn-classic-is-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-classical-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (rdfn-classical-domain))
		 (not (equal x1 x)))
	    (i-close (/ (- (rdfn-classical x) (rdfn-classical x1)) (- x x1))
		     (derivative-rdfn-classical x)))
   :hints (("Goal"
	    :use ((:instance rdfn-classic-is-differentiable-step-2
			     (eps (standard-lower-bound-of-diff
				   (derivative-rdfn-classical x)
				   (/ (- (rdfn-classical x) (rdfn-classical x1)) (- x x1))))
			     (delta (* 2 (abs (- x1 x)))))
		  (:instance rdfn-classic-is-differentiable-step-3
			     (x (derivative-rdfn-classical x))
			     (y (/ (- (rdfn-classical x) (rdfn-classical x1)) (- x x1)))))
	    :in-theory (disable standard-lower-bound-of-diff
				abs))
	   ("Subgoal 1"
	    :use ((:instance close-small-abs-2x
			     (x x)
			     (y x1)))
	    :in-theory (enable abs))))
 )

(defthm rdfn-classic-is-differentiable-using-nonstd-criterion
  (implies (and (standardp x)
		(inside-interval-p x (rdfn-classical-domain))
		(inside-interval-p y1 (rdfn-classical-domain))
		(inside-interval-p y2 (rdfn-classical-domain))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2)))
	   (and (i-limited (/ (- (rdfn-classical x) (rdfn-classical y1)) (- x y1)))
		(i-close (/ (- (rdfn-classical x) (rdfn-classical y1)) (- x y1))
			 (/ (- (rdfn-classical x) (rdfn-classical y2)) (- x y2)))))
  :hints (("Goal"
	   :use ((:instance rdfn-classic-is-differentiable (x1 y1))
		 (:instance rdfn-classic-is-differentiable (x1 y2))
		 (:instance i-close-transitive
			    (x (/ (- (rdfn-classical x) (rdfn-classical y1)) (- x y1)))
			    (y (derivative-rdfn-classical x))
			    (z (/ (- (rdfn-classical x) (rdfn-classical y2)) (- x y2))))
		 (:instance i-close-limited
			    (x (derivative-rdfn-classical x))
			    (y (/ (- (rdfn-classical x) (rdfn-classical y1)) (- x y1))))
		 (:instance standard-derivative-rdfn-classical)
		 )
	   :in-theory (disable i-close-transitive
			       i-close-limited
			       standard-derivative-rdfn-classical
; Added by Matt K., 12/5/2014: The proof seemed to take very long (forever?)
; today (I don't know why), but it succeeds quickly with the following
; additional disables.  Actually only one of these needs to be disabled, but
; compared to disabling both, the proof takes about 10x longer if only the
; second is enabled and about 27x as long if only the first is enabled.
                               DIFFERENTIAL-RDFN2-LIMITED
                               CLOSE-IF-<-ABS
                               )
	   )
	  )
  )


(defun-sk exists-critical-point-for-rdfn-classical (a b)
  (exists (x)
	  (and (realp x)
	       (< a x)
	       (< x b)
	       (equal (derivative-rdfn-classical x) 0))))

(local
 (defthmd smaller-value-inside-interval
   (implies (and (weak-interval-p interval)
		 (inside-interval-p x interval)
		 (null (interval-left-endpoint interval))
		 (realp y)
		 (< y x))
	    (inside-interval-p y interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthmd bigger-value-inside-interval
   (implies (and (weak-interval-p interval)
		 (inside-interval-p x interval)
		 (null (interval-right-endpoint interval))
		 (realp y)
		 (< x y))
	    (inside-interval-p y interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthmd standard-difference-separation-1
   (implies (and (realp x)
		 (standardp x)
		 (realp y)
		 (standardp y)
		 (< x y)
		 (realp eps)
		 (i-small eps))
	    (< (+ x eps) y))
   :hints (("Goal"
	    :use ((:instance small-<-non-small
			     (x eps)
			     (y (- y x)))
		  (:instance standard-small-is-zero
			     (x (- y x)))
		  )
	    :in-theory (disable small-<-non-small
				small-if-<-small
				close-if-<-abs
				i-close-small
				i-close-small-2)))))

(local
 (defthmd standard-difference-separation-2
   (implies (and (realp x)
		 (standardp x)
		 (realp y)
		 (standardp y)
		 (< y x)
		 (realp eps)
		 (i-small eps))
	    (< y (+ x eps)))
   :hints (("Goal"
	    :use ((:instance small-<-non-small
			     (x eps)
			     (y (- y x)))
		  (:instance standard-small-is-zero
			     (x (- y x)))
		  )
	    :in-theory (disable small-<-non-small
				small-if-<-small
				close-if-<-abs
				i-close-small
				i-close-small-2)))))

(local
 (defthm contains-right-endpoint-means-right-inclusive
   (implies (and (weak-interval-p interval)
		 (inside-interval-p (interval-right-endpoint interval)
				    interval))
	    (interval-right-inclusive-p interval))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthmd smaller-value-inside-closed-interval
   (implies (and (weak-interval-p interval)
		 (inside-interval-p x interval)
		 (standardp x)
		 (standardp interval)
		 (not (null (interval-left-endpoint interval)))
		 (not (equal (interval-left-endpoint interval) x))
		 (realp eps)
		 (<= 0 eps)
		 (i-small eps))
	    (inside-interval-p (- x eps) interval))
   :hints (("Goal"
	    :expand ((INSIDE-INTERVAL-P (+ (- EPS) X)
                            INTERVAL))
	    :use ((:instance standard-difference-separation-2
			     (x x)
			     (y (interval-left-endpoint interval))
			     (eps (- eps))
			     )))
	   ("Subgoal 1"
	    :expand (i-small eps))
	   )))

(local
 (defthmd bigger-value-inside-closed-interval
   (implies (and (weak-interval-p interval)
		 (inside-interval-p x interval)
		 (standardp x)
		 (standardp interval)
		 (not (null (interval-right-endpoint interval)))
		 (not (equal (interval-right-endpoint interval) x))
		 (realp eps)
		 (<= 0 eps)
		 (i-small eps))
	    (inside-interval-p (+ x eps) interval))
   :hints (("Goal"
	    :expand ((INSIDE-INTERVAL-P (+ EPS X)
                            INTERVAL))
	    :use ((:instance standard-difference-separation-1
			     (x x)
			     (y (interval-right-endpoint interval))
			     (eps eps)
			     )
		  (:instance standard-difference-separation-2
			     (x x)
			     (y (interval-left-endpoint interval))
			     (eps eps)
			     )))
	   ("Subgoal 4"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthmd trivial-interval-is-not-empty
   (implies (and (interval-p interval)
		 (inside-interval-p x interval)
		 (equal (interval-left-endpoint interval) x)
		 (equal (interval-right-endpoint interval) x))
	    (realp (car interval)))
   :hints (("Goal"
	    :expand ((interval-p interval))
	    :cases ((equal (interval-left-endpoint interval) nil)
		    (equal (interval-right-endpoint interval) nil)
		    (and (interval-left-inclusive-p interval)
			 (interval-right-inclusive-p interval))))
	   ("Subgoal 1"
	    :in-theory (enable interval-definition-theory))
	    )))

(defthm standard+eps-inside-standard-interval
  (implies (and (interval-p interval)
		(inside-interval-p x interval)
		(standardp x)
		(standardp interval)
		(realp eps)
		(i-small eps)
		(not (inside-interval-p (+ x eps) interval))
		(not (inside-interval-p (- x eps) interval)))
	   (and (interval-left-inclusive-p interval)
		(interval-right-inclusive-p interval)
		(equal (interval-left-endpoint interval)
		       (interval-right-endpoint interval))))
  :hints (("Goal"
	   :cases ((<= 0 eps)))
	  ("Subgoal 2"
	   :use ((:instance bigger-value-inside-closed-interval
			    (x x)
			    (eps (- eps)))
		 (:instance bigger-value-inside-interval
			    (x x)
			    (y (- x eps)))
		 (:instance smaller-value-inside-closed-interval
			    (x (interval-right-endpoint interval))
			    (eps (- eps)))
		 (:instance smaller-value-inside-interval
			    (x (interval-right-endpoint interval))
			    (y (+ x eps)))
		 (:instance trivial-interval-is-not-empty)
		 )
	   :expand ((interval-left-inclusive-p interval)
		    ;(interval-left-endpoint interval)
		    (interval-right-inclusive-p interval)
		    ;(interval-right-endpoint interval)
		    )
	   )
	  ("Subgoal 1"
	   :use ((:instance bigger-value-inside-closed-interval
			    (x x)
			    (eps eps))
		 (:instance bigger-value-inside-interval
			    (x x)
			    (y (+ x eps)))
		 (:instance smaller-value-inside-closed-interval
			    (x (interval-right-endpoint interval))
			    (eps eps))
		 (:instance smaller-value-inside-interval
			    (x (interval-right-endpoint interval))
			    (y (- x eps)))
		 (:instance trivial-interval-is-not-empty)
		 )
	   :expand ((interval-left-inclusive-p interval)
		    ;(interval-left-endpoint interval)
		    (interval-right-inclusive-p interval)
		    ;(interval-right-endpoint interval)
		    ))
	  )
  :rule-classes nil)

(local
 (defthm-std standard-rdfn-classical-domain
   (standardp (rdfn-classical-domain))))

(local
 (defthm standard+eps-inside-rdfn-classical-domain
   (implies (and (inside-interval-p x (rdfn-classical-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps))
	    (or (inside-interval-p (+ x eps) (rdfn-classical-domain))
		(inside-interval-p (- x eps) (rdfn-classical-domain))))
   :hints (("Goal"
	    :use ((:instance standard+eps-inside-standard-interval
			     (interval (rdfn-classical-domain)))
		  (:instance rdfn-classical-domain-non-trivial))))
   :rule-classes nil))

(defthm rolles-theorem-sk-for-rdfn-classical
  (implies (and (inside-interval-p a (rdfn-classical-domain))
		(inside-interval-p b (rdfn-classical-domain))
		(= (rdfn-classical a) (rdfn-classical b))
		(< a b))
	   (exists-critical-point-for-rdfn-classical a b))
  :hints (("Goal"
	   :by (:functional-instance rolles-theorem-sk
				     (rdfn rdfn-classical)
				     (rdfn-domain rdfn-classical-domain)
				     (exists-critical-point exists-critical-point-for-rdfn-classical)
				     (exists-critical-point-witness exists-critical-point-for-rdfn-classical-witness)
				     (differential-rdfn
				      (lambda (x eps)
					(/ (- (rdfn-classical (+ x eps))
					      (rdfn-classical x))
					   eps)))
				     (derivative-rdfn derivative-rdfn-classical)))
	  ("Subgoal 4"
	   :use ((:instance rdfn-classic-is-differentiable
			    (x x)
			    (x1 (+ x (/ (i-large-integer)))))
		 (:instance rdfn-classic-is-differentiable
			    (x x)
			    (x1 (- x (/ (i-large-integer)))))
		 (:instance standard+eps-inside-rdfn-classical-domain
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance i-close-to-small-sum
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance close-x-y->same-standard-part
			    (x (derivative-rdfn-classical x))
			    (y (+ (- (* (i-large-integer)
					(rdfn-classical x)))
				  (* (i-large-integer)
				     (rdfn-classical (+ (/ (i-large-integer)) x))))))
		 (:instance close-x-y->same-standard-part
			    (x (derivative-rdfn-classical x))
			    (y (+ (* (i-large-integer) (rdfn-classical x))
				  (- (* (i-large-integer)
					(rdfn-classical (+ (- (/ (i-large-integer))) x)))))))
		 (:instance standard-derivative-rdfn-classical)
		 )
	   :in-theory (disable i-close-to-small-sum
			       standard-part-of-plus
			       standard-part-of-uminus
			       close-x-y->same-standard-part
			       standard-derivative-rdfn-classical)
	   )
	  ("Subgoal 3"
	   :use ((:instance rdfn-classic-is-differentiable-using-nonstd-criterion)))
	  ("Subgoal 2"
	   :use ((:instance rdfn-classical-domain-non-trivial)))
	  ))

(encapsulate
 ((rdfn-classical-subdomain () t))

 (local
  (defun rdfn-classical-subdomain ()
    (let ((left (interval-left-endpoint (rdfn-classical-domain)))
	  (right (interval-right-endpoint (rdfn-classical-domain))))
      (if (null left)
	  (if (null right)
	      (interval 0 1)
	      (interval (- right 2) (- right 1)))
	  (if (null right)
	      (interval (+ left 1) (+ left 2))
	      (interval (+ left (* 1/3 (- right left)))
			(+ left (* 2/3 (- right left)))))))))

 (defthm rdfn-classical-subdomain-is-subdomain
     (subinterval-p (rdfn-classical-subdomain) (rdfn-classical-domain))
   :hints (("Goal"
	    :use ((:instance interval-p (interval (rdfn-classical-domain))))
	    :in-theory (enable interval-definition-theory))
	   ))

 (defthm rdfn-classical-subdomain-closed-bounded
     (and (interval-left-inclusive-p (rdfn-classical-subdomain))
	  (interval-right-inclusive-p (rdfn-classical-subdomain))))

 (defthm rdfn-classical-subdomain-real-left
     (realp (interval-left-endpoint (rdfn-classical-subdomain)))
   :rule-classes (:rewrite :type-prescription))

 (defthm rdfn-classical-subdomain-real-right
     (realp (interval-right-endpoint (rdfn-classical-subdomain)))
   :rule-classes (:rewrite :type-prescription))

 (defthm rdfn-classical-subdomain-non-trivial
     (< (interval-left-endpoint (rdfn-classical-subdomain))
	(interval-right-endpoint (rdfn-classical-subdomain)))
   :hints (("Goal"
	    :use (:instance rdfn-classical-domain-non-trivial)))
   )
 )

(defun-sk exists-mvt-point-for-rdfn-classical ()
  (exists (x)
	  (and (inside-interval-p x (rdfn-classical-subdomain))
	       (not (equal x (interval-left-endpoint (rdfn-classical-subdomain))))
	       (not (equal x (interval-right-endpoint (rdfn-classical-subdomain))))
	       (equal (derivative-rdfn-classical x)
		      (/ (- (rdfn-classical (interval-right-endpoint (rdfn-classical-subdomain)))
			    (rdfn-classical (interval-left-endpoint (rdfn-classical-subdomain))))
			 (- (interval-right-endpoint (rdfn-classical-subdomain))
			    (interval-left-endpoint (rdfn-classical-subdomain))))))))

(defthm mvt-theorem-sk-for-rdfn-classical
    (exists-mvt-point-for-rdfn-classical)
    :hints (("Goal"
	     :by (:functional-instance mvt-theorem-sk
				       (rdfn rdfn-classical)
				       (rdfn-domain rdfn-classical-domain)
				       (rdfn-subdomain rdfn-classical-subdomain)
				       (exists-mvt-point exists-mvt-point-for-rdfn-classical)
				       (exists-mvt-point-witness exists-mvt-point-for-rdfn-classical-witness)
				       (differential-rdfn
					(lambda (x eps)
					  (/ (- (rdfn-classical (+ x eps))
						(rdfn-classical x))
					     eps)))
				       (derivative-rdfn derivative-rdfn-classical)))
	    ("Subgoal 2"
	     :use ((:instance exists-mvt-point-for-rdfn-classical-suff)))
	    ))

(defthm rdfn-classical-continuous-nonstd-version
   (implies (and (standardp x)
		 (inside-interval-p x (rdfn-classical-domain))
		 (i-close x y)
		 (inside-interval-p y (rdfn-classical-domain)))
	    (i-close (rdfn-classical x) (rdfn-classical y)))
   :hints (("Goal"
	    :by (:functional-instance rdfn-continuous
				      (rdfn rdfn-classical)
				      (rdfn-domain rdfn-classical-domain)
				      (rdfn-subdomain rdfn-classical-subdomain)
				      (exists-mvt-point exists-mvt-point-for-rdfn-classical)
				      (exists-mvt-point-witness exists-mvt-point-for-rdfn-classical-witness)
				      (differential-rdfn
				       (lambda (x eps)
					 (/ (- (rdfn-classical (+ x eps))
					       (rdfn-classical x))
					    eps)))
				      (derivative-rdfn derivative-rdfn-classical)))))

(defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn (x0 eps delta)
  (forall (x)
	  (implies (and (inside-interval-p x (rdfn-classical-domain))
			(inside-interval-p x0 (rdfn-classical-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(< (abs (- x x0)) delta)
			(not (equal x x0)))
		   (< (abs (- (rdfn-classical x) (rdfn-classical x0))) eps)))
  :rewrite :direct)

 (defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn (x0 eps)
   (exists (delta)
	   (implies (and (inside-interval-p x0 (rdfn-classical-domain))
			 (standardp x0)
			 (realp eps)
			 (standardp eps)
			 (< 0 eps))
		    (and (standardp delta)
			 (realp delta)
			 (< 0 delta)
			 (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn x0 eps delta))))
   :classicalp nil)

(defun-sk exists-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn (x0 eps)
  (exists (delta)
	  (implies (and (inside-interval-p x0 (rdfn-classical-domain))
			(realp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn x0 eps delta)))))

(defthmd rdfn-classic-is-continuous-classically
  (implies (and (inside-interval-p x0 (rdfn-classical-domain))
		(standardp x0)
		(realp eps)
		(standardp eps)
		(< 0 eps))
	   (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn x0 eps))
  :hints (("Goal"
	   :by (:functional-instance rcfn-is-continuous-using-classical-criterion
				     (rcfn rdfn-classical)
				     (rcfn-domain rdfn-classical-domain)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f-witness
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn-witness)
				     (forall-x-within-delta-of-x0-f-x-within-epsilon-of-f
				      forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn)
				     (forall-x-within-delta-of-x0-f-x-within-epsilon-of-f-witness
				      forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn-witness)
				     ))
	  ("Subgoal 7"
	   :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn-suff)))
	  ("Subgoal 5"
	   :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn-necc)))
	  ("Subgoal 2"
	   :use (:instance rdfn-classical-domain-non-trivial))
	  ))

(defthm-std rdfn-classic-is-continuous-hyperreals
  (implies (and (inside-interval-p x0 (rdfn-classical-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn x0 eps))
  :hints (("Goal"
	   :use ((:instance rdfn-classic-is-continuous-classically)
		 (:instance exists-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn-suff
			    (delta (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-rdfn-witness x0 eps))))
	   :in-theory (disable forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-rdfn)
	   )))
