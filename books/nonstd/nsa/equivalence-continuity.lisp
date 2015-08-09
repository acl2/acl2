(in-package "ACL2")

(include-book "continuity")
(include-book "intervals")

(local (include-book "equivalence-limits"))
(include-book "continuity")


;; Part 1: The nonstd definition of continuity implies the classical definition

(defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-f (x0 eps delta)
  (forall (x)
	  (implies (and (inside-interval-p x (rcfn-domain))
			(inside-interval-p x0 (rcfn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(< (abs (- x x0)) delta)
			(not (equal x x0)))
		   (< (abs (- (rcfn x) (rcfn x0))) eps)))
  :rewrite :direct)

(defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f (x0 eps)
  (exists (delta)
	  (implies (and (inside-interval-p x0 (rcfn-domain))
			(standardp x0)
			(realp eps)
			(standardp eps)
			(< 0 eps))
		   (and (standardp delta)
			(realp delta)
			(< 0 delta)
			(forall-x-within-delta-of-x0-f-x-within-epsilon-of-f x0 eps delta))))
  :classicalp nil)

(defthmd rcfn-is-continuous-using-classical-criterion
   (implies (and (inside-interval-p x0 (rcfn-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f x0 eps))
   :hints (("Goal"
	    :by (:functional-instance rlfn-classic-has-a-limit-using-classical-criterion
				      (rlfn rcfn)
				      (rlfn-limit rcfn)
				      (rlfn-domain rcfn-domain)
				      (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-limit exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f)
				      (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-limit-witness exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f-witness)
				      (forall-x-within-delta-of-x0-f-x-within-epsilon-of-limit forall-x-within-delta-of-x0-f-x-within-epsilon-of-f)
				      (forall-x-within-delta-of-x0-f-x-within-epsilon-of-limit-witness forall-x-within-delta-of-x0-f-x-within-epsilon-of-f-witness)
				      )
	    )
	   ("Subgoal 7"
	    :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f-suff))
	    :in-theory (disable exists-standard-delta-for-x0-to-make-x-within-epsilon-of-f-suff
				abs))
	   ("Subgoal 5"
	    :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-f-necc))
	    :in-theory (disable forall-x-within-delta-of-x0-f-x-within-epsilon-of-f-necc
				abs))
	   ("Subgoal 2"
	    :use ((:instance rcfn-domain-non-trivial)))
	   )
   )


;; Part 2: The classical definition of continuity implies the nonstd definition

(encapsulate
 ((rcfn-classical (x) t)
  (rcfn-classical-domain () t))

 (local (defun rcfn-classical (x) (declare (ignore x)) 0))
 (local (defun rcfn-classical-domain () (interval nil nil)))

 (defthm intervalp-rcfn-classical-domain
     (interval-p (rcfn-classical-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm rcfn-classical-domain-real
     (implies (inside-interval-p x (rcfn-classical-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 (defthm rcfn-classical-domain-non-trivial
     (or (null (interval-left-endpoint (rcfn-classical-domain)))
	 (null (interval-right-endpoint (rcfn-classical-domain)))
	 (< (interval-left-endpoint (rcfn-classical-domain))
	    (interval-right-endpoint (rcfn-classical-domain))))
   :rule-classes nil)

 (defthm rcfn-classical-real
     (realp (rcfn-classical x))
   :rule-classes (:rewrite :type-prescription))

 (defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f (x0 eps delta)
   (forall (x)
	   (implies (and (inside-interval-p x (rcfn-classical-domain))
			 (inside-interval-p x0 (rcfn-classical-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (< (abs (- x x0)) delta)
			 (not (equal x x0)))
		    (< (abs (- (rcfn-classical x) (rcfn-classical x0))) eps)))
   :rewrite :direct)

 (defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f (x0 eps)
   (exists (delta)
	   (implies (and (inside-interval-p x0 (rcfn-classical-domain))
			 (standardp x0)
			 (realp eps)
			 (standardp eps)
			 (< 0 eps))
		    (and (standardp delta)
			 (realp delta)
			 (< 0 delta)
			 (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f x0 eps delta))))
   :classicalp nil)

 (defthmd rcfn-classic-is-continuous
   (implies (and (inside-interval-p x0 (rcfn-classical-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f x0 eps))
   :hints (("Goal"
	    :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-suff
			     (delta 1))
		  (:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f
			     (x0 x0)
			     (eps eps)
			     (delta 1)))
	    :in-theory (disable abs))))
 )

(defthm rcfn-classical-is-continuous-using-nonstandard-criterion
  (implies (and (standardp x0)
		(inside-interval-p x0 (rcfn-classical-domain))
		(i-close x x0)
		(inside-interval-p x (rcfn-classical-domain))
		(not (equal x x0)))
	   (i-close (rcfn-classical x) (rcfn-classical x0)))
  :hints (("Goal"
	   :by (:functional-instance rlfn-classical-has-a-limit-using-nonstandard-criterion
				     (rlfn-classical rcfn-classical)
				     (rlfn-classical-limit rcfn-classical)
				     (rlfn-classical-domain rcfn-classical-domain)
				     (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f)
				     (forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-limit-witness forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f-witness)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-limit-witness exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-witness)
				     )
	   )
	  ("Subgoal 7"
	   :by (:instance rcfn-classic-is-continuous))
	  ("Subgoal 5"
	   :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-suff)))
	  ("Subgoal 3"
	   :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-classical-f-necc)))
	  ("Subgoal 2"
	   :use ((:instance rcfn-classical-domain-non-trivial)))
	  ))


;; Corollaries: Show the intermediate value theorem and extreme value theorems hold
;; for the classical definition

(defun-sk exists-intermediate-point-classical (a b z)
  (exists (x)
	  (and (realp x)
	       (< a x)
	       (< x b)
	       (equal (rcfn-classical x) z))))

(defthm intermediate-value-theorem-classical-sk
    (implies (and (inside-interval-p a (rcfn-classical-domain))
		  (inside-interval-p b (rcfn-classical-domain))
		  (realp z)
		  (< a b)
		  (or (and (< (rcfn-classical a) z) (< z (rcfn-classical b)))
		      (and (< z (rcfn-classical a)) (< (rcfn-classical b) z))))
	      (exists-intermediate-point-classical a b z))
  :hints (("Goal"
	   :by (:functional-instance intermediate-value-theorem-sk
				     (rcfn rcfn-classical)
				     (rcfn-domain rcfn-classical-domain)
				     (exists-intermediate-point exists-intermediate-point-classical)
				     (exists-intermediate-point-witness exists-intermediate-point-classical-witness)))
	  ("Subgoal 3"
	   :use ((:instance rcfn-classical-is-continuous-using-nonstandard-criterion
			    (x0 x)
			    (x y))))
	  ("Subgoal 2"
	   :use ((:instance rcfn-classical-domain-non-trivial)))))

(defun-sk is-maximum-point-of-rcfn-classical (a b max)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn-classical x) (rcfn-classical max)))))

(defun-sk rcfn-classical-achieves-maximum-point (a b)
  (exists (max)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp max)
			(<= a max)
			(<= max b)
			(is-maximum-point-of-rcfn-classical a b max)))))

(defthm maximum-point-theorem-classical-sk
  (implies (and (inside-interval-p a (rcfn-classical-domain))
		(inside-interval-p b (rcfn-classical-domain))
		(< a b))
	   (rcfn-classical-achieves-maximum-point a b))
  :hints (("Goal"
	   :by (:functional-instance maximum-point-theorem-sk
				     (rcfn rcfn-classical)
				     (rcfn-domain rcfn-classical-domain)
				     (is-maximum-point is-maximum-point-of-rcfn-classical)
				     (is-maximum-point-witness is-maximum-point-of-rcfn-classical-witness)
				     (achieves-maximum-point rcfn-classical-achieves-maximum-point)
				     (achieves-maximum-point-witness rcfn-classical-achieves-maximum-point-witness)
				     )
	   )
	  ("Subgoal 4"
	   :use ((:instance rcfn-classical-achieves-maximum-point-suff)))
	  ("Subgoal 2"
	   :use ((:instance is-maximum-point-of-rcfn-classical-necc)))))


(defun-sk is-minimum-point-of-rcfn-classical (a b min)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn-classical min) (rcfn-classical x)))))

(defun-sk rcfn-classical-achieves-minimum-point (a b)
  (exists (min)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp min)
			(<= a min)
			(<= min b)
			(is-minimum-point-of-rcfn-classical a b min)))))

(defthm minimum-point-theorem-classical-sk
  (implies (and (inside-interval-p a (rcfn-classical-domain))
		(inside-interval-p b (rcfn-classical-domain))
		(< a b))
	   (rcfn-classical-achieves-minimum-point a b))
  :hints (("Goal"
	   :by (:functional-instance minimum-point-theorem-sk
				     (rcfn rcfn-classical)
				     (rcfn-domain rcfn-classical-domain)
				     (is-minimum-point is-minimum-point-of-rcfn-classical)
				     (is-minimum-point-witness is-minimum-point-of-rcfn-classical-witness)
				     (achieves-minimum-point rcfn-classical-achieves-minimum-point)
				     (achieves-minimum-point-witness rcfn-classical-achieves-minimum-point-witness)
				     )
	   )
	  ("Subgoal 4"
	   :use ((:instance rcfn-classical-achieves-minimum-point-suff)))
	  ("Subgoal 2"
	   :use ((:instance is-minimum-point-of-rcfn-classical-necc)))))


;; Part 3: The hyperreal definition of continuity implies the classical definition

(encapsulate
 ((rcfn-hyper (x) t)
  (rcfn-hyper-domain () t))

 (local (defun rcfn-hyper (x) (declare (ignore x)) 0))
 (local (defun rcfn-hyper-domain () (interval nil nil)))

 (defthm intervalp-rcfn-hyper-domain
     (interval-p (rcfn-hyper-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm rcfn-hyper-domain-real
     (implies (inside-interval-p x (rcfn-hyper-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 (defthm rcfn-hyper-domain-non-trivial
     (or (null (interval-left-endpoint (rcfn-hyper-domain)))
	 (null (interval-right-endpoint (rcfn-hyper-domain)))
	 (< (interval-left-endpoint (rcfn-hyper-domain))
	    (interval-right-endpoint (rcfn-hyper-domain))))
   :rule-classes nil)

 (defthm rcfn-hyper-real
     (realp (rcfn-hyper x))
   :rule-classes (:rewrite :type-prescription))

 (defun-sk forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f (x0 eps delta)
   (forall (x)
	   (implies (and (inside-interval-p x (rcfn-hyper-domain))
			 (inside-interval-p x0 (rcfn-hyper-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (< (abs (- x x0)) delta)
			 (not (equal x x0)))
		    (< (abs (- (rcfn-hyper x) (rcfn-hyper x0))) eps)))
   :rewrite :direct)

 (defun-sk exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f (x0 eps)
   (exists (delta)
	   (implies (and (inside-interval-p x0 (rcfn-hyper-domain))
			 ;(standardp x0)
			 (realp eps)
			 ;(standardp eps)
			 (< 0 eps))
		    (and ;(standardp delta)
			 (realp delta)
			 (< 0 delta)
			 (forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f x0 eps delta)))))

 (defthmd rcfn-hyper-is-continuous
   (implies (and (inside-interval-p x0 (rcfn-hyper-domain))
		 ;(standardp x0)
		 (realp eps)
		 ;(standardp eps)
		 (< 0 eps))
	    (exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f x0 eps))
   :hints (("Goal"
	    :use ((:instance exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-suff
			     (delta 1))
		  (:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f
			     (x0 x0)
			     (eps eps)
			     (delta 1)))
	    :in-theory (disable abs))))
 )

(defun-sk exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f (x0 eps)
   (exists (delta)
	   (implies (and (inside-interval-p x0 (rcfn-hyper-domain))
			 (standardp x0)
			 (realp eps)
			 (standardp eps)
			 (< 0 eps))
		    (and (standardp delta)
			 (realp delta)
			 (< 0 delta)
			 (forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f x0 eps delta))))
   :classicalp nil)

(defthm-std standard-exists-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness
  (implies (and (standardp x0)
		(standardp eps))
	   (standardp (EXISTS-DELTA-FOR-X0-TO-MAKE-X-WITHIN-EPSILON-OF-HYPER-F-WITNESS
		       X0 EPS))))

(defthmd rcfn-hyper-is-continuous-using-standard-criterion
   (implies (and (inside-interval-p x0 (rcfn-hyper-domain))
		 (standardp x0)
		 (realp eps)
		 (standardp eps)
		 (< 0 eps))
	    (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f x0 eps))
   :hints (("Goal"
	    :use ((:instance rcfn-hyper-is-continuous)
		  (:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-suff
			     (delta (EXISTS-DELTA-FOR-X0-TO-MAKE-X-WITHIN-EPSILON-OF-HYPER-F-WITNESS
				     X0 EPS))))
	    :in-theory (disable rcfn-hyper-is-continuous
				forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f)
	    )))

(defthm rcfn-hyper-is-continuous-using-nonstandard-criterion
  (implies (and (standardp x0)
		(inside-interval-p x0 (rcfn-hyper-domain))
		(i-close x x0)
		(inside-interval-p x (rcfn-hyper-domain))
		(not (equal x x0)))
	   (i-close (rcfn-hyper x) (rcfn-hyper x0)))
  :hints (("Goal"
	   :by (:functional-instance rcfn-classical-is-continuous-using-nonstandard-criterion
				     (rcfn-classical rcfn-hyper)
				     (rcfn-classical-domain rcfn-hyper-domain)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-witness
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F-witness
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F-witness)))
	  ("Subgoal 7"
	   :use ((:instance rcfn-hyper-is-continuous-using-standard-criterion)))
	  ("Subgoal 5"
	   :use ((:instance exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-suff)))
	  ("Subgoal 3"
	   :use ((:instance forall-x-within-delta-of-x0-f-x-within-epsilon-of-hyper-f-necc)))
	  ("Subgoal 2"
	   :use ((:instance rcfn-hyper-domain-non-trivial)))
	  ))


;; Corollaries: Show the intermediate value theorem and extreme value theorems hold
;; for the hyperreal definition

(defun-sk exists-intermediate-point-hyper (a b z)
  (exists (x)
	  (and (realp x)
	       (< a x)
	       (< x b)
	       (equal (rcfn-hyper x) z))))

(defthm intermediate-value-theorem-hyper-sk
  (implies (and (inside-interval-p a (rcfn-hyper-domain))
		(inside-interval-p b (rcfn-hyper-domain))
		(realp z)
		(< a b)
		(or (and (< (rcfn-hyper a) z) (< z (rcfn-hyper b)))
		    (and (< z (rcfn-hyper a)) (< (rcfn-hyper b) z))))
	   (exists-intermediate-point-hyper a b z))
  :hints (("Goal"
	   :by (:functional-instance intermediate-value-theorem-classical-sk
				     (rcfn-classical rcfn-hyper)
				     (rcfn-classical-domain rcfn-hyper-domain)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-witness
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F-witness
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F-witness)
				     (exists-intermediate-point-classical exists-intermediate-point-hyper)
				     (exists-intermediate-point-classical-witness exists-intermediate-point-hyper-witness)))
	  ))

(defun-sk is-maximum-point-of-rcfn-hyper (a b max)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn-hyper x) (rcfn-hyper max)))))

(defun-sk rcfn-hyper-achieves-maximum-point (a b)
  (exists (max)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp max)
			(<= a max)
			(<= max b)
			(is-maximum-point-of-rcfn-hyper a b max)))))

(defthm maximum-point-theorem-hyper-sk
  (implies (and (inside-interval-p a (rcfn-hyper-domain))
		(inside-interval-p b (rcfn-hyper-domain))
		(< a b))
	   (rcfn-hyper-achieves-maximum-point a b))
  :hints (("Goal"
	   :by (:functional-instance maximum-point-theorem-classical-sk
				     (rcfn-classical rcfn-hyper)
				     (rcfn-classical-domain rcfn-hyper-domain)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-witness
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F-witness
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F-witness)
				     (is-maximum-point-of-rcfn-classical is-maximum-point-of-rcfn-hyper)
				     (is-maximum-point-of-rcfn-classical-witness is-maximum-point-of-rcfn-hyper-witness)
				     (rcfn-classical-achieves-maximum-point rcfn-hyper-achieves-maximum-point)
				     (rcfn-classical-achieves-maximum-point-witness rcfn-hyper-achieves-maximum-point-witness)
				     ))
	  ("Subgoal 4"
	   :use ((:instance rcfn-hyper-achieves-maximum-point-suff)))
	  ("Subgoal 2"
	   :use ((:instance is-maximum-point-of-rcfn-hyper-necc)))
	  ))

(defun-sk is-minimum-point-of-rcfn-hyper (a b min)
  (forall (x)
	  (implies (and (realp x)
			(<= a x)
			(<= x b))
		   (<= (rcfn-hyper min) (rcfn-hyper x)))))

(defun-sk rcfn-hyper-achieves-minimum-point (a b)
  (exists (min)
	  (implies (and (realp a)
			(realp b)
			(<= a b))
		   (and (realp min)
			(<= a min)
			(<= min b)
			(is-minimum-point-of-rcfn-hyper a b min)))))

(defthm minimum-point-theorem-hyper-sk
  (implies (and (inside-interval-p a (rcfn-hyper-domain))
		(inside-interval-p b (rcfn-hyper-domain))
		(< a b))
	   (rcfn-hyper-achieves-minimum-point a b))
  :hints (("Goal"
	   :by (:functional-instance minimum-point-theorem-classical-sk
				     (rcfn-classical rcfn-hyper)
				     (rcfn-classical-domain rcfn-hyper-domain)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f)
				     (exists-standard-delta-for-x0-to-make-x-within-epsilon-of-classical-f-witness
				      exists-standard-delta-for-x0-to-make-x-within-epsilon-of-hyper-f-witness)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F)
				     (FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-CLASSICAL-F-witness
				      FORALL-X-WITHIN-DELTA-OF-X0-F-X-WITHIN-EPSILON-OF-hyper-F-witness)
				     (is-minimum-point-of-rcfn-classical is-minimum-point-of-rcfn-hyper)
				     (is-minimum-point-of-rcfn-classical-witness is-minimum-point-of-rcfn-hyper-witness)
				     (rcfn-classical-achieves-minimum-point rcfn-hyper-achieves-minimum-point)
				     (rcfn-classical-achieves-minimum-point-witness rcfn-hyper-achieves-minimum-point-witness)
				     ))
	  ("Subgoal 4"
	   :use ((:instance rcfn-hyper-achieves-minimum-point-suff)))
	  ("Subgoal 2"
	   :use ((:instance is-minimum-point-of-rcfn-hyper-necc)))))

