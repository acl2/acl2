(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/derivatives" :dir :system))
(local (include-book "nonstd/nsa/derivatives-composition" :dir :system))
(local (include-book "nonstd/nsa/chain-rule" :dir :system))
(include-book "nonstd/nsa/equivalence-derivatives" :dir :system)
(include-book "nonstd/nsa/intervals" :dir :system)

(add-match-free-override :once t)
(set-match-free-default :once)

(encapsulate
 ((dcc-fn1 (context1 x) t)
  (derivative-dcc-fn1 (context1 x) t)
  (dcc-fn2 (context2 x) t)
  (derivative-dcc-fn2 (context2 x) t)
  (dcc-fnz (contextz x) t)
  (derivative-dcc-fnz (contextz x) t)
  (dcc-fn-domain () t))

 ;; Our witness continuous function is the identity function.

 (local (defun dcc-fn1 (context1 x) (declare (ignore context1 x)) 1))
 (local (defun derivative-dcc-fn1 (context1 x) (declare (ignore context1 x)) 0))
 (local (defun dcc-fn2 (context2 x) (declare (ignore context2 x)) 1))
 (local (defun derivative-dcc-fn2 (context2 x) (declare (ignore context2 x)) 0))
 (local (defun dcc-fnz (contextz x) (declare (ignore contextz x)) 1))
 (local (defun derivative-dcc-fnz (contextz x) (declare (ignore contextz x)) 0))
 (local (defun dcc-fn-domain () (interval 0 1)))

 ;; The interval really is an interval

 (defthm intervalp-dcc-fn-domain
     (interval-p (dcc-fn-domain))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm dcc-fn-domain-real
     (implies (inside-interval-p x (dcc-fn-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm dcc-fn-domain-non-trivial
     (or (null (interval-left-endpoint (dcc-fn-domain)))
	 (null (interval-right-endpoint (dcc-fn-domain)))
	 (< (interval-left-endpoint (dcc-fn-domain))
	    (interval-right-endpoint (dcc-fn-domain))))
   :rule-classes nil)

 ;; The function returns real values (even for improper arguments).

 (defthm dcc-fn1-real
   (realp (dcc-fn1 context1 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm dcc-fn2-real
   (realp (dcc-fn2 context2 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm dcc-fnz-real
   (realp (dcc-fnz contextz x))
   :rule-classes (:rewrite :type-prescription))

 (defthm dcc-fnz-non-zero
   (implies (inside-interval-p x (dcc-fn-domain))
	    (not (equal (dcc-fnz contextz x) 0)))
   :rule-classes (:rewrite :type-prescription))

 (defthm derivative-dcc-fn1-real
     (realp (derivative-dcc-fn1 context1 x))
     :rule-classes (:rewrite :type-prescription))

 (defthm derivative-dcc-fn2-real
     (realp (derivative-dcc-fn2 context2 x))
     :rule-classes (:rewrite :type-prescription))

 (defthm derivative-dcc-fnz-real
     (realp (derivative-dcc-fnz contextz x))
     :rule-classes (:rewrite :type-prescription))

 (defun-sk forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1 (context1 x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (dcc-fn-domain))
			 (inside-interval-p x (dcc-fn-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (dcc-fn1 context1 x)
                                     (dcc-fn1 context1 x1))
                                  (- x x1))
			       (derivative-dcc-fn1 context1 x)))
		       eps)))
   :rewrite :direct)

 (defun-sk forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2 (context2 x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (dcc-fn-domain))
			 (inside-interval-p x (dcc-fn-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (dcc-fn2 context2 x)
                                     (dcc-fn2 context2 x1))
                                  (- x x1))
			       (derivative-dcc-fn2 context2 x)))
		       eps)))
   :rewrite :direct)

 (defun-sk forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz (contextz x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (dcc-fn-domain))
			 (inside-interval-p x (dcc-fn-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (dcc-fnz contextz x)
                                     (dcc-fnz contextz x1))
                                  (- x x1))
			       (derivative-dcc-fnz contextz x)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1 (context1 x eps)
  (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1 context1 x eps delta)))))

 (defun-sk exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2 (context2 x eps)
  (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2 context2 x eps delta)))))

 (defun-sk exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz (contextz x eps)
   (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz contextz x eps delta)))))

 (defthm derivative-dcc-fn1-is-derivative
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1 context1 x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1-suff
			    (delta 1))))))

 (defthm derivative-dcc-fn2-is-derivative
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2 context2 x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2-suff
			    (delta 1))))))

  (defthm derivative-dcc-fnz-is-derivative
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (realp eps)
		 (< 0 eps))
	    (exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz contextz x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz-suff
			    (delta 1))))))

 )

(defthm dcc-fn1-differentiable-using-nonstd-criterion
    (implies (and (standardp x)
                  (standardp context1)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited (/ (- (dcc-fn1 context1 x)
                                   (dcc-fn1 context1 y1))
                                (- x y1)))
		  (i-close (/ (- (dcc-fn1 context1 x)
                                 (dcc-fn1 context1 y1))
                              (- x y1))
			   (/ (- (dcc-fn1 context1 x)
                                 (dcc-fn1 context1 y2))
                              (- x y2)))))
   :hints (("Goal"
	    :by (:instance
                 (:functional-instance rdfn-classic-is-differentiable-using-nonstd-criterion
				       (rdfn-classical dcc-fn1)
				       (derivative-rdfn-classical derivative-dcc-fn1)
				       (rdfn-classical-domain dcc-fn-domain)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works
				        exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				        exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1-witness)
				       (forall-x-eps-delta-in-range-deriv-classical-works
				        forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1)
				       (forall-x-eps-delta-in-range-deriv-classical-works-witness
				        forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1-witness)
				       )
                 (context context1)))
	   ("Subgoal 5"
	    :cases ((and (inside-interval-p x (dcc-fn-domain))
			 (realp eps)
			 (< 0 eps)))
	    :expand ((exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1 context1 x eps))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1))
	   ("Subgoal 3"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1-necc
                             (context1 context))))
	   ("Subgoal 2"
	    :use ((:instance dcc-fn-domain-non-trivial)))
	   )
   )

(defthm dcc-fn2-differentiable-using-nonstd-criterion
    (implies (and (standardp x)
                  (standardp context2)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited (/ (- (dcc-fn2 context2 x)
                                   (dcc-fn2 context2 y1))
                                (- x y1)))
		  (i-close (/ (- (dcc-fn2 context2 x)
                                 (dcc-fn2 context2 y1))
                              (- x y1))
			   (/ (- (dcc-fn2 context2 x)
                                 (dcc-fn2 context2 y2))
                              (- x y2)))))
   :hints (("Goal"
	    :by (:instance
                 (:functional-instance rdfn-classic-is-differentiable-using-nonstd-criterion
				       (rdfn-classical dcc-fn2)
				       (derivative-rdfn-classical derivative-dcc-fn2)
				       (rdfn-classical-domain dcc-fn-domain)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works
				        exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				        exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2-witness)
				       (forall-x-eps-delta-in-range-deriv-classical-works
				        forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2)
				       (forall-x-eps-delta-in-range-deriv-classical-works-witness
				        forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2-witness)
				       )
                 (context context2)))
	   ("Subgoal 5"
	    :cases ((and (inside-interval-p x (dcc-fn-domain))
			 (realp eps)
			 (< 0 eps)))
	    :expand ((exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2 context2 x eps))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2))
	   ("Subgoal 3"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2-necc
                   (context2 context))))
	   ("Subgoal 2"
	    :use ((:instance dcc-fn-domain-non-trivial)))
	   )
   )


(defthm dcc-fnz-differentiable-using-nonstd-criterion
    (implies (and (standardp x)
                  (standardp contextz)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited (/ (- (dcc-fnz contextz x)
                                   (dcc-fnz contextz y1))
                                (- x y1)))
		  (i-close (/ (- (dcc-fnz contextz x)
                                 (dcc-fnz contextz y1))
                              (- x y1))
			   (/ (- (dcc-fnz contextz x)
                                 (dcc-fnz contextz y2))
                              (- x y2)))))
   :hints (("Goal"
	    :by (:instance
                 (:functional-instance rdfn-classic-is-differentiable-using-nonstd-criterion
				       (rdfn-classical dcc-fnz)
				       (derivative-rdfn-classical derivative-dcc-fnz)
				       (rdfn-classical-domain dcc-fn-domain)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works
				        exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz)
				       (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				        exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz-witness)
				       (forall-x-eps-delta-in-range-deriv-classical-works
				        forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz)
				       (forall-x-eps-delta-in-range-deriv-classical-works-witness
				        forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz-witness)
				       )
                 (context contextz)))
	   ("Subgoal 5"
	    :cases ((and (inside-interval-p x (dcc-fn-domain))
			 (realp eps)
			 (< 0 eps)))
	    :expand ((exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz contextz x eps))
	    :in-theory (disable forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz))
	   ("Subgoal 3"
	    :use ((:instance forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz-necc
                   (contextz  context))))
	   ("Subgoal 2"
	    :use ((:instance dcc-fn-domain-non-trivial)))
	   )
   )

(defthmd dcc-fn1-is-differentiable
    (implies (and (standardp x)
                  (standardp context1)
		  (Inside-interval-p x (dcc-fn-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (dcc-fn-domain))
		  (not (equal x1 x)))
	     (i-close (/ (- (dcc-fn1 context1 x)
                            (dcc-fn1 context1 x1))
                         (- x x1))
		      (derivative-dcc-fn1 context1 x)))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable
				     (rdfn-classical dcc-fn1)
				     (derivative-rdfn-classical derivative-dcc-fn1)
				     (rdfn-classical-domain dcc-fn-domain)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn1-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works
				       forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1)
				      (forall-x-eps-delta-in-range-deriv-classical-works-witness
				       forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn1-witness)
				      ))
	  ))

(defthmd dcc-fn2-is-differentiable
    (implies (and (standardp x)
                  (standardp context2)
		  (inside-interval-p x (dcc-fn-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (dcc-fn-domain))
		  (not (equal x1 x)))
	     (i-close (/ (- (dcc-fn2 context2 x)
                            (dcc-fn2 context2 x1))
                         (- x x1))
		      (derivative-dcc-fn2 context2 x)))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable
				     (rdfn-classical dcc-fn2)
				     (derivative-rdfn-classical derivative-dcc-fn2)
				     (rdfn-classical-domain dcc-fn-domain)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fn2-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works
				       forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2)
				      (forall-x-eps-delta-in-range-deriv-classical-works-witness
				       forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fn2-witness)
				      ))
	  ))

(defthmd dcc-fnz-is-differentiable
    (implies (and (standardp x)
                  (standardp contextz)
		  (inside-interval-p x (dcc-fn-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (dcc-fn-domain))
		  (not (equal x1 x)))
	     (i-close (/ (- (dcc-fnz contextz x)
                            (dcc-fnz contextz x1))
                         (- x x1))
		      (derivative-dcc-fnz contextz x)))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable
				     (rdfn-classical dcc-fnz)
				     (derivative-rdfn-classical derivative-dcc-fnz)
				     (rdfn-classical-domain dcc-fn-domain)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-dcc-fnz-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works
				       forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz)
				      (forall-x-eps-delta-in-range-deriv-classical-works-witness
				       forall-x-eps-delta-in-range-deriv-classical-works-for-dcc-fnz-witness)
				      ))
	  ))

(local
 (defthm-std standard-dcc-fn-domain
   (standardp (dcc-fn-domain))))

(local
 (defthm standard+eps-inside-dcc-fn-domain
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps))
	    (or (inside-interval-p (+ x eps) (dcc-fn-domain))
		(inside-interval-p (- x eps) (dcc-fn-domain))))
   :hints (("Goal"
	    :use ((:instance standard+eps-inside-standard-interval
			     (interval (dcc-fn-domain)))
		  (:instance dcc-fn-domain-non-trivial))))
   :rule-classes nil))

(local
 (defthm-std standard-derivative-dcc-fn1
     (implies (and (standardp x)
                   (standardp context1))
	      (standardp (derivative-dcc-fn1 context1 x)))))

(local
 (defthm-std standard-derivative-dcc-fn2
     (implies (and (standardp x)
                   (standardp context2))
	      (standardp (derivative-dcc-fn2 context2 x)))))

(local
 (defthm-std standard-derivative-dcc-fnz
     (implies (and (standardp x)
                   (standardp contextz))
	      (standardp (derivative-dcc-fnz contextz x)))))

(defun differential-dcc-fn1 (context1 x eps)
  (/ (- (dcc-fn1 context1 (+ x eps)) (dcc-fn1 context1 x)) eps))

(local
 (defthmd derivative-dcc-fn1-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context1))
	    (equal (derivative-dcc-fn1 context1 x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (dcc-fn-domain))
		       (standard-part
                        (differential-dcc-fn1 context1 x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (dcc-fn-domain))
			 (standard-part
                          (differential-dcc-fn1 context1 x (- (/ (i-large-integer)))))
		       'error))))
   :hints (("Goal"
	    :use ((:instance dcc-fn1-is-differentiable
			     (x x)
			     (x1 (+ x (/ (i-large-integer)))))
		  (:instance dcc-fn1-is-differentiable
			     (x x)
			     (x1 (- x (/ (i-large-integer)))))
		  (:instance standard+eps-inside-dcc-fn-domain
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (- (/ (i-large-integer)))))
		  (:instance close-x-y->same-standard-part
			     (x (derivative-dcc-fn1 context1 x))
			     (y (+ (- (* (i-large-integer)
					 (dcc-fn1 context1 x)))
				   (* (i-large-integer)
				      (dcc-fn1 context1 (+ (/ (i-large-integer)) x))))))
		  (:instance close-x-y->same-standard-part
			     (x (derivative-dcc-fn1 context1 x))
			     (y (+ (* (i-large-integer)
				      (dcc-fn1 context1 x))
				   (- (* (i-large-integer)
					 (dcc-fn1 context1 (+ (- (/ (i-large-integer))) x)))))))
		  (:instance standard-derivative-dcc-fn1)
		  )
	    :in-theory (disable i-close-to-small-sum
				standard-part-of-plus
				standard-part-of-uminus
				close-x-y->same-standard-part
				standard-derivative-dcc-fn1)
	    )
	   )))

(defun differential-dcc-fn2 (context2 x eps)
  (/ (- (dcc-fn2 context2 (+ x eps)) (dcc-fn2 context2 x)) eps))

(local
 (defthmd derivative-dcc-fn2-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context2))
	    (equal (derivative-dcc-fn2 context2 x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (dcc-fn-domain))
		       (standard-part
                        (differential-dcc-fn2 context2 x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (dcc-fn-domain))
			 (standard-part
                          (differential-dcc-fn2 context2 x (- (/ (i-large-integer)))))
		       'error))))
   :hints (("Goal"
	    :use ((:instance dcc-fn2-is-differentiable
			     (x x)
			     (x1 (+ x (/ (i-large-integer)))))
		  (:instance dcc-fn2-is-differentiable
			     (x x)
			     (x1 (- x (/ (i-large-integer)))))
		  (:instance standard+eps-inside-dcc-fn-domain
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (- (/ (i-large-integer)))))
		  (:instance close-x-y->same-standard-part
			     (x (derivative-dcc-fn2 context2 x))
			     (y (+ (- (* (i-large-integer)
					 (dcc-fn2 context2 x)))
				   (* (i-large-integer)
				      (dcc-fn2 context2 (+ (/ (i-large-integer)) x))))))
		  (:instance close-x-y->same-standard-part
			     (x (derivative-dcc-fn2 context2 x))
			     (y (+ (* (i-large-integer)
				      (dcc-fn2 context2 x))
				   (- (* (i-large-integer)
					 (dcc-fn2 context2
                                                  (+ (- (/ (i-large-integer))) x)))))))
		  (:instance standard-derivative-dcc-fn2)
		  )
	    :in-theory (disable i-close-to-small-sum
				standard-part-of-plus
				standard-part-of-uminus
				close-x-y->same-standard-part
				standard-derivative-dcc-fn2)
	    )
	   )))


(defun differential-dcc-fnz (contextz x eps)
  (/ (- (dcc-fnz contextz (+ x eps)) (dcc-fnz contextz x)) eps))

(local
 (defthmd derivative-dcc-fnz-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp contextz))
	    (equal (derivative-dcc-fnz contextz x)
		   (if (inside-interval-p (+ x (/ (i-large-integer))) (dcc-fn-domain))
		       (standard-part
                        (differential-dcc-fnz contextz x (/ (i-large-integer))))
		     (if (inside-interval-p (- x (/ (i-large-integer))) (dcc-fn-domain))
			 (standard-part (differential-dcc-fnz contextz x (- (/ (i-large-integer)))))
		       'error))))
   :hints (("Goal"
	    :use ((:instance dcc-fnz-is-differentiable
			     (x x)
			     (x1 (+ x (/ (i-large-integer)))))
		  (:instance dcc-fnz-is-differentiable
			     (x x)
			     (x1 (- x (/ (i-large-integer)))))
		  (:instance standard+eps-inside-dcc-fn-domain
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance i-close-to-small-sum
			     (x x)
			     (eps (- (/ (i-large-integer)))))
		  (:instance close-x-y->same-standard-part
			     (x (derivative-dcc-fnz contextz x))
			     (y (+ (- (* (i-large-integer)
					 (dcc-fnz contextz x)))
				   (* (i-large-integer)
				      (dcc-fnz contextz (+ (/ (i-large-integer)) x))))))
		  (:instance close-x-y->same-standard-part
			     (x (derivative-dcc-fnz contextz x))
			     (y (+ (* (i-large-integer)
				      (dcc-fnz contextz x))
				   (- (* (i-large-integer)
					 (dcc-fnz contextz
                                                  (+ (- (/ (i-large-integer))) x)))))))
		  (:instance standard-derivative-dcc-fnz)
		  )
	    :in-theory (disable i-close-to-small-sum
				standard-part-of-plus
				standard-part-of-uminus
				close-x-y->same-standard-part
				standard-derivative-dcc-fnz)
	    )
	   )))


(encapsulate
    ( ((dcc-car-context *) => *)
      ((dcc-cdr-context *) => *)
      )

    (local
     (defun dcc-car-context (context)
       (car context)))

  (local
   (defun dcc-cdr-context (context)
     (cdr context)))
  )

(local
 (defthm-std standard-dcc-car-context
     (implies (standardp context)
              (standardp (dcc-car-context context)))))

(local
 (defthm-std standard-dcc-cdr-context
     (implies (standardp context)
              (standardp (dcc-cdr-context context)))))

(encapsulate
 ( ((differential-dcc-fn1+fn2 * * *) => *)
   ((derivative-dcc-fn1+fn2 * *) => *)
   )

 (defun dcc-fn1+fn2 (context x)
   (+ (dcc-fn1 (dcc-car-context context) x) (dcc-fn2 (dcc-cdr-context context) x)))

 (local
  (defun differential-dcc-fn1+fn2 (context x eps)
    (+ (differential-dcc-fn1 (dcc-car-context context) x eps)
       (differential-dcc-fn2 (dcc-cdr-context context) x eps))))

 (local
  (defun derivative-dcc-fn1+fn2 (context x)
    (+ (derivative-dcc-fn1 (dcc-car-context context) x)
       (derivative-dcc-fn2 (dcc-cdr-context context) x))))

 (defthm differential-dcc-fn1+fn2-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (differential-dcc-fn1+fn2 context x eps)
		   (+ (differential-dcc-fn1 (dcc-car-context context) x eps)
		      (differential-dcc-fn2 (dcc-cdr-context context) x eps)))))

 (defthm derivative-dcc-fn1+fn2-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context))
	    (equal (derivative-dcc-fn1+fn2 context x)
		   (+ (derivative-dcc-fn1 (dcc-car-context context) x)
		      (derivative-dcc-fn2 (dcc-cdr-context context) x)))))
 )

(defthm dcc-fn1+fn2-differentiable
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited  (/ (- (dcc-fn1+fn2 context x)
                                    (dcc-fn1+fn2 context y1))
                                 (- x y1)))
		  (i-close (/ (- (dcc-fn1+fn2 context x)
                                 (dcc-fn1+fn2 context y1))
                              (- x y1))
			   (/ (- (dcc-fn1+fn2 context x)
                                 (dcc-fn1+fn2 context y2))
                              (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance dc-fn1+fn2-differentiable
				     (dc-fn1 dcc-fn1)
				     (dc-fn2 dcc-fn2)
				     (dc-fnz dcc-fnz)
				     (dc-fn-domain dcc-fn-domain)
				     (dc-fn1+fn2 dcc-fn1+fn2)
                                     (dc-car-context dcc-car-context)
                                     (dc-cdr-context dcc-cdr-context))
	   )
	  ("Subgoal 5"
	   :use ((:instance dcc-fnz-differentiable-using-nonstd-criterion)))
	  ("Subgoal 4"
	   :use ((:instance dcc-fn2-differentiable-using-nonstd-criterion)))
	  ("Subgoal 3"
	   :use ((:instance dcc-fn1-differentiable-using-nonstd-criterion)))
	  ("Subgoal 2"
	   :use ((:instance (:instance dcc-fn-domain-non-trivial))))
	  ))

(defun-sk forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works (context x eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (dcc-fn-domain))
			(inside-interval-p x (dcc-fn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (dcc-fn1+fn2 context x)
                                    (dcc-fn1+fn2 context x1))
                                 (- x x1))
			      (derivative-dcc-fn1+fn2 context x)))
		      eps))))

(defun-sk exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works (context x eps)
  (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works context x eps delta)))))

(defthmd differential-dcc-fn1+fn2-close
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (standard-part (differential-dcc-fn1+fn2 context x eps))
		   (derivative-dcc-fn1+fn2 context x)))
  :hints (("Goal"
	   :use ((:functional-instance differential-dc-fn1+fn2-close
				       (dc-fn1 dcc-fn1)
				       (dc-fn2 dcc-fn2)
				       (dc-fnz dcc-fnz)
				       (dc-fn-domain dcc-fn-domain)
				       (dc-fn1+fn2 dcc-fn1+fn2)
				       (differential-dc-fn1+fn2 differential-dcc-fn1+fn2)
				       (derivative-dc-fn1+fn2 derivative-dcc-fn1+fn2)
				       (differential-dc-fn1 differential-dcc-fn1)
				       (derivative-dc-fn1 derivative-dcc-fn1)
				       (differential-dc-fn2 differential-dcc-fn2)
				       (derivative-dc-fn2 derivative-dcc-fn2)
                                       (dc-car-context dcc-car-context)
                                       (dc-cdr-context dcc-cdr-context)
				       )))
	  ("Subgoal 6"
	   :use ((:instance derivative-dcc-fn2-definition)))
	  ("Subgoal 4"
	   :use ((:instance derivative-dcc-fn1-definition)))
	   ))

(defthmd dcc-fn1+fn2-derivative-using-classical-criterion
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (realp eps)
		  (standardp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works CONTEXT x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classical-derivative-using-classical-criterion
				     (rdfn dcc-fn1+fn2)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-fn1+fn2)
				     (differential-rdfn differential-dcc-fn1+fn2)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works-witness)
				     ))
	  ("Subgoal 9"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works-suff))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works)
	   )
	  ("Subgoal 7"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works-necc)))
	  ("Subgoal 5"
	   :use ((:instance derivative-dcc-fn1-definition
                            (context1 (dcc-car-context context)))
		 (:instance derivative-dcc-fn2-definition
                            (context2 (dcc-cdr-context context)))))
	  ("Subgoal 3"
	   :use ((:instance dcc-fn1+fn2-differentiable)))
	  ("Subgoal 2"
	   :use ((:instance (:instance dcc-fn-domain-non-trivial))))
	  ))

(defthmd dcc-fn1+fn2-differentiable-classical-using-hyperreal-criterion
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				     (rdfn dcc-fn1+fn2)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-fn1+fn2)
				     (differential-rdfn differential-dcc-fn1+fn2)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-fn1+fn2-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1+fn2-works-witness)
				     ))
	  ))

(encapsulate
 ( ((differential-dcc-minus-fn1 * * *) => *)
   ((derivative-dcc-minus-fn1 * *) => *)
   )

 (defun dcc-minus-fn1 (context x)
   (- (dcc-fn1 context x)))

 (local
  (defun differential-dcc-minus-fn1 (context x eps)
    (- (differential-dcc-fn1 context x eps))))

 (local
  (defun derivative-dcc-minus-fn1 (context x)
    (- (derivative-dcc-fn1 context x))))

 (defthm differential-dcc-minus-fn1-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (differential-dcc-minus-fn1 context x eps)
		   (- (differential-dcc-fn1 context x eps)))))

 (defthm derivative-dcc-minus-fn1-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context))
	    (equal (derivative-dcc-minus-fn1 context x)
		   (- (derivative-dcc-fn1 context x)))))
 )

(defthm dcc-minus-fn1-differentiable
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited  (/ (- (dcc-minus-fn1 context x)
                                    (dcc-minus-fn1 context y1))
                                 (- x y1)))
		  (i-close (/ (- (dcc-minus-fn1 context x)
                                 (dcc-minus-fn1 context y1))
                              (- x y1))
			   (/ (- (dcc-minus-fn1 context x)
                                 (dcc-minus-fn1 context y2))
                              (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance dc-minus-fn1-differentiable
				     (dc-fn1 dcc-fn1)
				     (dc-fn2 dcc-fn2)
				     (dc-fnz dcc-fnz)
				     (dc-fn-domain dcc-fn-domain)
				     (dc-minus-fn1 dcc-minus-fn1)))))

(defun-sk forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works (context x eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (dcc-fn-domain))
			(inside-interval-p x (dcc-fn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (dcc-minus-fn1 context x)
                                    (dcc-minus-fn1 context x1))
                                 (- x x1))
			      (derivative-dcc-minus-fn1 context x)))
		      eps))))

(defun-sk exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works (context x eps)
  (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works context x eps delta)))))


(defthmd differential-dcc-minus-fn1-close
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (standard-part (differential-dcc-minus-fn1 context x eps))
		   (derivative-dcc-minus-fn1 context x)))
  :hints (("Goal"
	   :use ((:functional-instance differential-dc-minus-fn1-close
				       (dc-fn1 dcc-fn1)
				       (dc-fn2 dcc-fn2)
				       (dc-fnz dcc-fnz)
				       (dc-fn-domain dcc-fn-domain)
				       (dc-minus-fn1 dcc-minus-fn1)
				       (differential-dc-minus-fn1 differential-dcc-minus-fn1)
				       (derivative-dc-minus-fn1 derivative-dcc-minus-fn1)
				       (differential-dc-fn1 differential-dcc-fn1)
				       (derivative-dc-fn1 derivative-dcc-fn1)
				       (differential-dc-fn2 differential-dcc-fn2)
				       (derivative-dc-fn2 derivative-dcc-fn2)
				       )))))


(defthmd dcc-minus-fn1-derivative-using-classical-criterion
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (realp eps)
		  (standardp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classical-derivative-using-classical-criterion
				     (rdfn dcc-minus-fn1)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-minus-fn1)
				     (differential-rdfn differential-dcc-minus-fn1)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works-witness)
				     ))
	  ("Subgoal 9"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works-suff))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works))
	  ("Subgoal 7"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works-necc)))
	  ("Subgoal 5"
	   :use ((:instance derivative-dcc-fn1-definition
                            (context1 context))))
	  ("Subgoal 3"
	   :use ((:instance dcc-minus-fn1-differentiable)))
	  ("Subgoal 2"
	   :use ((:instance (:instance dcc-fn-domain-non-trivial))))
	  ))

(defthmd dcc-minus-fn1-differentiable-classical-using-hyperreal-criterion
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				     (rdfn dcc-minus-fn1)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-minus-fn1)
				     (differential-rdfn differential-dcc-minus-fn1)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-minus-fn1-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-minus-fn1-works-witness)
				     ))
	  ))

(encapsulate
 ( ((differential-dcc-fn1*fn2 * * *) => *)
   ((derivative-dcc-fn1*fn2 * *) => *)
   )

  (defun dcc-fn1*fn2 (context x)
    (* (dcc-fn1 (dcc-car-context context) x) (dcc-fn2 (dcc-cdr-context context) x)))

  (local
   (defun differential-dcc-fn1*fn2 (context x eps)
     (+ (* (dcc-fn1 (dcc-car-context context) (+ x eps))
	   (differential-dcc-fn2 (dcc-cdr-context context) x eps))
	(* (dcc-fn2 (dcc-cdr-context context) x)
	   (differential-dcc-fn1 (dcc-car-context context) x eps)))))

  (local
   (defun derivative-dcc-fn1*fn2 (context x)
     (+ (* (dcc-fn1 (dcc-car-context context) x)
	   (derivative-dcc-fn2 (dcc-cdr-context context) x))
	(* (dcc-fn2 (dcc-cdr-context context) x)
	   (derivative-dcc-fn1 (dcc-car-context context) x)))))

  (defthm differential-dcc-fn1*fn2-definition
    (implies (and (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p (+ x eps) (dcc-fn-domain)))
	     (equal (differential-dcc-fn1*fn2 context x eps)
		    (+ (* (dcc-fn1 (dcc-car-context context) (+ x eps))
			  (differential-dcc-fn2 (dcc-cdr-context context) x eps))
		       (* (dcc-fn2 (dcc-cdr-context context) x)
			  (differential-dcc-fn1 (dcc-car-context context) x eps))))))

  (defthm derivative-dcc-fn1*fn2-definition
    (implies (inside-interval-p x (dcc-fn-domain))
	     (equal (derivative-dcc-fn1*fn2 context x)
		    (+ (* (dcc-fn1 (dcc-car-context context) x)
			  (derivative-dcc-fn2 (dcc-cdr-context context) x))
		       (* (dcc-fn2 (dcc-cdr-context context) x)
			  (derivative-dcc-fn1 (dcc-car-context context) x))))))
  )

(defthm dcc-fn1*fn2-differentiable
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited  (/ (- (dcc-fn1*fn2 context x)
                                    (dcc-fn1*fn2 context y1))
                                 (- x y1)))
		  (i-close (/ (- (dcc-fn1*fn2 context x)
                                 (dcc-fn1*fn2 context y1))
                              (- x y1))
			   (/ (- (dcc-fn1*fn2 context x)
                                 (dcc-fn1*fn2 context y2))
                              (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance dc-fn1*fn2-differentiable
				     (dc-fn1 dcc-fn1)
				     (dc-fn2 dcc-fn2)
				     (dc-fnz dcc-fnz)
                                     (dc-car-context dcc-car-context)
                                     (dc-cdr-context dcc-cdr-context)
				     (dc-fn-domain dcc-fn-domain)
				     (dc-fn1*fn2 dcc-fn1*fn2)))))

(defun-sk forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works (context x eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (dcc-fn-domain))
			(inside-interval-p x (dcc-fn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (dcc-fn1*fn2 context x)
                                    (dcc-fn1*fn2 context x1))
                                 (- x x1))
			      (derivative-dcc-fn1*fn2 context x)))
		      eps))))

(defun-sk exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works (context x eps)
  (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works context x eps delta)))))

(defthmd differential-dcc-fn1*fn2-close
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (standard-part (differential-dcc-fn1*fn2 context x eps))
		   (derivative-dcc-fn1*fn2 context x)))
  :hints (("Goal"
	   :use ((:functional-instance differential-dc-fn1*fn2-close
				       (dc-fn1 dcc-fn1)
				       (dc-fn2 dcc-fn2)
				       (dc-fnz dcc-fnz)
				       (dc-fn-domain dcc-fn-domain)
                                       (dc-car-context dcc-car-context)
                                       (dc-cdr-context dcc-cdr-context)
				       (dc-fn1*fn2 dcc-fn1*fn2)
				       (differential-dc-fn1*fn2 differential-dcc-fn1*fn2)
				       (derivative-dc-fn1*fn2 derivative-dcc-fn1*fn2)
				       (differential-dc-fn1 differential-dcc-fn1)
				       (derivative-dc-fn1 derivative-dcc-fn1)
				       (differential-dc-fn2 differential-dcc-fn2)
				       (derivative-dc-fn2 derivative-dcc-fn2)
				       )))))

(defthm expand-differential-dcc-fn1*fn2
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(inside-interval-p (+ x eps) (dcc-fn-domain)))
	   (equal (differential-dcc-fn1*fn2 context x eps)
		  (/ (- (dcc-fn1*fn2 context (+ x eps))
                        (dcc-fn1*fn2 context x))
                     eps)))
  :hints (("Goal"
	   :by (:functional-instance expand-differential-dc-fn1*fn2
				       (dc-fn1 dcc-fn1)
				       (dc-fn2 dcc-fn2)
				       (dc-fnz dcc-fnz)
				       (dc-fn-domain dcc-fn-domain)
                                       (dc-car-context dcc-car-context)
                                       (dc-cdr-context dcc-cdr-context)
				       (dc-fn1*fn2 dcc-fn1*fn2)
				       (differential-dc-fn1*fn2 differential-dcc-fn1*fn2)
				       (derivative-dc-fn1*fn2 derivative-dcc-fn1*fn2)
				       (differential-dc-fn1 differential-dcc-fn1)
				       (derivative-dc-fn1 derivative-dcc-fn1)
				       (differential-dc-fn2 differential-dcc-fn2)
				       (derivative-dc-fn2 derivative-dcc-fn2))
	   ))
  :rule-classes nil)

(defthmd dcc-fn1*fn2-derivative-using-classical-criterion
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (realp eps)
		  (standardp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classical-derivative-using-classical-criterion
				     (rdfn dcc-fn1*fn2)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-fn1*fn2)
				     (differential-rdfn differential-dcc-fn1*fn2)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works-witness)
				     ))
	  ("Subgoal 9"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works-suff))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works))
	  ("Subgoal 7"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works-necc)))
	  ("Subgoal 5"
	   :use ((:instance differential-dcc-fn1*fn2-close
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-dcc-fn1*fn2-close
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		  (:instance standard+eps-inside-dcc-fn-domain
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance standard+eps-inside-dcc-fn-domain
			     (x x)
			     (eps (- (/ (i-large-integer)))))))
	  ("Subgoal 3"
	   :use ((:instance dcc-fn1*fn2-differentiable)))
	  ("Subgoal 2"
	   :use ((:instance (:instance dcc-fn-domain-non-trivial))))
	  ))

(defthmd dcc-fn1*fn2-differentiable-classical-using-hyperreal-criterion
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				     (rdfn dcc-fn1*fn2)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-fn1*fn2)
				     (differential-rdfn differential-dcc-fn1*fn2)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-fn1*fn2-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-fn1*fn2-works-witness)
				     ))
	  ))


(encapsulate
 ( ((differential-dcc-/-fnz * * *) => *)
   ((derivative-dcc-/-fnz * *) => *)
   )

 (defun dcc-/-fnz (context x)
   (/ (dcc-fnz context x)))

 (local
  (defun differential-dcc-/-fnz (context x eps)
    (- (/ (differential-dcc-fnz context x eps)
	  (* (dcc-fnz context (+ x eps))
	     (dcc-fnz context x))))
    ))

 (local
  (defun derivative-dcc-/-fnz (context x)
    (- (/ (derivative-dcc-fnz context x)
	  (* (dcc-fnz context x)
	     (dcc-fnz context x))))
    ))

 (defthm differential-dcc-/-fnz-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (differential-dcc-/-fnz context x eps)
		   (- (/ (differential-dcc-fnz context x eps)
			 (* (dcc-fnz context (+ x eps))
			    (dcc-fnz context x)))))))

 (defthm derivative-dcc-/-fnz-definition
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context))
	    (equal (derivative-dcc-/-fnz context x)
		   (- (/ (derivative-dcc-fnz context x)
			 (* (dcc-fnz context x)
			    (dcc-fnz context x)))))))
 )

(defthm dcc-/-fnz-differentiable
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (inside-interval-p y1 (dcc-fn-domain))
		  (inside-interval-p y2 (dcc-fn-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited  (/ (- (dcc-/-fnz context x)
                                    (dcc-/-fnz context y1))
                                 (- x y1)))
		  (i-close (/ (- (dcc-/-fnz context x)
                                 (dcc-/-fnz context y1))
                              (- x y1))
			   (/ (- (dcc-/-fnz context x)
                                 (dcc-/-fnz context y2))
                              (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance dc-/-fnz-differentiable
				     (dc-fn1 dcc-fn1)
				     (dc-fn2 dcc-fn2)
				     (dc-fnz dcc-fnz)
				     (dc-fn-domain dcc-fn-domain)
                                     (dc-car-context dcc-car-context)
                                     (dc-cdr-context dcc-cdr-context)
				     (dc-/-fnz dcc-/-fnz)))))

(defun-sk forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works (context x eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (dcc-fn-domain))
			(inside-interval-p x (dcc-fn-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (dcc-/-fnz context x)
                                    (dcc-/-fnz context x1))
                                 (- x x1))
			      (derivative-dcc-/-fnz context x)))
		      eps))))

(defun-sk exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works (context x eps)
  (exists delta
	  (implies (and (inside-interval-p x (dcc-fn-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works context x eps delta)))))

(defthmd differential-dcc-/-fnz-close
   (implies (and (inside-interval-p x (dcc-fn-domain))
		 (standardp x)
                 (standardp context)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (dcc-fn-domain)))
	    (equal (standard-part (differential-dcc-/-fnz context x eps))
		   (derivative-dcc-/-fnz context x)))
  :hints (("Goal"
	   :use ((:functional-instance differential-dc-/-fnz-close
				       (dc-fn1 dcc-fn1)
				       (dc-fn2 dcc-fn2)
				       (dc-fnz dcc-fnz)
				       (dc-fn-domain dcc-fn-domain)
                                       (dc-car-context dcc-car-context)
                                       (dc-cdr-context dcc-cdr-context)
				       (dc-/-fnz dcc-/-fnz)
				       (differential-dc-/-fnz differential-dcc-/-fnz)
				       (derivative-dc-/-fnz derivative-dcc-/-fnz)
				       (differential-dc-fnz differential-dcc-fnz)
				       (derivative-dc-fnz derivative-dcc-fnz)
				       )))
	   ("Subgoal 4"
	    :use ((:instance derivative-dcc-fnz-definition)))
	   ))

(defthm expand-differential-dcc-/-fnz
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(inside-interval-p (+ x eps) (dcc-fn-domain)))
	   (equal (differential-dcc-/-fnz context x eps)
		  (/ (- (dcc-/-fnz context (+ x eps)) (dcc-/-fnz context x)) eps)))
  :hints (("Goal"
	   :by (:functional-instance expand-differential-dc-/-fnz
				       (dc-fn1 dcc-fn1)
				       (dc-fn2 dcc-fn2)
				       (dc-fnz dcc-fnz)
				       (dc-fn-domain dcc-fn-domain)
				       (dc-/-fnz dcc-/-fnz)
                                       (dc-car-context dcc-car-context)
                                       (dc-cdr-context dcc-cdr-context)
				       (differential-dc-/-fnz differential-dcc-/-fnz)
				       (derivative-dc-/-fnz derivative-dcc-/-fnz)
				       (differential-dc-fnz differential-dcc-fnz)
				       (derivative-dc-fnz derivative-dcc-fnz))
	   ))
  :rule-classes nil)

(defthmd dcc-/-fnz-derivative-using-classical-criterion
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (dcc-fn-domain))
		  (realp eps)
		  (standardp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classical-derivative-using-classical-criterion
				     (rdfn dcc-/-fnz)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-/-fnz)
				     (differential-rdfn differential-dcc-/-fnz)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works-witness)
				     ))
	  ("Subgoal 9"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works-suff))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works))
	  ("Subgoal 7"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works-necc)))
	  ("Subgoal 5"
	   :use ((:instance differential-dcc-/-fnz-close
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-dcc-/-fnz-close
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		 (:instance standard+eps-inside-dcc-fn-domain
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance standard+eps-inside-dcc-fn-domain
			    (x x)
			    (eps (- (/ (i-large-integer)))))))
	  ("Subgoal 3"
	   :use ((:instance dcc-/-fnz-differentiable)))
	  ("Subgoal 2"
	   :use ((:instance (:instance dcc-fn-domain-non-trivial))))
	  ))

(defthmd dcc-/-fnz-differentiable-classical-using-hyperreal-criterion
  (implies (and (inside-interval-p x (dcc-fn-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				     (rdfn dcc-/-fnz)
				     (rdfn-domain dcc-fn-domain)
				     (derivative-rdfn derivative-dcc-/-fnz)
				     (differential-rdfn differential-dcc-/-fnz)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-dcc-/-fnz-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-dcc-/-fnz-works-witness)
				     ))
	  ))

(encapsulate
 ((ccr-fn1 (context x) t)
  (derivative-ccr-fn1 (context x) t)
  (ccr-fn2 (context x) t)
  (derivative-ccr-fn2 (context x) t)
  (ccr-fn2-domain () t)
  (ccr-fn2-range () t))

 ;; Our witness continuous function is the identity function.

 (local (defun ccr-fn1 (context x) (declare (ignore context x)) 1))
 (local (defun derivative-ccr-fn1 (context x) (declare (ignore context x)) 0))
 (local (defun ccr-fn2 (context x) (declare (ignore context x)) 1))
 (local (defun derivative-ccr-fn2 (context x) (declare (ignore context x)) 0))
 (local (defun ccr-fn2-domain () (interval 0 1)))
 (local (defun ccr-fn2-range () (interval 0 1)))

 ;; The interval really is an interval

 (defthm intervalp-ccr-fn2-domain
     (interval-p (ccr-fn2-domain))
   :rule-classes (:type-prescription :rewrite))

 (defthm intervalp-ccr-fn2-range
     (interval-p (ccr-fn2-range))
   :rule-classes (:type-prescription :rewrite))

 ;; The interval is real

 (defthm ccr-fn2-domain-real
     (implies (inside-interval-p x (ccr-fn2-domain))
	      (realp x))
   :rule-classes (:forward-chaining))

 (defthm ccr-fn2-range-real
     (implies (inside-interval-p x (ccr-fn2-range))
	      (realp x))
   :rule-classes (:forward-chaining))

 ;; The interval is non-trivial

 (defthm ccr-fn2-domain-non-trivial
     (or (null (interval-left-endpoint (ccr-fn2-domain)))
	 (null (interval-right-endpoint (ccr-fn2-domain)))
	 (< (interval-left-endpoint (ccr-fn2-domain))
	    (interval-right-endpoint (ccr-fn2-domain))))
   :rule-classes nil)

 (defthm ccr-fn2-range-non-trivial
     (or (null (interval-left-endpoint (ccr-fn2-range)))
	 (null (interval-right-endpoint (ccr-fn2-range)))
	 (< (interval-left-endpoint (ccr-fn2-range))
	    (interval-right-endpoint (ccr-fn2-range))))
   :rule-classes nil)

 ;; The functions return real values (even for improper arguments).

 (defthm ccr-fn1-real
     (realp (ccr-fn1 context1 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm ccr-fn2-real
     (realp (ccr-fn2 context2 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm derivative-ccr-fn1-real
   (realp (derivative-ccr-fn1 context1 x))
   :rule-classes (:rewrite :type-prescription))

 (defthm derivative-ccr-fn2-real
   (realp (derivative-ccr-fn2 context2 x))
   :rule-classes (:rewrite :type-prescription))

 ;; The range of fn2 is inside the domain of fn1

 (defthm ccr-fn2-range-in-domain-of-fn2
     (implies (inside-interval-p x (ccr-fn2-domain))
	      (inside-interval-p (ccr-fn2 context2 x) (ccr-fn2-range))))

 ;; If x is a standard real and y1 and y2 are two arbitrary reals
 ;; close to x, then (rdfn(x)-rdfn(y1))/(x-y1) is close to
 ;; (rdfn(x)-rdfn(y2))/(x-y2).  Also, (rdfn(x)-rdfn(y1))/(x-y1) is
 ;; limited.  What this means is that the standard-part of that is a
 ;; standard number, and we'll call that the derivative of rdfn at x.

 (defun-sk forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1 (context1 x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (ccr-fn2-range))
			 (inside-interval-p x (ccr-fn2-range))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (ccr-fn1 context1 x) (ccr-fn1 context1 x1)) (- x x1))
			       (derivative-ccr-fn1 context1 x)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1 (context1 x eps)
  (exists delta
	  (implies (and (inside-interval-p x (ccr-fn2-range))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1 context1 x eps delta)))))

 (defun-sk forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2 (context2 x eps delta)
   (forall (x1)
	   (implies (and (inside-interval-p x1 (ccr-fn2-domain))
			 (inside-interval-p x (ccr-fn2-domain))
			 (realp delta)
			 (< 0 delta)
			 (realp eps)
			 (< 0 eps)
			 (not (equal x x1))
			 (< (abs (- x x1)) delta))
		    (< (abs (- (/ (- (ccr-fn2 context2 x) (ccr-fn2 context2 x1)) (- x x1))
			       (derivative-ccr-fn2 context2 x)))
		       eps)))
   :rewrite :direct)

 (defun-sk exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2 (context2 x eps)
   (exists delta
	  (implies (and (inside-interval-p x (ccr-fn2-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2 context2 x eps delta)))))

 (defthm derivative-ccr-fn1-is-derivative
  (implies (and (inside-interval-p x (ccr-fn2-range))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1 context1 x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1-suff
			    (delta 1)))))
  )

 (defthm derivative-ccr-fn2-is-derivative
  (implies (and (inside-interval-p x (ccr-fn2-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2 context2 x eps))
  :hints (("Goal"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2-suff
			    (delta 1)))))
  )
 )


(defthm ccr-fn1-differentiable-using-nonstd-criterion
    (implies (and (standardp x)
                  (standardp context1)
		  (inside-interval-p x (ccr-fn2-range))
		  (inside-interval-p y1 (ccr-fn2-range))
		  (inside-interval-p y2 (ccr-fn2-range))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited (/ (- (ccr-fn1 context1 x) (ccr-fn1 context1 y1)) (- x y1)))
		  (i-close (/ (- (ccr-fn1 context1 x) (ccr-fn1 context1 y1)) (- x y1))
			   (/ (- (ccr-fn1 context1 x) (ccr-fn1 context1 y2)) (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable-using-nonstd-criterion
				     (rdfn-classical ccr-fn1)
				     (derivative-rdfn-classical derivative-ccr-fn1)
				     (rdfn-classical-domain ccr-fn2-range)
				     (exists-delta-for-x-and-eps-so-deriv-classical-works
				      exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1)
				     (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				      exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1-witness)
				     (forall-x-eps-delta-in-range-deriv-classical-works
				      forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1)
				     (forall-x-eps-delta-in-range-deriv-classical-works-witness
				      forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1-witness)
				     ))
	  ("Subgoal 5"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1-suff
                  (context1 context)))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1))
	  ("Subgoal 3"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1-necc
                  (context1 context))))
	  ("Subgoal 2"
	   :use ((:instance ccr-fn2-range-non-trivial)))
	  ))

(defthm ccr-fn2-differentiable-using-nonstd-criterion
    (implies (and (standardp x)
                  (standardp context2)
		  (inside-interval-p x (ccr-fn2-domain))
		  (inside-interval-p y1 (ccr-fn2-domain))
		  (inside-interval-p y2 (ccr-fn2-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited (/ (- (ccr-fn2 context2 x)
                                   (ccr-fn2 context2 y1))
                                (- x y1)))
		  (i-close (/ (- (ccr-fn2 context2 x) (ccr-fn2 context2 y1)) (- x y1))
			   (/ (- (ccr-fn2 context2 x) (ccr-fn2 context2 y2)) (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable-using-nonstd-criterion
				     (rdfn-classical ccr-fn2)
				     (derivative-rdfn-classical derivative-ccr-fn2)
				     (rdfn-classical-domain ccr-fn2-domain)
				     (exists-delta-for-x-and-eps-so-deriv-classical-works
				      exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2)
				     (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				      exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2-witness)
				     (forall-x-eps-delta-in-range-deriv-classical-works
				      forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2)
				     (forall-x-eps-delta-in-range-deriv-classical-works-witness
				      forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2-witness)
				     ))
	  ("Subgoal 5"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2-suff
                  (context2 context)))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2))
	  ("Subgoal 3"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2-necc
                  (context2 context))))
	  ("Subgoal 2"
	   :use ((:instance ccr-fn2-domain-non-trivial)))
	  ))

(defun differential-ccr-fn1 (context1 x eps)
  (/ (- (ccr-fn1 context1 (+ x eps)) (ccr-fn1 context1 x)) eps))

(defun differential-ccr-fn2 (context2 x eps)
  (/ (- (ccr-fn2 context2 (+ x eps)) (ccr-fn2 context2 x)) eps))

(defun ccr-fn1-o-fn2 (context x)
  (ccr-fn1 (dcc-car-context context) (ccr-fn2 (dcc-cdr-context context) x)))

(defun differential-ccr-fn1-o-fn2 (context x eps)
  (if (equal (ccr-fn2 (dcc-cdr-context context) (+ x eps)) (ccr-fn2 (dcc-cdr-context context) x))
      0
      (* (differential-ccr-fn1 (dcc-car-context context) (ccr-fn2 (dcc-cdr-context context) x)
                               (- (ccr-fn2 (dcc-cdr-context context) (+ x eps))
                                  (ccr-fn2 (dcc-cdr-context context) x)))
	 (differential-ccr-fn2 (dcc-cdr-context context) x eps))))

(defun derivative-ccr-fn1-o-fn2 (context x)
  (* (derivative-ccr-fn1 (dcc-car-context context) (ccr-fn2 (dcc-cdr-context context) x))
     (derivative-ccr-fn2 (dcc-cdr-context context) x)))

(defthm ccr-fn1-o-fn2-differentiable
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (ccr-fn2-domain))
		  (inside-interval-p y1 (ccr-fn2-domain))
		  (inside-interval-p y2 (ccr-fn2-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (and (i-limited  (/ (- (ccr-fn1-o-fn2 context x)
                                    (ccr-fn1-o-fn2 context y1))
                                 (- x y1)))
		  (i-close (/ (- (ccr-fn1-o-fn2 context x)
                                 (ccr-fn1-o-fn2 context y1))
                              (- x y1))
			   (/ (- (ccr-fn1-o-fn2 context x)
                                 (ccr-fn1-o-fn2 context y2))
                              (- x y2)))))
  :hints (("Goal"
	   :by (:functional-instance cr-fn1-o-fn2-differentiable
				     (cr-fn1 ccr-fn1)
				     (cr-fn2 ccr-fn2)
				     (cr-fn2-domain ccr-fn2-domain)
                                     (cr-car-context dcc-car-context)
                                     (cr-cdr-context dcc-cdr-context)
				     (cr-fn2-range ccr-fn2-range)
				     (cr-fn1-o-fn2 ccr-fn1-o-fn2)))
	  ("Subgoal 8"
	   :use ((:instance ccr-fn2-differentiable-using-nonstd-criterion
                            (context2 context))))
	  ("Subgoal 7"
	   :use ((:instance ccr-fn1-differentiable-using-nonstd-criterion
                            (context1 context))))
	  ("Subgoal 5"
	   :use ((:instance ccr-fn2-range-non-trivial)))
	  ("Subgoal 4"
	   :use ((:instance ccr-fn2-domain-non-trivial)))))

(defun-sk forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works (context x eps delta)
  (forall (x1)
	  (implies (and (inside-interval-p x1 (ccr-fn2-domain))
			(inside-interval-p x (ccr-fn2-domain))
			(realp delta)
			(< 0 delta)
			(realp eps)
			(< 0 eps)
			(not (equal x x1))
			(< (abs (- x x1)) delta))
		   (< (abs (- (/ (- (ccr-fn1-o-fn2 context x) (ccr-fn1-o-fn2 context x1)) (- x x1))
			      (derivative-ccr-fn1-o-fn2 context x)))
		      eps)))
  :rewrite :direct)

(defun-sk exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works (context x eps)
  (exists delta
	  (implies (and (inside-interval-p x (ccr-fn2-domain))
			;(standardp x)
			(realp eps)
			;(standardp eps)
			(< 0 eps))
		   (and (realp delta)
			(< 0 delta)
			(forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works context x eps delta)))))

(defthmd ccr-fn1-is-differentiable
    (implies (and (standardp x)
                  (standardp context1)
		  (inside-interval-p x (ccr-fn2-range))
		  (i-close x x1)
		  (inside-interval-p x1 (ccr-fn2-range))
		  (not (equal x1 x)))
	     (i-close (/ (- (ccr-fn1 context1 x)
                            (ccr-fn1 context1 x1))
                         (- x x1))
		      (derivative-ccr-fn1 context1 x)))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable
				     (rdfn-classical ccr-fn1)
				     (derivative-rdfn-classical derivative-ccr-fn1)
				     (rdfn-classical-domain ccr-fn2-range)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn1-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works
				       forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1)
				      (forall-x-eps-delta-in-range-deriv-classical-works-witness
				       forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn1-witness)
				      ))
	  ))

(defthmd ccr-fn2-is-differentiable
    (implies (and (standardp x)
                  (standardp context2)
		  (inside-interval-p x (ccr-fn2-domain))
		  (i-close x x1)
		  (inside-interval-p x1 (ccr-fn2-domain))
		  (not (equal x1 x)))
	     (i-close (/ (- (ccr-fn2 context2 x)
                            (ccr-fn2 context2 x1))
                         (- x x1))
		      (derivative-ccr-fn2 context2 x)))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classic-is-differentiable
				     (rdfn-classical ccr-fn2)
				     (derivative-rdfn-classical derivative-ccr-fn2)
				     (rdfn-classical-domain ccr-fn2-domain)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2)
				      (exists-delta-for-x-and-eps-so-deriv-classical-works-witness
				       exists-delta-for-x-and-eps-so-deriv-classical-works-for-ccr-fn2-witness)
				      (forall-x-eps-delta-in-range-deriv-classical-works
				       forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2)
				      (forall-x-eps-delta-in-range-deriv-classical-works-witness
				       forall-x-eps-delta-in-range-deriv-classical-works-for-ccr-fn2-witness)
				      ))
	  ))


(defthm-std standard-derivative-ccr-fn1
    (implies (and (standardp x)
                  (standardp context1))
             (standardp (derivative-ccr-fn1 context1 x))))

(defthm-std standard-derivative-ccr-fn2
    (implies (and (standardp x)
                  (standardp context2))
             (standardp (derivative-ccr-fn2 context2 x))))

(defthmd differential-ccr-fn1-close
  (implies (and (inside-interval-p x (ccr-fn2-range))
                (standardp x)
                (standardp context1)
                (realp eps) (i-small eps) (not (= eps 0))
                (inside-interval-p (+ x eps) (ccr-fn2-range)))
           (equal (standard-part (differential-ccr-fn1 context1 x eps))
                  (derivative-ccr-fn1 context1 x)))
  :hints (("Goal"
           :use ((:instance close-x-y->same-standard-part
                            (x (derivative-ccr-fn1 context1 x))
                            (y (differential-ccr-fn1 context1 x eps)))
                 (:instance ccr-fn1-is-differentiable
                            (x x)
                            (x1 (+ x eps)))
                 (:instance i-close-to-small-sum)
                 (:instance standard-derivative-ccr-fn1)
                 )
           :in-theory (disable standard-derivative-ccr-fn1
                               close-x-y->same-standard-part
                               i-close-to-small-sum
                               standard-part-of-plus
                               standard-part-of-uminus)
           )
          ))

(defthmd differential-ccr-fn2-close
  (implies (and (inside-interval-p x (ccr-fn2-domain))
                (standardp x)
                (standardp context2)
                (realp eps) (i-small eps) (not (= eps 0))
                (inside-interval-p (+ x eps) (ccr-fn2-domain)))
           (equal (standard-part (differential-ccr-fn2 context2 x eps))
                  (derivative-ccr-fn2 context2 x)))
  :hints (("Goal"
           :use ((:instance close-x-y->same-standard-part
                            (x (derivative-ccr-fn2 context2 x))
                            (y (differential-ccr-fn2 context2 x eps)))
                 (:instance ccr-fn2-is-differentiable
                            (x x)
                            (x1 (+ x eps)))
                 (:instance i-close-to-small-sum)
                 (:instance standard-derivative-ccr-fn2)
                 )
           :in-theory (disable standard-derivative-ccr-fn2
                               close-x-y->same-standard-part
                               i-close-to-small-sum
                               standard-part-of-plus
                               standard-part-of-uminus)
           )
          ))

(local
 (defthm-std standard-ccr-fn2-domain
   (standardp (ccr-fn2-domain))))

(local
 (defthm standard+eps-inside-ccr-fn2-domain
   (implies (and (inside-interval-p x (ccr-fn2-domain))
		 (standardp x)
		 (realp eps)
		 (i-small eps))
	    (or (inside-interval-p (+ x eps) (ccr-fn2-domain))
		(inside-interval-p (- x eps) (ccr-fn2-domain))))
   :hints (("Goal"
	    :use ((:instance standard+eps-inside-standard-interval
			     (interval (ccr-fn2-domain)))
		  (:instance ccr-fn2-domain-non-trivial))))
   :rule-classes nil))

(local
 (defthm-std standard-ccr-fn2-range
   (standardp (ccr-fn2-range))))

(local
 (defthm standard+eps-inside-ccr-fn2-range
   (implies (and (inside-interval-p x (ccr-fn2-range))
		 (standardp x)
		 (realp eps)
		 (i-small eps))
	    (or (inside-interval-p (+ x eps) (ccr-fn2-range))
		(inside-interval-p (- x eps) (ccr-fn2-range))))
   :hints (("Goal"
	    :use ((:instance standard+eps-inside-standard-interval
			     (interval (ccr-fn2-range)))
		  (:instance ccr-fn2-range-non-trivial))))
   :rule-classes nil))

(defthmd differential-ccr-fn1-o-fn2-close
   (implies (and (inside-interval-p x (ccr-fn2-domain))
		 (standardp x)
                 (standardp context)
		 (realp eps) (i-small eps) (not (= eps 0))
		 (inside-interval-p (+ x eps) (ccr-fn2-domain)))
	    (equal (standard-part (differential-ccr-fn1-o-fn2 context x eps))
		   (derivative-ccr-fn1-o-fn2 context x)))
  :hints (("Goal"
	   :use ((:functional-instance differential-cr-fn1-o-fn2-close
				       (cr-fn1 ccr-fn1)
				       (cr-fn2 ccr-fn2)
				       (cr-fn2-domain ccr-fn2-domain)
                                       (cr-car-context dcc-car-context)
                                       (cr-cdr-context dcc-cdr-context)
				       (cr-fn2-range ccr-fn2-range)
				       (cr-fn1-o-fn2 ccr-fn1-o-fn2)
				       (differential-cr-fn1-o-fn2 differential-ccr-fn1-o-fn2)
				       (derivative-cr-fn1-o-fn2 derivative-ccr-fn1-o-fn2)
				       (differential-cr-fn1 differential-ccr-fn1)
				       (derivative-cr-fn1 derivative-ccr-fn1)
				       (differential-cr-fn2 differential-ccr-fn2)
				       (derivative-cr-fn2 derivative-ccr-fn2)
				       )))
          ("Subgoal 5"
           :use ((:instance differential-ccr-fn2-close
                            (context2 context)
                            (x x)
                            (eps (/ (i-large-integer))))
                 (:instance differential-ccr-fn2-close
                            (context2 context)
                            (x x)
                            (eps (/ (- (i-large-integer)))))
                 (:instance standard+eps-inside-ccr-fn2-domain
                            (eps (/ (i-large-integer)))))
           :in-theory (disable differential-ccr-fn2-close))
          ("Subgoal 3"
           :use ((:instance differential-ccr-fn1-close
                            (context1 context)
                            (x x)
                            (eps (/ (i-large-integer))))
                 (:instance differential-ccr-fn1-close
                            (context1 context)
                            (x x)
                            (eps (/ (- (i-large-integer)))))
                 (:instance standard+eps-inside-ccr-fn2-range
                            (eps (/ (i-large-integer)))))
           :in-theory (disable differential-ccr-fn1-close))
          ))

(defthm expand-differential-ccr-fn1-o-fn2
  (implies (and (inside-interval-p x (ccr-fn2-domain))
                (inside-interval-p (+ x eps) (ccr-fn2-domain)))
           (equal (differential-ccr-fn1-o-fn2 context x eps)
                  (/ (- (ccr-fn1-o-fn2 context (+ x eps))
                        (ccr-fn1-o-fn2 context x))
                     eps)))
  :hints (("Goal"
	   :by (:functional-instance expand-differential-cr-fn1-o-fn2
				     (cr-fn1 ccr-fn1)
				     (cr-fn2 ccr-fn2)
                                     (cr-car-context dcc-car-context)
                                     (cr-cdr-context dcc-cdr-context)
				     (cr-fn2-domain ccr-fn2-domain)
				     (cr-fn2-range ccr-fn2-range)
				     (cr-fn1-o-fn2 ccr-fn1-o-fn2)
				     (differential-cr-fn1-o-fn2 differential-ccr-fn1-o-fn2)
				     (derivative-cr-fn1-o-fn2 derivative-ccr-fn1-o-fn2)
				     (differential-cr-fn1 differential-ccr-fn1)
				     (derivative-cr-fn1 derivative-ccr-fn1)
				     (differential-cr-fn2 differential-ccr-fn2)
				     (derivative-cr-fn2 derivative-ccr-fn2))
	   ))
  :rule-classes nil)

(defthmd ccr-fn1-o-fn2-derivative-using-classical-criterion
    (implies (and (standardp x)
                  (standardp context)
		  (inside-interval-p x (ccr-fn2-domain))
		  (realp eps)
		  (standardp eps)
		  (< 0 eps))
	     (exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-classical-derivative-using-classical-criterion
				     (rdfn ccr-fn1-o-fn2)
				     (rdfn-domain ccr-fn2-domain)
				     (derivative-rdfn derivative-ccr-fn1-o-fn2)
				     (differential-rdfn differential-ccr-fn1-o-fn2)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works-witness)
				     ))
	  ("Subgoal 9"
	   :use ((:instance exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works-suff))
	   :in-theory (disable forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works))
	  ("Subgoal 7"
	   :use ((:instance forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works-necc)))
	  ("Subgoal 5"
	   :use ((:instance differential-ccr-fn1-o-fn2-close
			    (x x)
			    (eps (/ (i-large-integer))))
		 (:instance differential-ccr-fn1-o-fn2-close
			    (x x)
			    (eps (- (/ (i-large-integer)))))
		  (:instance standard+eps-inside-ccr-fn2-domain
			     (x x)
			     (eps (/ (i-large-integer))))
		  (:instance standard+eps-inside-ccr-fn2-domain
			     (x x)
			     (eps (- (/ (i-large-integer)))))))
	  ("Subgoal 4"
	   :use ((:instance expand-differential-ccr-fn1-o-fn2)))
	  ("Subgoal 3"
	   :use ((:instance ccr-fn1-o-fn2-differentiable)))
	  ("Subgoal 2"
	   :use ((:instance (:instance ccr-fn2-domain-non-trivial))))
	  ))

(defthmd ccr-fn1-o-fn2-differentiable-classical-using-hyperreal-criterion
  (implies (and (inside-interval-p x (ccr-fn2-domain))
		(realp eps)
		(< 0 eps))
	   (exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works context x eps))
  :hints (("Goal"
	   :by (:functional-instance rdfn-differentiable-classical-using-hyperreal-criterion
				     (rdfn ccr-fn1-o-fn2)
				     (rdfn-domain ccr-fn2-domain)
				     (derivative-rdfn derivative-ccr-fn1-o-fn2)
				     (differential-rdfn differential-ccr-fn1-o-fn2)
				     (forall-x-eps-delta-in-range-deriv-works
				      forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works)
				     (forall-x-eps-delta-in-range-deriv-works-witness
				      forall-x-eps-delta-in-range-deriv-ccr-fn1-o-fn2-works-witness)
				     (exists-delta-for-x-and-eps-so-deriv-works
				      exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works)
				     (exists-delta-for-x-and-eps-so-deriv-works-witness
				      exists-delta-for-x-and-eps-so-deriv-ccr-fn1-o-fn2-works-witness)
				     ))
	  ))
