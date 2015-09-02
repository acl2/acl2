(in-package "ACL2")

(include-book "nonstd/nsa/inverse-monotone" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nsa-ex")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(local
 (defun sine-interval (y)
   (declare (ignore y))
   (interval (- (/ (acl2-pi) 2)) (/ (acl2-pi) 2))))

(local
 (defun cosine-interval (y)
   (declare (ignore y))
   (interval 0 (acl2-pi))))

(local
 (defthm trivial-subinterval
     (implies (and (realp x)
		   (realp y)
		   (< x y))
	      (subinterval-p (interval x y) (interval x y)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm *-x-0
   (equal (* x 0) 0)))

(local
 (defthm-std standard-pi
     (standardp (acl2-pi))))

(local
 (defthm-std standard-exp
     (implies (standardp x)
	      (standardp (acl2-exp x)))))


(local
 (defthm-std standard-cosine
     (implies (standardp x)
	      (standardp (acl2-cosine x)))))


(encapsulate
 ()
 (local
  (defthm lemma-1
      (implies (and (realp c)
		    (realp s)
		    (equal (+ (* s s) (* c c)) 1))
	       (<= c 1))))
 (local
  (defthm lemma-2
      (implies (and (realp c)
		    (realp s)
		    (equal (+ (* s s) (* c c)) 1))
	       (<= -1 c))
    :hints (("Goal"
	     :use ((:instance lemma-1 (c (- c))))
	     :in-theory (disable lemma-1)))))
 (defthm cosine-bound
     (implies (realp x)
	      (and (<= -1 (acl2-cosine x))
		   (<= (acl2-cosine x) 1)))
   :hints (("Goal"
	    :use ((:instance lemma-1
			     (s (acl2-sine x))
			     (c (acl2-cosine x)))
		  (:instance lemma-2
			     (s (acl2-sine x))
			     (c (acl2-cosine x))))
	    :in-theory (disable lemma-1 lemma-2))))
 )

(local
 (defthm standard-part-<=-acl2-pi
  (implies (and (realp x)
                (<= x (acl2-pi)))
           (<= (standard-part x) (acl2-pi)))
  :hints (("Goal"
           :use ((:instance standard-part-<=
                            (x x)
                            (y (acl2-pi))))
           :in-theory (disable standard-part-<=)))))

(local
 (encapsulate
  ()
  (local
   (defthm lemma-1-1-1
       (implies (and (realp x)
		     (realp y)
		     (<= 0 x)
		     (< x y)
		     (<= y (acl2-pi)))
		(and (<= 0 (- y x))
		     (<= (- y x) (acl2-pi))))))
  (local
   (defthm lemma-1-1-2
       (equal (acl2-sine (* 1/2 (acl2-pi))) 1)))
  (local
   (defthm lemma-1-1-3
       (implies (and (realp x)
		     (<= 0 x)
		     (<= x (acl2-pi)))
		(<= 0 (acl2-sine x)))
     :hints (("goal"
	      :use ((:instance sine-positive-in-0-pi/2)
		    (:instance sine-positive-in-pi/2-pi))
	      :in-theory (disable sine-positive-in-0-pi/2
				  sine-positive-in-pi/2-pi
				  sine-2x
				  sine-3x)))))
  (local
   (defthm lemma-1-1
       (implies (and (realp x)
		     (realp y)
		     (<= 0 x)
		     (< x y)
		     (<= y (acl2-pi)))
		(<= 0 (* (acl2-sine x)
			 (acl2-sine (- y x)))))
     :hints (("goal"
	      :use ((:instance lemma-1-1-1)
		    (:instance lemma-1-1-3)
		    (:instance lemma-1-1-3 (x (- y x))))
	      :in-theory (disable lemma-1-1-1 lemma-1-1-3 sine-of-sums)))))
  (local
   (defthm lemma-1-2
       (implies (and (realp x)
		     (realp y)
		     (<= 0 x)
		     (< x y)
		     (<= y (acl2-pi)))
		(<= (acl2-cosine y)
		    (* (acl2-cosine x)
		       (acl2-cosine (- y x)))))
     :hints (("goal"
	      :use ((:instance cosine-of-sums
			       (x x)
			       (y (- y x)))
		    (:instance lemma-1-1))
	      :in-theory (disable cosine-of-sums
				  sine-of-sums
				  lemma-1-1
				  lemma-1-1-3)))))
  (local
   (defthm lemma-1-3
       (implies (and (realp x)
		     (realp y1)
		     (realp y2)
		     (<= x (* y1 y2))
		     (< 0 x)
		     (< 0 y2)
		     (< y2 1))
		(< x y1))
     :hints (("goal"
	      :use ((:instance *-preserves->-for-nonnegatives-1
			       (y2 x)
			       (y1 (* y1 y2))
			       (x2 1)
			       (x1 (/ y2))))
	      :in-theory (disable *-preserves->-for-nonnegatives-1)))))
  (local
   (defthm case-1
       (implies (and (realp x)
		     (realp y)
		     (<= 0 x)
		     (< x y)
		     (< y (/ (acl2-pi) 2)))
		(< (acl2-cosine y)
		   (acl2-cosine x)))
     :hints (("goal"
	      :use ((:instance lemma-1-2)
		    (:instance lemma-1-3
			       (x (acl2-cosine y))
			       (y1 (acl2-cosine x))
			       (y2 (acl2-cosine (- y x))))
		    (:instance cosine-positive-in-0-pi/2 (x y))
		    (:instance cosine-positive-in-0-pi/2 (x (- y x)))
		    (:instance sine-positive-in-0-pi/2 (x (- y x)))
		    (:instance cosine-<-1-if-sine-non-0 (x (- y x))))
	      :in-theory (disable lemma-1-2
				  lemma-1-3
				  cosine-positive-in-0-pi/2
				  sine-positive-in-0-pi/2
				  cosine-<-1-if-sine-non-0
				  cosine-of-sums
				  sine-of-sums)))))
  (local
   (defthm case-2
       (implies (and (realp x)
		     (realp y)
		     (< (/ (acl2-pi) 2) x)
		     (< x y)
		     (<= y (acl2-pi)))
		(< (acl2-cosine y)
		   (acl2-cosine x)))
     :hints (("goal"
	      :use ((:instance case-1
			       (x (- (acl2-pi) y))
			       (y (- (acl2-pi) x))))
	      :in-theory (disable case-1
				  cosine-of-sums)))))
  (local
   (defthm lemma-3-1
       (equal (acl2-cosine (* 1/2 (acl2-pi))) 0)))
  (local
   (defthm case-3
       (implies (and (realp x)
		     (realp y)
		     (<= 0 x)
		     (<= x (/ (acl2-pi) 2))
		     (< (/ (acl2-pi) 2) y)
		     (<= y (acl2-pi)))
		(< (acl2-cosine y)
		   (acl2-cosine x)))
     :hints (("goal"
	      :use ((:instance cosine-positive-in-0-pi/2)
		    (:instance cosine-negative-in-pi/2-pi (x y)))
	      :in-theory (disable cosine-positive-in-0-pi/2
				  cosine-negative-in-pi/2-pi)))))
  (local
   (defthm case-4
       (implies (and (realp x)
		     (realp y)
		     (<= 0 x)
		     (< x y)
		     (= y (/ (acl2-pi) 2)))
		(< (acl2-cosine y)
		   (acl2-cosine x)))
     :hints (("goal"
	      :use ((:instance cosine-positive-in-0-pi/2))
	      :in-theory (disable cosine-positive-in-0-pi/2)))))
  (defthm cosine-is-decreasing-on-0-pi
      (implies (and (realp x)
		    (realp y)
		    (<= 0 x)
		    (< x y)
		    (<= y (acl2-pi)))
	       (< (acl2-cosine y)
		  (acl2-cosine x)))
    :hints (("goal"
	     :use ((:instance case-1)
		   (:instance case-2)
		   (:instance case-3)
		   (:instance case-4))
	     :in-theory (disable case-1
				 case-2
				 case-3
				 case-4))))
  ))

(local
 (defthm cosine-is-1-1-on-0-pi
     (implies (and (realp x)
		   (realp y)
		   (<= 0 x)
		   (<= x (acl2-pi))
		   (<= 0 y)
		   (<= y (acl2-pi))
		   (not (equal x y)))
	      (not (equal (acl2-cosine x)
			  (acl2-cosine y))))
   :hints (("Goal"
	    :cases ((< x y) (< y x)))
	   ("Subgoal 2"
	    :use ((:instance cosine-is-decreasing-on-0-pi))
	    :in-theory (disable cosine-is-decreasing-on-0-pi))
	   ("Subgoal 1"
	    :use ((:instance cosine-is-decreasing-on-0-pi (x y) (y x)))
	    :in-theory (disable cosine-is-decreasing-on-0-pi)))))

(local
 (defthm cosine-is-1-1-on-domain-builtin
     (IMPLIES (AND (INSIDE-INTERVAL-P X1 (INTERVAL 0 (ACL2-PI)))
		   (INSIDE-INTERVAL-P X2 (INTERVAL 0 (ACL2-PI)))
		   (EQUAL (ACL2-COSINE X1)
			  (ACL2-COSINE X2)))
	      (EQUAL X1 X2))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause)))

(defthm cosine-is-1-1-on-domain
    (IMPLIES (AND (INSIDE-INTERVAL-P X1 (INTERVAL 0 (ACL2-PI)))
		  (INSIDE-INTERVAL-P X2 (INTERVAL 0 (ACL2-PI)))
		  (EQUAL (ACL2-COSINE X1)
			 (ACL2-COSINE X2)))
	     (EQUAL X1 X2))
  :rule-classes nil)


(defthm cosine-lemma-1
    (IMPLIES (INSIDE-INTERVAL-P X (INTERVAL 0 (ACL2-PI)))
	     (INSIDE-INTERVAL-P (ACL2-COSINE X)
				(INTERVAL -1 1)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause))

(local
 (defthm sine-is-1-1-on--pi/2-pi/2
     (implies (and (realp x)
		   (realp y)
		   (<= (- (/ (acl2-pi) 2)) x)
		   (<= x (/ (acl2-pi) 2))
		   (<= (- (/ (acl2-pi) 2)) y)
		   (<= y (/ (acl2-pi) 2))
		   (not (equal x y)))
	      (not (equal (acl2-sine x)
			  (acl2-sine y))))
   :hints (("Goal"
	    :use ((:instance cosine-is-1-1-on-0-pi
			     (x (+ (* 1/2 (acl2-pi)) (- x)))
			     (y (+ (* 1/2 (acl2-pi)) (- y))))
		  (:instance cos-pi/2-x (x x))
		  (:instance cos-pi/2-x (x y)))
	    :in-theory (disable cosine-is-1-1-on-0-pi cos-pi/2-x)))))

(local
 (defthm sine-is-1-1-on-domain
     (IMPLIES (AND (INSIDE-INTERVAL-P X1
				      (INTERVAL (- (* 1/2 (ACL2-PI)))
						(* 1/2 (ACL2-PI))))
		   (INSIDE-INTERVAL-P X2
				      (INTERVAL (- (* 1/2 (ACL2-PI)))
						(* 1/2 (ACL2-PI))))
		   (EQUAL (ACL2-SINE X1) (ACL2-SINE X2)))
	      (EQUAL X1 X2))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause)))



(local
 (defthm sine-bound
     (implies (realp x)
	      (and (<= -1 (acl2-sine x))
		   (<= (acl2-sine x) 1)))
   :hints (("Goal"
	    :use ((:instance cosine-bound
			     (x (+ (* 1/2 (acl2-pi)) (- x))))
		  (:instance cos-pi/2-x (x x)))
	    :in-theory (disable cosine-bound cos-pi/2-x)))))

(local
 (defthm sine-lemma-1
     (IMPLIES (INSIDE-INTERVAL-P Y (INTERVAL -1 1))
	      (<= -1 Y))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))



(local
 (defthm sine-lemma-2
     (IMPLIES (INSIDE-INTERVAL-P Y (INTERVAL -1 1))
	      (<= Y 1))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(defthm sine-lemma-3
    (IMPLIES (INSIDE-INTERVAL-P X
				(INTERVAL (- (* 1/2 (ACL2-PI)))
					  (* 1/2 (ACL2-PI))))
	     (INSIDE-INTERVAL-P (ACL2-SINE X)
				(INTERVAL -1 1)))
  :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))
   :rule-classes (:built-in-clause))

(defun real-cosine (x)
  (acl2-cosine (realfix x)))

(defun real-sine (x)
  (acl2-sine (realfix x)))

(definv real-cosine
    :f-inverse        acl2-acos
    :domain           (interval 0 (acl2-pi))
    :range            (interval -1 1)
    :inverse-interval cosine-interval)

(definv real-sine
    :f-inverse        acl2-asin
    :domain           (interval (* -1/2 (acl2-pi)) (* 1/2 (acl2-pi)))
    :range            (interval -1 1)
    :inverse-interval sine-interval)

(defthm sine-inverts-asin
  (implies (and (realp x)
                (<= -1 x)
                (<= x 1))
           (equal (acl2-sine (acl2-asin x))
                  x))
  :hints (("Goal" :use (:instance acl2-asin-exists (y x))
           :in-theory (enable inside-interval-p))))

(defthm cosine-inverts-acos
  (implies (and (realp x)
                (<= -1 x)
                (<= x 1))
           (equal (acl2-cosine (acl2-acos x))
                  x))
  :hints (("Goal" :use (:instance acl2-acos-exists (y x))
           :in-theory (enable inside-interval-p))))

; Trying to prove that acl2-asin is continuous
(local
 (defthm-std acl2-sine-standard
   (implies (standardp x)
            (standardp (acl2-sine x)))))

(local
 (defthm-std acl2-cosine-standard
   (implies (standardp x)
            (standardp (acl2-cosine x)))))

(local
 (defthm acl2-sine-standard-part-out
   (implies (and (realp x)
                 (i-limited x))
            (equal (acl2-sine (standard-part x))
                   (standard-part (acl2-sine  x))))
   :hints (("Goal"
            :in-theory (enable-disable (i-close i-small)
                                       (sine-continuous ))
            :use (:instance sine-continuous
                            (x (standard-part x))
                            (y x))))))

(local
 (defthm acl2-cosine-standard-part-out
   (implies (and (realp x)
                 (i-limited x))
            (equal (acl2-cosine (standard-part x))
                   (standard-part (acl2-cosine  x))))
   :hints (("Goal"
            :in-theory (enable-disable (i-close i-small)
                                       (cosine-continuous ))
            :use (:instance cosine-continuous
                            (x (standard-part x))
                            (y x))))))

(defthm acl2-asin-limited
  (implies (inside-interval-p x (interval -1 1))
           (i-limited (acl2-asin x)))
  :hints (("Goal"
           :in-theory (enable inside-interval-p)
           :use ((:instance acl2-asin-exists (y x))
                 (:instance limited-squeeze
                            (a (- (/ (ACL2-PI) 2)))
                            (b (/ (ACL2-PI) 2))
                            (x (acl2-asin x)))
                 (:instance standards-are-limited
                            (x (acl2-pi)))))))

(defthm acl2-acos-limited
  (implies (inside-interval-p x (interval -1 1))
           (i-limited (acl2-acos x)))
  :hints (("Goal"
           :in-theory (enable inside-interval-p)
           :use ((:instance acl2-acos-exists (y x))
                 (:instance limited-squeeze
                            (a 0)
                            (b (ACL2-PI))
                            (x (acl2-acos x)))
                 (:instance standards-are-limited
                            (x (acl2-pi)))))))

(local
 (defthm standard-part-still-inside-interval
   (implies (and (standardp a) (realp a)
                 (standardp b) (realp b)
                 (i-limited x)
                 (inside-interval-p x (INTERVAL a b))
                 )
            (inside-interval-p (standard-part x) (interval a b)))
   :hints (("Goal" :in-theory (enable inside-interval-p)
            :use ((:instance standard-part-<= (x x) (y b))
                  (:instance standard-part-<= (x a) (y x)))))))

(local
 (defthm standard-part-asin-in-interval
   (implies (inside-interval-p x (interval -1 1))
            (inside-interval-p (standard-part (acl2-asin x))
                               (INTERVAL (- (* 1/2 (ACL2-PI)))
                                         (* 1/2 (ACL2-PI)))))
   :hints (("Goal"
            :use (:instance acl2-asin-exists (y x))))))

(local
 (defthm standard-part-acos-in-interval
   (implies (inside-interval-p x (interval -1 1))
            (inside-interval-p (standard-part (acl2-acos x))
                               (INTERVAL 0
                                         (ACL2-PI))))
   :hints (("Goal"
            :use (:instance acl2-acos-exists (y x))))))

(local
 (defthm acl2-asin-continuous-lemma
   (implies (and (inside-interval-p x (interval -1 1))
                 (inside-interval-p y (interval -1 1))
                 (i-close x y)
                 (syntaxp (not (equal x y))) ; avoid loop (Matt K., 5/2013)
                 )
            (equal (acl2-sine (standard-part (acl2-asin x)))
                   (acl2-sine (standard-part (acl2-asin y)))))
   :hints (("Goal" :in-theory (enable i-close i-small interval-definition-theory)
            ))))

(local
 (defthm acl2-acos-continuous-lemma
   (implies (and (inside-interval-p x (interval -1 1))
                 (inside-interval-p y (interval -1 1))
                 (i-close x y)
                 (syntaxp (not (equal x y))) ; avoid loop (Matt K., 5/2013)
                 )
            (equal (acl2-cosine (standard-part (acl2-acos x)))
                   (acl2-cosine (standard-part (acl2-acos y)))))
   :hints (("Goal" :in-theory (enable i-close i-small interval-definition-theory)
            ))))

(defthm acl2-asin-continuous
   (implies (and (inside-interval-p x (interval -1 1))
                 (inside-interval-p y (interval -1 1))
                 (i-close x y)

; Matt K., 5/2013:
; The following is reasonable based on the two uses of syntaxp just above to
; avoid a loop, though it isn't actually necessary in this case.

                (syntaxp (not (equal x y))) ; avoid potential loop
                )
            (i-close (acl2-asin x)
                     (acl2-asin y)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)
            :use ((:instance sine-is-1-1-on-domain
                             (x1 (standard-part (acl2-asin x)))
                             (x2 (standard-part (acl2-asin y))))
                  (:instance acl2-asin-continuous-lemma)))))


(defthm acl2-acos-continuous
   (implies (and (inside-interval-p x (interval -1 1))
                 (inside-interval-p y (interval -1 1))
                 (i-close x y)

; Matt K., 5/2013:
; The following is reasonable based on the two uses of syntaxp just above to
; avoid a loop, though it isn't actually necessary in this case.

                 (syntaxp (not (equal x y))) ; avoid potential loop
                 )
            (i-close (acl2-acos x)
                     (acl2-acos y)))
   :hints (("Goal"
            :in-theory (enable i-close i-small)
            :use ((:instance cosine-is-1-1-on-domain
                             (x1 (standard-part (acl2-acos x)))
                             (x2 (standard-part (acl2-acos y))))
                  (:instance acl2-acos-continuous-lemma)))))

(defthm pi/2-acos-=-asin
  (implies (inside-interval-p x (interval -1 1))
           (equal (- (/ (acl2-pi) 2) (acl2-acos x))
                  (acl2-asin x)))
  :hints (("Goal"
           :use ((:instance sine-is-1-1-on--pi/2-pi/2
                           (x (acl2-asin x))
                           (y (- (/ (acl2-pi) 2) (acl2-acos x))))
                 (:instance acl2-asin-exists (y x))
                 (:instance acl2-acos-exists (y x)))
           :in-theory (enable interval-definition-theory))))

(defun acl2-atan (x)
  (* (sign x)
     (acl2-acos (/ (acl2-sqrt (+ 1 (* x x)))))))

; Goal: Prove that atan(tan(x)) = x for x between -pi/2 and pi/2
(defthm cos-positive--pi/2-to-pi/2
  (implies (and (realp x)
                (< (- (/ (acl2-pi) 2)) x)
                (< x (/ (acl2-pi) 2)))
           (< 0 (acl2-cosine x)))
  :hints (("Goal"
           :cases ((= 0 x)
                   (< 0 x)
                   (> 0 x)))
          ("Subgoal 1"
           :use (:instance cosine-positive-in-0-pi/2 (x (- x))))))

; acos(cos(x)) works like absolute value for the xs we are interested in. This
; is why the (sign x) exists in the definition of atan.
(defthm acos-cos
  (implies (and (realp x)
                (<= (- (acl2-pi)) x)
                (<= x (acl2-pi)))
           (equal (acl2-acos (acl2-cosine x))
                  (abs x)))
  :hints (("Goal"
           :cases ((<= 0 x)
                   (< x 0)))
          ("Subgoal 2"
           :use (:instance acl2-acos-inverse-exists (x x))
           :in-theory (enable interval-definition-theory))
          ("Subgoal 1"
           :in-theory (enable abs interval-definition-theory)
           :use (:instance acl2-acos-inverse-exists (x (- x))))))

; Taking the tangent preserves sign
(defthm acl2-tangent-sign
  (implies (and (realp x)
                (< (- (/ (acl2-pi) 2)) x)
                (< x (/ (acl2-pi) 2)))
           (equal (sign (acl2-tangent x))
                  (sign x)))
  :hints (("Goal" :in-theory (enable-disable (sign)
                                             (cos-positive--pi/2-to-pi/2))
           :use ((:instance cos-positive--pi/2-to-pi/2)
                 (:instance sine-positive-in-0-pi/2
                            (x x))
                 (:instance sine-positive-in-0-pi/2
                            (x (- x)))))))

; End of this goal: atan inverts tangent
(encapsulate
 nil
 (local
  (defthmd lemma-1
    (implies (< 0 (acl2-cosine x))
	     (equal (+ 1
		       (* (/ (ACL2-COSINE X))
			  (/ (ACL2-COSINE X))
			  (ACL2-SINE X)
			  (ACL2-SINE X)))
		    (/ (+ (* (acl2-cosine x) (acl2-cosine x))
			  (* (acl2-sine x) (acl2-sine x)))
		       (* (acl2-cosine x) (acl2-cosine x))))))
  )

 (defthm 1+sin^2/cos^x
    (implies (< 0 (acl2-cosine x))
	     (equal (+ 1
		       (* (/ (ACL2-COSINE X))
			  (/ (ACL2-COSINE X))
			  (ACL2-SINE X)
			  (ACL2-SINE X)))
		    (* (/ (acl2-cosine x)) (/ (acl2-cosine x)))))
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance sin**2+cos**2))
	     :in-theory (disable sin**2+cos**2))))
   )


(defthm atan-tangent
  (implies (and (realp x)
                (< (- (/ (acl2-pi) 2)) x)
                (< x (/ (acl2-pi) 2)))
           (equal (acl2-atan (acl2-tangent x))
                  x))
  :hints (("Goal" :use ((:instance  (:theorem
                                     (implies (equal x y)
                                              (equal (acl2-acos x) (acl2-acos y))))
                                    (x (acl2-sqrt (/ (+ 1 (* (acl2-tangent x)
                                                             (acl2-tangent x))))))
                                    (y (acl2-cosine x)))
                        (:instance acl2-tangent-sign)
                        (:instance sin**2+cos**2)
                        (:instance cos-positive--pi/2-to-pi/2))
           :in-theory (enable-disable (abs sign)
                                      (SIGN-*-X-Y
                                       sin**2+cos**2
                                       cos-positive--pi/2-to-pi/2)))))

; Next goal: prove that the range of atan(x) is (-pi/2, pi/2)

; Start by showing that cosine in nonincreasing. This is useful for
; establishing a bound on acos.
(defthm cosine-is-nonincreasing-on-0-pi
  (implies (and (realp x)
                (realp y)
                (<= 0 x)
                (<= x y)
                (<= y (acl2-pi)))
           (<= (acl2-cosine y)
               (acl2-cosine x)))
  :hints (("Goal"
           :cases ((= x y)
                   (< x y)))
          ("Subgoal 1"
           :in-theory (disable cosine-is-decreasing-on-0-pi)
           :use (:instance cosine-is-decreasing-on-0-pi))))

; For values between 0 and 1, acos gives an angle in the first quadrant.
(defthm acos-for-quadrant-1
  (implies (and (realp x)
                (<= x 1)
                (< 0 x))
           (< (acl2-acos x) (/ (acl2-pi) 2)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)
           :use ((:instance acl2-acos-exists (y x))
                 (:instance cosine-is-nonincreasing-on-0-pi
                           (y (acl2-acos x))
                           (x (/ (acl2-pi) 2)))))))

; For values between 0 and 1, acos gives an angle in the first quadrant.
(defthm acos-for-quadrant-1
  (implies (and (realp x)
                (<= x 1)
                (< 0 x))
           (< (acl2-acos x) (/ (acl2-pi) 2)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)
           :use ((:instance acl2-acos-exists (y x))
                 (:instance cosine-is-nonincreasing-on-0-pi
                           (y (acl2-acos x))
                           (x (/ (acl2-pi) 2)))))))
; Ignoring the (sign x), atan is in [0, pi/2)
(local
 (defthm atan-sqrt-bounds
   (implies (realp x)
            (and (< (acl2-acos (/ (acl2-sqrt (+ 1 (* x x))))) (/ (acl2-pi) 2))
                 (<= 0 (acl2-acos (/ (acl2-sqrt (+ 1 (* x x))))))))
   :hints (("Goal" :use ((:instance acos-for-quadrant-1
                                    (x (/ (acl2-sqrt (+ 1 (* x x))))))
                         (:instance acl2-acos-exists
                                    (y (/ (acl2-sqrt (+ 1 (* x x)))))))
            :in-theory (enable interval-definition-theory)))))

; The [0, x) range turns into a (-x, x) range once the value is multiplied by
; (sign x).
(local
 (defthm sign-flippy
   (implies (and (realp x)
                 (realp y)
                 (realp z)
                 (<= 0 x)
                 (< x y))
            (and (< (* (sign z) x) y)
                 (< (- y) (* (sign z) x))))
   :hints (("Goal" :in-theory (enable sign)))))

; atan gives values in (-pi/2, pi/2)
(defthm atan-bounds
  (implies (realp x)
           (and (< (acl2-atan x) (/ (acl2-pi) 2))
                (< (- (/ (acl2-pi) 2)) (acl2-atan x))))
  :hints (("Goal"
           :use ((:instance sign-flippy
                            (x (acl2-acos (/ (acl2-sqrt (+ 1 (* x x))))))
                            (y (/ (acl2-pi) 2))
                            (z x))
                 (:instance atan-sqrt-bounds)))))

; lets try showing that acos decreases
(defthm acl2-acos-decreases
  (implies (and (< x y)
                (inside-interval-p x (interval -1 1))
                (inside-interval-p y (interval -1 1)))
           (< (acl2-acos y) (acl2-acos x)))
  :hints (("Goal"
           :in-theory (enable inside-interval-p)
           :use ((:instance cosine-is-nonincreasing-on-0-pi
                           (x (acl2-acos x))
                           (y (acl2-acos y)))
                 (:instance acl2-acos-exists
                            (y x))
                 (:instance acl2-acos-exists
                            (y y))))))

; The stuff inside atan's sqrt decreases for positive x
(defthm atan-sqrt-decreases
  (implies (and (realp x)
                (realp y)
                (< 0 x)
                (< x y))
           (< (/ (acl2-sqrt (+ 1 (* y y))))
              (/ (acl2-sqrt (+ 1 (* x x))))))
  :hints (("Goal" :use (:instance (:theorem
                                   (implies (and (realp x) (< 0 x)
                                                 (realp y) (< x y))
                                            (< (+ 1 x) (+ 1 y))))
                                  (x (* x x)) (y (* y y))))))


(defthm acl2-acos-1
  (equal (acl2-acos 1)
         0)
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)
           :use (:instance acl2-acos-inverse-exists
                                  (x 0)))))
(defthm acos-positive
  (implies (and (realp x)
                (<= -1 x)
                (< x 1))
           (< 0 (acl2-acos x)))
  :hints (("Goal"
           :in-theory (enable interval-definition-theory)
           :use ((:instance acl2-acos-exists (y x)
                            )
                 (:instance acl2-acos-is-1-to-1
                            (y1 x)
                            (y2 1))))))

(defthm atan-above-0
  (implies (and (realp x)
                (< 0 x))
           (< 0 (acl2-atan x)))
  :hints (("Goal" :in-theory (enable sign))))

(defthm atan-0
  (equal (acl2-atan 0)
         0)
  :hints (("Goal" :expand ((:free (x) (hide x))))))

(defthm atan-odd
  (implies (realp x)
           (equal (acl2-atan (- x))
                  (- (acl2-atan x)))))

(encapsulate
 nil

 (local
  (defthm atan-increases-positive
    (implies (and (realp x)
                  (realp y)
                  (<= 0 x)
                  (< x y))
             (< (acl2-atan x)
                (acl2-atan y)))
    :hints (("Goal"

             :expand ((:free (x) (hide x)))
             :in-theory (enable interval-definition-theory sign)
             :cases ((= x 0)
                     (< 0 x)))
            ("Subgoal 2"
             :use (:instance acl2-acos-decreases
                             (x (/ (acl2-sqrt (+ 1 (* y y)))))
                             (y (/ (acl2-sqrt (+ 1 (* x x))))))))))


 (local
  (defthm atan-increases-negative
    (implies (and (realp x)
                  (realp y)
                  (<= y 0)
                  (< x y))
             (< (acl2-atan x)
                (acl2-atan y)))
    :hints (("Goal" :in-theory (disable acl2-atan)
             :use (:instance atan-increases-positive (x (- y)) (y (- x)))))))

 (local
  (defthm atan-increases-switch
    (implies (and (realp x)
                  (realp y)
                  (< 0 y)
                  (< x 0))
             (< (acl2-atan x)
                (acl2-atan y)))
    :hints (("Goal"
             :use ((:instance atan-increases-negative (x x) (y 0))
                   (:instance atan-increases-positive (x 0) (y y)))
             :in-theory (disable acl2-atan)))))

 (defthm atan-increases
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (< (acl2-atan x) (acl2-atan y)))
   :hints (("Goal"
            :cases ((<= 0 x)
                    (<= y 0)
                    (and (< 0 y)
                         (< x 0)))
            :in-theory (disable acl2-atan)))))

(defthm acl2-atan-is-1-to-1
  (implies (and (realp x)
                (realp y)
                (equal (acl2-atan x) (acl2-atan y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :cases ((< x y)
                          (< y x)
                          (= x y))
           :in-theory (disable acl2-atan atan-increases)
           :use ((:instance atan-increases (x x) (y y))
                 (:instance atan-increases (x y) (y x))))))

(defthm tangent-atan
  (implies (realp x)
           (equal (acl2-tangent (acl2-atan x)) x))
  :hints (("Goal"
           :in-theory (disable acl2-atan)
           :use ((:instance atan-bounds)
                 (:instance atan-tangent
                            (x (acl2-atan x)))
                 (:instance acl2-atan-is-1-to-1
                           (x (acl2-tangent (acl2-atan x)))
                           (y x))))))

(local
 (defthm sqrt-1+x*x-not-small
   (implies (realp x)
            (not (i-small (acl2-sqrt (+ 1 (* x x))))))
   :hints (("Goal" :in-theory (enable i-small)
            :use (:instance standard-part-<=
                            (x 1)
                            (y (acl2-sqrt (+ 1 (* x x)))))))))

(defthm sqrt-continuous
  (implies (and (realp x) (realp y)
                (<= 0 x) (<= 0 y)
                (i-close x y))
           (i-close (acl2-sqrt x) (acl2-sqrt y)))
  :hints (("Goal" :use (:instance squares-close
                                  (x (acl2-sqrt x))
                                  (y (acl2-sqrt y))))))


(local
 (defthm 1+x*x-continuous
   (implies (and
             (i-limited x)
             (i-limited y)
             (i-close x y))
            (i-close (+ 1 (* x x)) (+ 1 (* y y))))
   :hints (("Goal"
            :in-theory (enable i-close i-small)))))

(defthm atan-continous-positive
  (implies (and (realp x)
                (realp y)
                (i-limited x)
                (i-limited y)
                (< 0 x)
                (< 0 y)
                (i-close x y))
           (i-close (acl2-atan x)
                    (acl2-atan y)))
  :hints (("Goal" :in-theory (enable sign interval-definition-theory))))

(local
(defthm atan-continuous-negative
  (implies (and (realp x) (i-limited x) (< x 0)
                (realp y) (i-limited y) (< y 0)
                (i-close x y))
           (i-close (acl2-atan x)
                    (acl2-atan y)))
  :hints (("Goal" :in-theory (enable sign interval-definition-theory)))))

(local
(defthm sign-*-small
  (implies (i-close x 0)
           (i-close (* (sign y) x) 0))
  :hints (("Goal" :in-theory (enable i-close sign)))))

(local
 (defthm atan-continuous-zero
  (implies (and (realp x) (i-small x))
           (i-close (acl2-atan x)
                     0))
  :hints (("Goal"
           :in-theory (enable sign interval-definition-theory)
           :use ((:instance sign-*-small
                            (y x)
                            (x (acl2-acos (/ (ACL2-SQRT (+ 1 (* X X)))))))
                 (:instance close-/
                           (x (ACL2-SQRT (+ 1 (* X X))))
                           (y 1))
                 (:instance acl2-acos-continuous
                            (x (/ (ACL2-SQRT (+ 1 (* X X)))));x)
                            (y 1)))
           :expand ((:free (x) (hide x)))))))

(local
(defthm small-if-close-across-0
  (implies (and (realp x) (realp y)
                (<= x 0)
                (<= 0 y)
                (i-close x y))
           (i-small x))
  :hints (("Goal" :in-theory (enable i-close i-small)
           :use ((:instance standard-part-<=
                           (x x) (y 0))
                 (:instance standard-part-<=
                            (x 0) (y y)))))))

(defthm acl2-atan-continuous
  (implies (and (realp x) (realp y) (i-limited x)
                (i-close x y))
           (i-close (acl2-atan x) (acl2-atan y)))
  :hints (("Goal"
           :in-theory (disable acl2-atan)
           :cases ((and (< 0 x) (< 0 y))
                   (and (< x 0) (< y 0))
                   (i-small x)))
          ("Subgoal 4"
           :use (:instance small-if-close-across-0 (x y) (y x)))
          ("Subgoal 3"
           :use (:instance atan-continous-positive))
          ("Subgoal 2"
           :use (:instance atan-continuous-negative))
          ("Subgoal 1"
           :in-theory (disable ATAN-CONTINUOUS-ZERO)
           :use ((:instance atan-continuous-zero
                           (x x))
                 (:instance atan-continuous-zero
                            (x y))))))

(in-theory (disable acl2-atan))

(defthm pi-limited
  (i-limited (acl2-pi))
  :hints (("Goal" :use (:instance standards-are-limited
                                  (x (acl2-pi))))))

(defthm acl2-atan-limited
  (implies (realp x)
           (i-limited (acl2-atan x)))
  :hints (("Goal" :use ((:instance limited-squeeze
                                  (a (- (/ (acl2-pi) 2)))
                                  (b (/ (acl2-pi) 2))
                                  (x (acl2-atan x)))
                        (:instance atan-bounds (x x)))))
  :rule-classes (:rewrite :type-prescription))

(defthm cosine-atan
  (implies (realp x)
           (equal (acl2-cosine (acl2-atan x))
                  (/ (acl2-sqrt (+ 1 (* x x))))))
  :hints (("Goal" :in-theory (enable acl2-atan sign)
           :cases ((= x 0) (not (= x 0)))
           :expand ((:free (x) (hide x))))))

(defthm-std acl2-atan-standard
  (implies (standardp x)
           (standardp (acl2-atan x))))
