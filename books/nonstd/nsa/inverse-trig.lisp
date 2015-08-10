(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "inverse-monotone")
(include-book "trig")

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
 )

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

