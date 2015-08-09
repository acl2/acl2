(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "inverse-monotone")
(include-book "exp")
(include-book "complex-polar")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(in-theory (enable acl2-exp))

(defthm real-sumlist-exp-list
  (implies (realp x)
           (realp (sumlist (taylor-exp-list n i x)))))

(defthm realp-standard-part
  (implies (realp x)
           (realp (standard-part x))))

(defthm realp-standard-part
  (implies (realp x)
           (realp (standard-part x))))

(defthm-std realp-exp
  (implies (realp x)
           (realp (acl2-exp x))))
(defthm-std standard-exp
  (implies (standardp x)
           (standardp (acl2-exp x))))
(defthm expt-is-non-decreasing-for-non-negatives
   (implies (and (realp x)
                 (realp y)
                 (<= 0 x)
                 (<= x y)
                 (integerp n)
                 (<= 0 n))
            (<= (expt x n) (expt y n))))

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (realp x1)
                  (realp x2)
                  (realp y1)
                  (realp y2)
                  (<= x1 x2)
                  (<= y1 y2))
             (<= (+ x1 y1) (+ x2 y2)))))

 (defthm taylor-exp-is-non-decreasing-for-non-negatives
   (implies (and (realp x)
                 (realp y)
                 (<= 0 x)
                 (< x y))
            (<= (sumlist (taylor-exp-list n i x))
                (sumlist (taylor-exp-list n i y)))))
 )

(defthm-std acl2-exp-is-non-decreasing-for-non-negatives
  (implies (and (realp x)
                (realp y)
                (<= 0 x)
                (< x y))
           (<= (acl2-exp x) (acl2-exp y))))
(encapsulate
 ()

 (local
  (defthm taylor-exp-list-0
    (equal (sumlist (taylor-exp-list nterms counter 0))
           (if (or (zp nterms)
                   (not (equal counter 0)))
               0
             1))))

 (defthm exp-0
   (equal (acl2-exp 0) 1)))

(defthm acl2-exp---x
  (equal (acl2-exp (- x))
         (/ (acl2-exp (fix x))))
  :hints (("Goal"
           :use ((:instance exp-sum
                            (x x)
                            (y (- x)))
                 (:instance exp-0)
                 (:instance Uniqueness-of-*-inverses
                            (x (acl2-exp x))
                            (y (acl2-exp (- x)))))
           :in-theory (disable exp-sum
                               exp-0
                               Uniqueness-of-*-inverses))))

(encapsulate
 ()

 (local
  (defthm taylor-exp->=-0-for-non-negatives
    (implies (and (realp x)
                  (<= 0 x))
             (<= 0 (sumlist (taylor-exp-list n i x))))))

 (local
  (defthm taylor-exp->-1-for-non-negatives-lemma
    (implies (and (realp x)
                  (<= 0 x)
                  (integerp n)
                  (< 1 n))
             (<= (+ 1 x) (sumlist (taylor-exp-list n 0 x))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((taylor-exp-list n 0 x)))
            ("Goal'"
             :do-not-induct t
             :expand ((taylor-exp-list (+ -1 n) 1 x)))
            ("Goal''"
             :do-not-induct t
             :use ((:instance taylor-exp->=-0-for-non-negatives
                              (n (+ -2 n))
                              (i 2)))
             :in-theory (disable taylor-exp->=-0-for-non-negatives)))))

 (defthm-std acl2-exp->-1-for-non-negatives-lemma
   (implies (and (realp x)
                 (<= 0 x))
            (<= (+ 1 x) (acl2-exp x)))
   :hints (("Goal"
            :use ((:instance standard-part-<=
                             (x (+ 1 x))
                             (y (sumlist (taylor-exp-list (i-large-integer) 0 x))))
                  (:instance taylor-exp->-1-for-non-negatives-lemma
                             (n (i-large-integer)))
                  (:instance large->-non-large
                             (x (i-large-integer))
                             (y 1)))
            :in-theory (disable standard-part-<=
                                taylor-exp->-1-for-non-negatives-lemma
                                large->-non-large))))

  (defthm acl2-exp->-1-for-positives
    (implies (and (realp x)
                  (< 0 x))
             (< 1 (acl2-exp x)))
    :hints (("Goal"
             :use ((:instance acl2-exp->-1-for-non-negatives-lemma))
             :in-theory (disable acl2-exp->-1-for-non-negatives-lemma
                                 acl2-exp))))

  )

(defthm acl2-exp->-0-for-reals
  (implies (realp x)
           (< 0 (acl2-exp x)))
  :hints (("Goal"
           :cases ((< 0 x) (= 0 x) (< x 0)))
          ("Subgoal 3"
           :use ((:instance acl2-exp->-1-for-positives))
           :in-theory (disable acl2-exp->-1-for-positives))
          ("Subgoal 1"
           :use ((:instance acl2-exp---x)
		 (:instance exp-sum (x x) (y (- x)))
                 (:instance acl2-exp->-1-for-positives (x (- x)))
		 (:instance REALP-EXP (x (- x)))
                 (:instance
                  (:theorem (implies (and (equal 1 (* a b))
                                          (< 0 b)
                                          (realp a)
                                          (realp b))
                                     (< 0 a)))
                  (a (acl2-exp x))
                  (b (acl2-exp (- x)))))
           :in-theory (disable acl2-exp---x
			       REALP-EXP
			       exp-sum
                               acl2-exp->-1-for-positives
			       (:type-prescription acl2-exp)))))
(defthm acl2-exp-x-never-zero
  (implies (acl2-numberp x)
           (not (equal (acl2-exp x) 0)))
  :hints (("Goal"
           :use ((:instance exp-sum
                            (x (- x))
                            (y x))
                 (:instance exp-0)
                 (:instance Uniqueness-of-*-inverses
                            (x (acl2-exp x))
                            (y (acl2-exp (- x)))))
           :in-theory (disable exp-sum
                               exp-0
                               Uniqueness-of-*-inverses))))

(defthm acl2-exp-is-non-decreasing-for-non-positives
  (implies (and (realp x)
                (realp y)
                (< x y)
                (<= y 0))
           (<= (acl2-exp x) (acl2-exp y)))
  :hints (("Goal"
           :use ((:instance acl2-exp-is-non-decreasing-for-non-negatives
                            (x (- y))
                            (y (- x)))
                 (:instance /-inverts-weak-order
                            (x (acl2-exp (- y)))
                            (y (acl2-exp (- x)))))
           :in-theory (disable acl2-exp-is-non-decreasing-for-non-negatives
                               /-inverts-weak-order
                               equal-/))))

(defthm acl2-exp-is-non-decreasing
  (implies (and (realp x)
                (realp y)
                (< x y))
           (<= (acl2-exp x) (acl2-exp y)))
  :hints (("Goal"
           :cases ((<= y 0)
                   (and (< x 0) (< 0 y))
                   (<= 0 x)))
          ("Subgoal 2"
           :use ((:instance acl2-exp-is-non-decreasing-for-non-positives
                            (x x)
                            (y 0))
                 (:instance acl2-exp-is-non-decreasing-for-non-negatives
                            (x 0)
                            (y y)))
           :in-theory (disable acl2-exp-is-non-decreasing-for-non-positives
                               acl2-exp-is-non-decreasing-for-non-negatives))))


(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (realp x)
                  (realp y)
                  (< x y))
             (not (equal (acl2-exp x)
                         (acl2-exp y))))
    :hints (("Goal"
             :use ((:instance exp-sum
                              (x x)
                              (y (- y x)))
                   (:instance equal-*-x-y-x
                              (x (acl2-exp x))
                              (y (acl2-exp (- y x))))
                   (:instance acl2-exp->-1-for-positives
                              (x (- y x))))
             :in-theory (disable exp-sum
                                 equal-*-x-y-x
                                 acl2-exp->-0-for-reals)))))

 (defthm acl2-exp-is-1-1
    (implies (and (realp x)
                  (realp y)
                  (not (equal x y)))
             (not (equal (acl2-exp x)
                         (acl2-exp y))))
    :hints (("Goal"
             :cases ((< x y) (= x y) (< y x)))
            ("Subgoal 1"
             :use ((:instance lemma-1 (x y) (y x)))
             :in-theory (disable lemma-1))))
 )
(defthm acl2-exp-is-increasing
  (implies (and (realp x)
                (realp y)
                (< x y))
           (< (acl2-exp x) (acl2-exp y)))
  :hints (("Goal"
           :use ((:instance acl2-exp-is-non-decreasing)
                 (:instance acl2-exp-is-1-1))
           :in-theory (disable acl2-exp-is-non-decreasing
                               acl2-exp-is-1-1))))

(defthm acl2-exp->=-1-for-non-negatives
    (implies (and (realp x)
                  (<= 0 x))
             (<= 1 (acl2-exp x)))
  :hints (("Goal"
	   :use ((:instance acl2-exp->-1-for-positives)
		 (:instance exp-0))
	   :in-theory (disable acl2-exp->-1-for-positives
			       exp-0))))

(defthm acl2-exp-x->=-x-for-x->=-1
  (implies (and (realp x)
                (<= 1 x))
           (<= x (acl2-exp x)))
  :hints (("Goal"
           :use ((:instance acl2-exp->-1-for-non-negatives-lemma))
           :in-theory (disable acl2-exp->-1-for-non-negatives-lemma))))

(in-theory (disable acl2-exp))

(defun pos-exp (x)
  (acl2-exp (realfix x)))

(defun real->=-1 (x)
  (and (realp x)
       (<= 1 x)))
(defun exp-interval (x)
  (interval 0 x))

(local
 (defthm exp-lemma-1
     (IMPLIES (INSIDE-INTERVAL-P Y (INTERVAL 1 NIL))
         (INTERVAL-P (INTERVAL 0 Y)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm exp-lemma-2
     (IMPLIES (INSIDE-INTERVAL-P Y (INTERVAL 1 NIL))
	      (SUBINTERVAL-P (INTERVAL 0 Y)
			     (INTERVAL 0 NIL)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))


(local
 (defthm exp-lemma-3
     (IMPLIES (AND (INSIDE-INTERVAL-P Y (INTERVAL 1 NIL))
		   (< Y 1))
	      (<= (ACL2-EXP Y) Y))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(local
 (defthm exp-lemma-4
     (IMPLIES (INSIDE-INTERVAL-P X (INTERVAL 0 NIL))
	      (INSIDE-INTERVAL-P (ACL2-EXP X)
				 (INTERVAL 1 NIL)))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))

(definv pos-exp
    :domain           (interval 0 nil)
    :range            (interval 1 nil)
    :inverse-interval exp-interval)

(defun acl2-ln-for-positive (y)
  (if (< y 1)
      (- (pos-exp-inverse (/ y)))
    (pos-exp-inverse y)))

(defthm acl2-exp-ln-for-positive
  (implies (and (realp y)
                (< 0 y))
           (and (realp (acl2-ln-for-positive y))
                (equal (acl2-exp (acl2-ln-for-positive y)) y)))
  :hints (("Goal"
	   :use ((:instance pos-exp-inverse-exists (y (/ y)))
		 (:instance pos-exp-inverse-exists (y y)))
	   :in-theory (enable-disable (interval-definition-theory) (pos-exp-inverse-exists))))
  )

(defthm realp-ln-for-positive
    (implies (and (realp x)
		  (< 0 x))
	     (realp (acl2-ln-for-positive x)))
  :hints (("Goal"
	   :use ((:instance pos-exp-inverse-exists (y x))
		 (:instance pos-exp-inverse-exists (y (/ x))))
	   :in-theory (enable-disable (interval-definition-theory) (pos-exp-inverse-exists)))))

(defthm ln-for-positive-exp
  (implies (realp x)
           (equal (acl2-ln-for-positive (acl2-exp x))
                  x))
  :hints (("Goal"
           :use ((:instance acl2-exp-is-1-1
			    (x x)
			    (y (acl2-ln-for-positive (acl2-exp  x))))
		 (:instance acl2-exp-ln-for-positive
			    (y (acl2-exp x))))
           :in-theory (disable acl2-exp-is-1-1
			       acl2-exp-ln-for-positive
			       acl2-ln-for-positive))))

(defthm uniqueness-of-ln-for-positive
  (implies (and (realp x)
                (equal (acl2-exp x) y))
           (equal (acl2-ln-for-positive y) x)))

(in-theory (disable acl2-ln-for-positive (acl2-ln-for-positive)))
(defun acl2-ln (y)
  (complex (acl2-ln-for-positive (radiuspart y))
           (anglepart y)))

(defthm realp-ln
  (implies (and (realp y)
                (< 0 y))
           (realp (acl2-ln y))))

(defthm complex-0-b
  (implies (realp b)
           (equal (complex 0 b)
                  (* #c(0 1) b)))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x 0)
                            (y b))))))

(defthm exp-complex
  (implies (and (realp a)
                (realp b))
           (equal (acl2-exp (complex a b))
                  (* (acl2-exp a) (acl2-exp (complex 0 b)))))
  :hints (("Goal"
           :use ((:instance complex-definition (x a) (y b))
                 (:instance exp-sum
                            (x a)
                            (y (* #c(0 1) b))))
           :in-theory (disable exp-sum
                               e^ix-cos-i-sin))))

(defthm radiuspart-real-non-zero
  (implies (not (equal (fix y) 0))
           (and (realp (radiuspart y))
                (< 0 (radiuspart y))))
  :hints (("Goal"
           :use ((:instance radiuspart-is-zero-only-for-zero
                            (x y)))
           :in-theory (disable radiuspart
                               radiuspart-is-zero-only-for-zero)))
  :rule-classes (:type-prescription :rewrite))

(defthm real-ln-radiuspart
  (implies (not (equal (fix y) 0))
           (realp (acl2-ln-for-positive (radiuspart y))))
  :hints (("Goal"
           :in-theory (disable radiuspart))))

(defthm exp-ln
  (implies (not (equal (fix y) 0))
           (equal (acl2-exp (acl2-ln y)) y))
  :hints (("Goal"
           :in-theory (disable anglepart
                               radiuspart
                               e^ix-cos-i-sin))))

(local
 (defthm +-complex
   (implies (and (realp i) (realp j) (realp r) (realp s))
            (equal (+ (complex i j) (complex r s))
                   (complex (+ i r) (+ j s))))
   :hints (("Goal"
            :use ((:instance complex-definition (x i) (y j))
                  (:instance complex-definition (x r) (y s))
                  (:instance complex-definition (x (+ i r)) (y (+ j s))))))))

(local
 (encapsulate
  ()
  (local
   (defthm *-complex-lemma-1
     (implies (and (realp a) (realp b) (realp r) (realp s))
              (equal (* (complex a b) (complex r s))
                     (* (+ a (* #C(0 1) b)) (+ R (* #C(0 1) S)))))
     :hints (("Goal"
              :use ((:instance complex-definition (x a) (y b))
                    (:instance complex-definition (x r) (y s)))))))

  ;; ...the next step is to factor everything out, remembering that
  ;; i^2=-1....

  (local
   (defthm *-complex-lemma-2
     (implies (and (realp a) (realp b) (realp r) (realp s))
              (equal (complex (- (* a r) (* b s))
                              (+ (* a s) (* b r)))
                     (+ (+ (* a R) (- (* b S)))
                        (* #C(0 1) (+ (* a S) (* b R))))))
     :hints (("Goal"
              :use ((:instance complex-definition
                               (x (- (* a r) (* b s)))
                               (y (+ (* a s) (* b r)))))))))

  ;; And so now we can get a formula for the product of two complex
  ;; numbers.

  (defthm *-complex
    (implies (and (realp i) (realp j) (realp r) (realp s))
             (equal (* (complex i j) (complex r s))
                    (complex (- (* i r) (* j s))
                             (+ (* i s) (* j r)))))))
 )

(defthm radiuspart-*
  (equal (radiuspart (* x y))
         (* (radiuspart x) (radiuspart y)))
  )


(defthm abs-exp
  (implies (realp x)
           (equal (abs (acl2-exp x))
                  (acl2-exp x)))
  :hints (("Goal"
           :use ((:instance acl2-exp->-0-for-reals))
           :in-theory (enable-disable (abs) (acl2-exp->-0-for-reals)))))

(defthm imagpart-+
  (equal (imagpart (+ x y))
         (+ (imagpart x) (imagpart y))))

(defthm realpart-+
  (equal (realpart (+ x y))
         (+ (realpart x) (realpart y))))

(defthm realpart-of-real
  (implies (realp x)
           (equal (realpart x) x)))

(defthm realpart-of-imaginary
  (implies (realp x)
           (equal (realpart (* #c(0 1) x)) 0))
  :hints (("Goal"
           :use ((:instance complex-0-b
                            (b x)))
           :in-theory (disable complex-0-b))))

(defthm imagpart-of-imaginary
  (implies (realp x)
           (equal (imagpart (* #c(0 1) x)) x))
  :hints (("Goal"
           :use ((:instance complex-0-b
                            (b x)))
           :in-theory (disable complex-0-b))))

(defthm realpart-sine
  (implies (realp x)
           (equal (realpart (acl2-sine x))
                  (acl2-sine x))))

(defthm imagpart-sine
  (implies (realp x)
           (equal (imagpart (acl2-sine x))
                  0)))

(defthm realpart-cosine
  (implies (realp x)
           (equal (realpart (acl2-cosine x))
                  (acl2-cosine x))))

(defthm imagpart-cosine
  (implies (realp x)
           (equal (imagpart (acl2-cosine x))
                  0)))

(defthm radiuspart-e-i-theta
  (implies (realp theta)
           (equal (radiuspart (acl2-exp (* #c(0 1) theta)))
                  1))
  :hints (("Goal"
           :use ((:instance sin**2+cos**2
                            (x theta)))
           :in-theory (disable sin**2+cos**2)))
  )

(defthm sine->=-0-=>-x-<=-pi
  (implies (and (realp x)
                (<= 0 x)
                (< x (* (acl2-pi) 2))
                (<= 0 (acl2-sine x))
                )
           (<= x (acl2-pi)))
  :hints (("Goal"
           :use ((:instance sine-negative-in-pi-3pi/2)
                 (:instance sine-3pi/2)
                 (:instance sine-negative-in-3pi/2-2pi))
           :in-theory (disable sine-negative-in-pi-3pi/2
                               sine-3pi/2
                               sine-negative-in-3pi/2-2pi)))
  )

(defthm sine-<-0-=>-x->-pi
  (implies (and (realp x)
                (<= 0 x)
                (< (acl2-sine x) 0)
                )
           (< (acl2-pi) x))
  :hints (("Goal"
           :use ((:instance sine-0)
                 (:instance sine-positive-in-0-pi/2)
                 (:instance sine-pi/2)
                 (:instance sine-positive-in-pi/2-pi))
           :in-theory (disable sine-0
                               sine-positive-in-0-pi/2
                               sine-pi/2
                               sine-positive-in-pi/2-pi
                               sine-2x
                               sine-3x
                               <-*-/-LEFT
                               <-*-/-right))))

(local
 (defthm realp-cosine-inverse
     (implies (realp theta)
	      (realp (acl2-acos (acl2-cosine theta))))
   :hints (("Goal"
	    :use ((:instance acl2-acos-exists (y (acl2-cosine theta))))
	    :in-theory (enable-disable (interval-definition-theory)
				       (acl2-acos-exists))))))

(defthm anglepart-e-i-theta
  (implies (and (realp theta)
                (<= 0 theta)
                (< theta (* (acl2-pi) 2)))
           (equal (anglepart (acl2-exp (* #c(0 1) theta)))
                  theta))
  :hints (("Goal"
           :use ((:instance sin**2+cos**2
                            (x theta)))
           :in-theory (disable sin**2+cos**2))
          ("Subgoal 3"
           :use ((:instance complex-definition
                            (x (acl2-cosine theta))
                            (y (acl2-sine theta)))
                 (:instance complex-equal
                            (x1 (acl2-cosine theta))
                            (y1 (acl2-sine theta))
                            (x2 0)
                            (y2 0)))
           :in-theory (disable complex-equal
                               sin**2+cos**2))
          ("Subgoal 2"
           :use ((:instance sine->=-0-=>-x-<=-pi
                            (x theta))
		 (:instance acl2-acos-exists
                            (y (acl2-cosine theta)))
		 (:instance cosine-is-1-1-on-domain
			    (x1 theta)
			    (x2 (ACL2-ACOS (ACL2-COSINE THETA))))
		 )
           :in-theory (enable-disable (interval-definition-theory)
				      (sine->=-0-=>-x-<=-pi
				       acl2-acos-exists)))
          ("Subgoal 1"
           :use ((:instance sine-<-0-=>-x->-pi
                            (x theta))
		 (:instance acl2-acos-exists
                            (y (acl2-cosine (+ (* (acl2-pi) 2) (- theta)))))
		 (:instance cosine-is-1-1-on-domain
			    (x1 (+ (* (acl2-pi) 2) (- theta)))
			    (x2 (ACL2-ACOS (ACL2-COSINE (+ (* (acl2-pi) 2) (- theta)))))))
           :in-theory (enable-disable (interval-definition-theory)
				      (sine-<-0-=>-x->-pi
				       acl2-acos-exists
				       COS-2PI-X
				       COS-2PI+X)))))

(encapsulate
 ()

 (local
  (defthm realpart-*-real
   (implies (realp x)
            (equal (realpart (* x y))
                   (* x (realpart y))))
   :hints (("Goal"
            :use ((:instance *-complex
                             (i x)
                             (j 0)
                             (r (realpart y))
                             (s (imagpart y)))
                  (:instance realpart-complex
                             (x (* (realpart y) x))
                             (y (* (imagpart y) x))))
            :in-theory (disable *-complex
                                realpart-complex)))))

 (local
  (defthm *-real-complex
    (implies (and (realp x)
                  (realp r)
                  (realp s))
             (equal (* x (complex r s))
                    (complex (* r x) (* s x))))
    :hints (("Goal"
             :use ((:instance *-complex
                              (i x)
                              (j 0)))))))

 (local
  (defthm imagpart-*-real
   (implies (realp x)
            (equal (imagpart (* x y))
                   (* x (imagpart y))))
   :hints (("Goal"
            :use ((:instance *-complex
                             (i x)
                             (j 0)
                             (r (realpart y))
                             (s (imagpart y)))
                  (:instance IMAGPART-COMPLEX
                             (x (* (realpart y) x))
                             (y (* (imagpart y) x))))
            :in-theory (disable *-complex
                                imagpart-complex)))))

 (defthm anglepart-*-real
   (implies (and (realp x)
                 (< 0 x))
            (equal (anglepart (* x y))
                   (anglepart y)))))

(defthm acl2-ln-for-positive-product
    (implies (and (realp x)
		  (realp y)
		  (< 0 x)
		  (< 0 y))
	     (equal (acl2-ln-for-positive (* x y))
		    (+ (acl2-ln-for-positive x)
		       (acl2-ln-for-positive y))))
  :hints (("Goal"
	   :use ((:instance uniqueness-of-ln-for-positive
			    (x (+ (acl2-ln-for-positive x)
				  (acl2-ln-for-positive y)))
			    (y (* x y)))
		 (:instance exp-sum
			    (x (acl2-ln-for-positive x))
			    (y (acl2-ln-for-positive y)))
		 (:instance acl2-exp-ln-for-positive (y x))
		 (:instance acl2-exp-ln-for-positive (y y))


		 )
	   :in-theory (disable uniqueness-of-ln-for-positive exp-sum acl2-exp-ln-for-positive ACL2-LN-FOR-POSITIVE))))

(defthm ln-exp
  (implies (and (acl2-numberp x)
                (<= 0 (imagpart x))
                (< (imagpart x) (* 2 (acl2-pi))))
           (equal (acl2-ln (acl2-exp x))
                  x))
  :hints (("Goal"
	   :use ((:instance radiuspart-e-i-theta (theta (imagpart x))))
           :in-theory (disable anglepart
                               radiuspart
			       radiuspart-e-i-theta
                               e^ix-cos-i-sin))))

(defthm uniqueness-of-ln
  (implies (and (acl2-numberp x)
                (<= 0 (imagpart x))
                (< (imagpart x) (* 2 (acl2-pi)))
                (equal (acl2-exp x) y))
           (equal (acl2-ln y) x)))

(in-theory (disable acl2-ln (acl2-ln)))


