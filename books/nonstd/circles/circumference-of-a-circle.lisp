; Circumference of a circle
;
; Copyright (C) 2021 University of Wyoming
;
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "nonstd/arc-length/length-of-a-rectifiable-curve" :dir :system)

(encapsulate 
 ((rad() t))
 (local (defun rad() 1))
 (defthm rad-det
   (and (realp (rad))
	(standardp (rad))
	(>= (rad) 0)
	(i-limited (rad))
	)
   ))

(defun circle (x)
  (* (rad) (acl2-exp (* #c(0 1) x)))
  )

(defthm circle-equal
  (equal (circle x)
         (* (rad) (+ (acl2-cosine x) (* #c(0 1) (acl2-sine x))))
         )
  :hints (("Goal" :in-theory (enable acl2-sine acl2-cosine)))
  )



(defun circle-der(x)
  (* (rad) (complex (- (acl2-sine x)) (acl2-cosine x)))
  )



(defthm circle-der-equal
  (implies (realp x)
           (equal (circle-der x)
                  (* (rad) (+ (- (acl2-sine x)) (* #c(0 1) (acl2-cosine x))))
                  )
           )
  
  :hints (("Goal" 
           :use(:instance complex-definition (x (- (acl2-sine x))) (y (acl2-cosine x)))
           :in-theory (disable acl2-sine acl2-cosine)))
  )

(encapsulate
 ()
 
 (local
  (defthm lemma-1
    (equal (+ (- (/ a b) c) (* #c(0 1) (- (/ p b) r)))
	   (- (/ (+ a (* #c(0 1) p)) b) (+ c (* #c(0 1) r))) 
	   )
    ))
 
 (local
  (defthm lemma-2
    (implies (and (realp a)
		  (realp b)
		  (realp p)
		  (i-close (/ a b) c)
		  (i-close (/ p b) r))
	     (i-close (/ (+ a (* #c(0 1) p)) b) (+ c (* #c(0 1) r)))
	     )
    
    :hints (("Goal"
	     :use (
		   (:instance i-small-plus-lemma(x (/ a b)) (y c) )
		   (:instance i-small-plus-lemma(x (/ p b)) (y r) )
		   (:instance limited*small->small (y (- (/ p b) r)) (x #c(0 1)))
		   (:instance i-small-plus (x (- (/ a b) c)) (y (* #c(0 1) (- (/ p b) r))))
		   (:instance lemma-1 (a a) (b b) (c c) (p p) (r r) )
		   (:instance i-close-plus-lemma-2 (x (/ (+ a (* #c(0 1) p)) b)) (y (+ c (* #c(0 1) r))))
		   )
	     ))
    ))
 
 (local
  (defthm lemma-3
    (equal (+ (- a b) (* c (- d e))) (- (+ a (* c d)) (+ b (* c e)))
	   )
    ))
 
 (local
  (defthm lemma-4
    (equal (* d (/ (- a b) c)) (/ (- (* d a) (* d b)) c))
    ))
 
 
 (defthmd close-limited
   (implies (and (i-close x y)
		 (i-limited z))
	    (i-close (* z x) (* z y))
	    )
   
   :hints (("Goal"
	    :use (
		  (:instance i-small-plus-lemma(x x) (y y))
		  (:instance limited*small->small(x z) (y (- x y)))
		  (:instance distributivity (y x) (z y) (x z))
		  (:instance i-close-plus-lemma-2 (x (* z x)) (y (* z y)))
		  
		  )
	    ))
   )

 (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-minimal" :dir :system))

 (local
  (defderivative sin-eqn-deriv 
    (/ (- (acl2-exp (* #c(0 1) x))
	  (acl2-exp (* #c(0 -1) x)))
       #c(0 2))))


 (defthm acl2-sine-derivative
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (standardp x)
		 (i-close x y)
		 (not (equal x y)))
	    (i-close (/ (- (acl2-sine x) (acl2-sine y))
			(- x y))
		     (acl2-cosine x)))
   :hints (("Goal" :use (:instance sin-eqn-deriv)
	    :in-theory (enable acl2-sine acl2-cosine))))
 
 (local
  (defderivative cos-eqn-deriv 
    (/ (+ (ACL2-EXP (* #C(0 1) X))
	  (ACL2-EXP (* #C(0 -1) X)))
       2)))

 (defthm acl2-cosine-derivative
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (standardp x)
		 (i-close x y)
		 (not (equal x y)))
	    (i-close (/ (- (acl2-cosine x) (acl2-cosine y))
			(- x y))
		     (- (acl2-sine x))))
   :hints (("Goal" :use (:instance cos-eqn-deriv)
	    :in-theory (enable acl2-sine acl2-cosine))))
 
 (defthm circle-der-lemma
   (implies (and (standardp x)
		 (realp x)
		 (realp y)
		 (i-close x y)
		 (not (= x y))
		 )
	    (i-close (/ (- (circle x) (circle y)) (- x y)) (circle-der x))
	    )
   :hints (("Goal"
	    :use (
		  (:instance rad-det)
		  (:instance acl2-sine-derivative (x x) (y y) )
		  (:instance acl2-cosine-derivative (x x) (y y) )
		  (:instance lemma-2 
			     (a (- (acl2-cosine x) (acl2-cosine y))) 
			     (b (- x y)) 
			     (c (- (acl2-sine x))) 
			     (p (- (acl2-sine x) (acl2-sine y))) 
			     (r (acl2-cosine x)))
		  (:instance lemma-3 
			     (a (acl2-cosine x)) 
			     (b (acl2-cosine y)) 
			     (c #c(0 1)) 
			     (d (acl2-sine x)) (e (acl2-sine y))
			     )
		  (:instance close-limited 
			     (x (/ (- (+ (acl2-cosine x) (* #c(0 1) (acl2-sine x))) (+ (acl2-cosine y) (* #c(0 1) (acl2-sine y)))) (- x y)))
			     (y (+ (- (acl2-sine x)) (* #c(0 1) (acl2-cosine x))))
			     (z (rad))
			     )
		  (:instance lemma-4 
			     (a (+ (acl2-cosine x) (* #c(0 1) (acl2-sine x))))
			     (b (+ (acl2-cosine y) (* #c(0 1) (acl2-sine y))))
			     (c (- x y))
			     (d (rad))
			     )
		  
		  (:instance circle-equal (x x))
		  (:instance circle-equal (x y))
		  (:instance circle-der-equal (x x))
		  
		  )
	    :in-theory (disable circle circle-der)
	    ))
   )
 
 (local 
  (defthm lemma-6
    (implies(and (standardp x)
		 (realp x)
		 (realp y)
		 (i-close x y)
		 )
	    (i-close (- (acl2-sine x)) (- (acl2-sine y)))
	    )
    ))
 
 (local
  (defthm lemma-5
    (implies(and (standardp x)
		 (realp x)
		 (realp y)
		 (i-close x y)
		 )
	    (i-close (acl2-cosine x) (acl2-cosine y))
	    
	    )
    ))
 
 (defthm circle-der-continuous
   (implies 
    (and 
     (standardp x)
     (realp x)
     (realp y)
     (i-close x y)
     )
    (i-close (circle-der x) (circle-der y))
    )
   :hints (("Goal"
	    :use (
		  (:instance rad-det)
		  (:instance lemma-6 (x x) (y y) )
		  (:instance lemma-5 (x x) (y y) )
		  (:instance i-small-plus-lemma (x (- (acl2-sine x))) (y (- (acl2-sine y))))
		  (:instance i-small-plus-lemma (x (acl2-cosine x)) (y (acl2-cosine y)))
		  (:instance limited*small->small (y (- (acl2-cosine x) (acl2-cosine y))) (x #c(0 1)))
		  (:instance i-small-plus 
			     (x (- (- (acl2-sine x)) (- (acl2-sine y)))) 
			     (y (* #c(0 1) (- (acl2-cosine x) (acl2-cosine y))))
			     )
		  (:instance lemma-3 
			     (a (- (acl2-sine x))) 
			     (b (- (acl2-sine y))) 
			     (c #c(0 1)) 
			     (d (acl2-cosine x)) 
			     (e (acl2-cosine y))
			     )
		  (:instance i-close-plus-lemma-2
			     (x (+ (- (acl2-sine x)) (* #c(0 1) (acl2-cosine x))))
			     (y (+ (- (acl2-sine y)) (* #c(0 1) (acl2-cosine y))))
			     )
		  (:instance close-limited 
			     (x (+ (- (acl2-sine x)) (* #c(0 1) (acl2-cosine x))))
			     (y (+ (- (acl2-sine y)) (* #c(0 1) (acl2-cosine y))))
			     (z (rad))
			     )
		  (:instance circle-der-equal(x x))
		  (:instance circle-der-equal(x y))
		  )
	    :in-theory (disable circle circle-der)
	    )
	   )
   
   )
 
 (defthm f-acl2num
   (implies (acl2-numberp x)
	    (acl2-numberp (circle x))
	    )
   )
 )

(defun rf(x) 
  (realpart (circle x)) 
  )

(defun imf(x) 
  (imagpart (circle x))
  )


(defun rcircle-derivative (x)
  (realpart (circle-der x))
  )

(defun icircle-derivative (x)
  (imagpart (circle-der x))
  )

(defun rcircle-der-sqr(x)
  (square (rcircle-derivative x) )
  )

(defun icircle-der-sqr(x)
  (square (icircle-derivative x) )
  )

(defun circle-der-sqr-sum(x)
  (+ (rcircle-der-sqr x) (icircle-der-sqr x))
  )


(defun circle-der-sum-sqrt(x)
  (acl2-sqrt (circle-der-sqr-sum x))
  )

(defun circle-domain () (interval nil nil))

(defun map-circle-der-sum-sqrt (p)
  (if (consp p)
      (cons (circle-der-sum-sqrt (car p))
	    (map-circle-der-sum-sqrt (cdr p)))
    nil))

(defun riemann-circle-der-sum-sqrt (p)
  (dotprod (deltas p)
           (map-circle-der-sum-sqrt (cdr p)))
  )

(defthm circle-domain-real
  (implies (inside-interval-p x (circle-domain))
	   (realp x))
  )

(defthm circle-domain-non-trivial
  (or (null (interval-left-endpoint (circle-domain)))
      (null (interval-right-endpoint (circle-domain)))
      (< (interval-left-endpoint (circle-domain))
	 (interval-right-endpoint (circle-domain))))
  :rule-classes nil)

(defthm intervalp-circle-der-sqrt-domain
  (interval-p (circle-domain))
  )

(encapsulate
 ()
 (local (include-book "nonstd/nsa/inverse-trig" :dir :system))
 
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

 (defthm circle-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (circle-domain))
		 (inside-interval-p y1 (circle-domain))
		 (inside-interval-p y2 (circle-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (circle x) (circle y1)) (- x y1)))
		 (i-close (/ (- (circle x) (circle y1)) (- x y1))
			  (/ (- (circle x) (circle y2)) (- x y2)))))
   :hints (("Goal"
	    :use ((:instance circle-der-lemma (x x) (y y1))
		  (:instance circle-der-lemma (x x) (y y2))
		  (:instance circle-domain-real)
		  (:instance cosine-bound)
		  (:instance sine-bound)
		  (:instance limited-squeeze (a -1) (x (acl2-cosine x)) (b 1))
		  (:instance limited-squeeze (a -1) (x (acl2-sine x)) (b 1))
		  (:instance limited-not-small-i)
		  (:instance i-limited-plus (x (- (* (RAD) (ACL2-SINE X)))) (y (* (RAD) (ACL2-COSINE X))))
		  (:instance i-limited-times (x #c(0 1)) (y (* (RAD) (ACL2-COSINE X))))
		  (:instance i-limited-times (x (ACL2-COSINE X)) (y (RAD)))
		  (:instance i-limited-times (x (- (ACL2-SINE X))) (y (RAD)))
		  (:instance rad-det)
		  (:instance circle-equal)
		  (:instance i-close-limited (x (circle-der x)) (y (/ (- (circle x) (circle y1)) (- x y1)))))
	    ))
   )
 )

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (i-small y)
		  (not (= y 0))
		  (i-limited (/ x y)))
	     (i-small x))
    :hints (("Goal"
	     :use ((:instance limited*large->large (y (/ y))))
	     :in-theory (disable limited*large->large)))))

 (defthm circle-continuous
   (implies (and (standardp x)
		 (inside-interval-p x (circle-domain))
		 (i-close x y)
		 (inside-interval-p y (circle-domain)))
	    (i-close (circle x) (circle y)))
   :hints (("Goal"
	    :use ((:instance circle-differentiable (y1 y) (y2 y))
		  (:instance lemma-1
			     (x (+ (circle x) (- (circle y))))
			     (y (+ x (- y)))))
	    :in-theory (enable-disable (i-close)
				       (circle-differentiable
					lemma-1)))))
 )


(defthm circle-der-sum-sqrt-cont
  (implies 
   (and (standardp x)
        (inside-interval-p x (circle-domain))
        (inside-interval-p y (circle-domain))
        (i-close x y)
        )
   (i-close
    (circle-der-sum-sqrt x) 
    (circle-der-sum-sqrt y)
    ))
  
  :hints (("Goal"
           :use (
                 (:functional-instance der-sum-sqrt-cont
				       (c-domain circle-domain)
				       (der-sum-sqrt circle-der-sum-sqrt)
				       (der-sqr-sum circle-der-sqr-sum)
				       (ic-der-sqr icircle-der-sqr)
				       (rc-der-sqr rcircle-der-sqr)
				       (ic-derivative icircle-derivative) 
				       (rc-derivative rcircle-derivative)
				       (c-derivative circle-der)
				       (c circle)
				       )
                 ))
          ("Subgoal 2" 
           :use (
                 (:instance circle-der-continuous (x x) (y y))
                 )
           )
          
          ("Subgoal 1" 
           :use (
                 (:instance circle-der-lemma (x x) (y y))
                 )
           )
          )
  )

(encapsulate
 ()
 
 (local 
  (defthm limited-riemann-circle-der-sum-sqrt-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (circle-domain))
		  (inside-interval-p b (circle-domain))
		  (< a b))
	     (i-limited (riemann-circle-der-sum-sqrt (make-small-partition a b))))
    
    :hints (("Goal"
	     :use (
		   (:functional-instance limited-riemann-der-sum-sqrt-small-partition
					 (riemann-der-sum-sqrt riemann-circle-der-sum-sqrt)
					 (map-der-sum-sqrt map-circle-der-sum-sqrt)
					 (c-domain circle-domain)
					 (der-sum-sqrt circle-der-sum-sqrt)
					 (der-sqr-sum circle-der-sqr-sum)
					 (ic-der-sqr icircle-der-sqr)
					 (rc-der-sqr rcircle-der-sqr)
					 (ic-derivative icircle-derivative) 
					 (rc-derivative rcircle-derivative)
					 (c-derivative circle-der)
					 (c circle)
					 )
		   )
	     ))
    ))
 
 (local (in-theory (disable riemann-circle-der-sum-sqrt)))
 
 (defun-std strict-int-circle-der-sum-sqrt (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (circle-domain))
	    (inside-interval-p b (circle-domain))
	    (< a b))
       (standard-part (riemann-circle-der-sum-sqrt (make-small-partition a b)))
     0))
 )

(defthm strict-int-circle-der-sum-sqrt-is-integral-of-der-sum-sqrt
  (implies (and (standardp a)
                (standardp b)
                (<= a b)
                (inside-interval-p a (circle-domain))
                (inside-interval-p b (circle-domain))
                (partitionp p)
                (equal (car p) a)
                (equal (car (last p)) b)
                (i-small (mesh p)))
           (i-close (riemann-circle-der-sum-sqrt p)
                    (strict-int-circle-der-sum-sqrt a b)))
  
  :hints (("Goal"
           :use (
                 (:functional-instance strict-int-der-sum-sqrt-is-integral-of-der-sum-sqrt
					 (riemann-der-sum-sqrt riemann-circle-der-sum-sqrt)
					 (map-der-sum-sqrt map-circle-der-sum-sqrt)
					 (c-domain circle-domain)
					 (der-sum-sqrt circle-der-sum-sqrt)
					 (der-sqr-sum circle-der-sqr-sum)
					 (ic-der-sqr icircle-der-sqr)
					 (rc-der-sqr rcircle-der-sqr)
					 (ic-derivative icircle-derivative) 
					 (rc-derivative rcircle-derivative)
					 (c-derivative circle-der)
					 (c circle)
					 (strict-int-der-sum-sqrt strict-int-circle-der-sum-sqrt)
				       )
                 )
           ))
  )

(defun f-len(x)
  (if (realp x)
      (* (rad) x)
    0)
  )

(defthm f-len-real
  (realp (f-len x))
  )

(defun int-circle-der-sum-sqrt (a b)
  (if (<= a b)
      (strict-int-circle-der-sum-sqrt a b)
    (- (strict-int-circle-der-sum-sqrt b a))))

(encapsulate
 ()
 
 (local (include-book "nonstd/nsa/ln" :dir :system))
 
 (local
  (defthm dis*-1
    (equal (+ (* a b c c) (* a b d d)) (* a b (+ (* c c) (* d d))))
    ))
 
 (local
  (defthm dis+-1
    (equal (+ (* a a) (* b b)) (+ (* b b) (* a a)))
    ))
 
 (local
  (defthm sin-cos-eq
    (EQUAL (* (RAD) (RAD))
	   (+ (* (RAD)
		 (RAD)
		 (ACL2-COSINE X)
		 (ACL2-COSINE X))
	      (* (RAD)
		 (RAD)
		 (ACL2-SINE X)
		 (ACL2-SINE X))))
    :hints (("Goal" 
	     :use(           
		  (:instance dis*-1 (a (rad)) (b (rad)) (c (acl2-cosine x)) (d (acl2-sine x)))
		  (:instance dis+-1 (a (ACL2-COSINE X)) (b (ACL2-SINE X)))
		  (:instance sin**2+cos**2(x x))
		  )
	     ))
    ))

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

   (defthm *-complex
     (implies (and (realp i) (realp j) (realp r) (realp s))
	      (equal (* (complex i j) (complex r s))
		     (complex (- (* i r) (* j s))
			      (+ (* i s) (* j r)))))))
  )
 
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

 (defthm circle-der-sum-sqrt-eq
   (implies (realp x)
	    (equal (circle-der-sum-sqrt x) (rad)))
   :hints (("Goal" 
	    :use(
		 (:instance rad-det)
		 (:instance sin-cos-eq (x x))
		 (:instance dis*-1 (a (rad)) (b (rad)) (c (acl2-cosine x)) (d (acl2-sine x)))
		 (:instance realpart-*-real (x (rad)) 
			    (y  (COMPLEX (- (ACL2-SINE X)) (ACL2-COSINE X))))
		 (:instance imagpart-*-real (x (rad)) 
			    (y  (COMPLEX (- (ACL2-SINE X)) (ACL2-COSINE X))))
		 (:instance sin**2+cos**2(x x))
		 )
	    :in-theory (disable acl2-sine acl2-cosine rad-det sin-cos-eq dis*-1 dis+-1)
	    ))
   )
 )

(encapsulate
 ()
 
 (local
  (defthm test-close-1
    (implies (acl2-numberp a) (i-close a a))
    ))
 
 (local
  (defthm dis-1
    (equal (- (* a b) (* a c)) (* a (- b c))
	   )
    )
  )
 
 (local
  (defthm div-test-2
    (implies (and (acl2-numberp a)
		  (acl2-numberp b)
		  (not (equal b 0))
		  )
	     (equal (/ (* a b) b) a)
	     )
    ))
 
 (local 
  (defthm not-eq-test
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (not (equal x y))
		  )
	     (not (equal (- x y) 0))
	     )
    ))
 
 (local
  (defthm circle-der-sum-sqrt-is-derivative-2
    (implies (and (standardp x)
		  (inside-interval-p x (circle-domain))
		  (inside-interval-p y (circle-domain))
		  (i-close x y) (not (= x y)))
	     (equal (/ (- (f-len x) (f-len y)) (- x y))
		    (rad)
		    ))
    
    :hints (("Goal" 
	     :use(
		  (:instance dis-1(a (rad)) (b x) (c y))
		  (:instance not-eq-test (x x) (y y))
		  (:instance rad-det)
		  (:instance div-test-2(a (rad)) (b (- x y)))
		  (:instance circle-der-sum-sqrt-eq(x x))
		  )
	     :in-theory (disable acl2-sine acl2-cosine ABS circle-der circle-der-SQR-SUM circle-der-SUM-SQRT circle-domain FIX
				 Icircle-der-SQR Icircle-derIVATIVE NOT REALFIX Rcircle-der-SQR Rcircle-derIVATIVE SQUARE
				 ASSOCIATIVITY-OF-* COMMUTATIVITY-2-OF-* DISTRIBUTIVITY FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
				 INVERSE-OF-* INVERSE-OF-+-AS=0 UNICITY-OF-1)
	     ))
    ))
 
 (defthm circle-der-sum-sqrt-is-derivative
   (implies (and (standardp x)
		 (inside-interval-p x (circle-domain))
		 (inside-interval-p y (circle-domain))
		 (i-close x y) (not (= x y)))
	    (i-close (/ (- (f-len x) (f-len y)) (- x y))
		     (circle-der-sum-sqrt x)
		     ))
   
   :hints (("Goal" 
	    :use(
		 (:instance circle-der-sum-sqrt-is-derivative-2(x x) (y y))
		 (:instance circle-der-sum-sqrt-eq(x x))
		 (:instance test-close-1 (a (rad)))
		 )
	    :in-theory (disable acl2-sine acl2-cosine ABS circle-der circle-der-SQR-SUM circle-der-SUM-SQRT circle-domain FIX
				Icircle-der-SQR Icircle-derIVATIVE NOT REALFIX Rcircle-der-SQR Rcircle-derIVATIVE SQUARE
				ASSOCIATIVITY-OF-* COMMUTATIVITY-2-OF-* DISTRIBUTIVITY FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
				INVERSE-OF-* INVERSE-OF-+-AS=0 UNICITY-OF-1)
	    ))
   )
 )

(include-book "nonstd/integrals/ftc-2" :dir :system)

(defthmd apply-ftc-2
  (implies (and (inside-interval-p a (circle-domain))
                (inside-interval-p b (circle-domain)))
           (equal (int-circle-der-sum-sqrt a b)
                  (- (f-len b)
                     (f-len a))))
  
  :hints (("Goal"
           :use (
                 (:functional-instance ftc-2
				       (rcdfn-domain circle-domain)
				       (int-rcdfn-prime int-circle-der-sum-sqrt)
				       (riemann-rcdfn-prime riemann-circle-der-sum-sqrt)
				       (map-rcdfn-prime map-circle-der-sum-sqrt)
				       (rcdfn-prime circle-der-sum-sqrt)
				       (rcdfn f-len)
				       
				       (STRICT-INT-RCDFN-PRIME STRICT-INT-circle-der-SUM-SQRT)
				       )
                 )
           :in-theory (disable circle-der-sum-sqrt)
           )
          ("Subgoal 7"
           :use(
                (:instance circle-der-sum-sqrt-cont(x x) (y x1))
                )
           
           :in-theory (disable circle-der-sum-sqrt)
           )
          ("Subgoal 6"
           :use(
                (:instance circle-der-sum-sqrt-is-derivative(x x) (y x1))
                )
           :in-theory (disable circle-der-sum-sqrt)
           )       
          )
  )

(encapsulate
 ()
 
 (local
  (defthm f-len-test-1
    (implies (realp x)
	     (equal (* 0 x) 0))
    ))
 
 (local
  (defthm f-len-test-2
    (implies (realp x)
	     (equal (* x 0) 0))
    ))
 
 (local
  (defthm f-len-test-3
    (implies (realp x)
	     (equal (f-len x) (* (rad) x))
	     )
    ))
 
 (local
  (defthm f-len-test-4
    (equal (f-len 0) 0)
    :hints (("Goal" 
	     :use(
		  (:instance f-len-test-3 (x 0))
		  (:instance f-len-test-2 (x (rad)))
		  (:instance rad-det)
		  )
	     :in-theory (disable f-len)
	     ))
    ))
 
 (local
  (defthm pi-test1
    (implies (and (realp x)
		  (<= 2 x)
		  (< x 4))
	     (and (<= 4 (* 2 x)) (< (* 2 x) 8))
	     )
    ))
 
 (local
  (defthm pi-test2
    (implies (and 
	      (inside-interval-p 4 (circle-domain))
	      (inside-interval-p 8 (circle-domain))
	      (realp x)
	      (<= 4 x)
	      (< x 8))
	     (inside-interval-p x (circle-domain))
	     )
    :hints (("Goal" 
	     :use(
		  (:instance inside-interval-p-squeeze(a 4) (b 8) (c x) (interval (circle-domain)))
		  )
	     :in-theory (enable interval)
	     ))
    ))
 
 (defthm circle-length
   (equal (int-circle-der-sum-sqrt 0 (* 2 (acl2-pi)))
	  (* 2 (rad) (acl2-pi)))   
   :hints (("Goal" 
	    :use(
		 (:instance pi-between-2-4)
		 (:instance pi-test1 (x (acl2-pi)))
		 (:instance pi-test2 (x (* 2 (acl2-pi))))
		 (:instance apply-ftc-2(a 0) (b (* 2 (acl2-pi))) )
		 (:instance f-len-test-4)
		 )
	    :in-theory (disable int-circle-der-sum-sqrt)
	    ))
   
   )
 )