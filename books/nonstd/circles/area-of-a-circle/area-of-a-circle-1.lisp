; Area of a Circle
; Application of Integration by Substitution
;
; Copyright (C) 2021 University of Wyoming
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/inequalities" :dir :system))
(include-book "nonstd/nsa/inverse-square" :dir :system)
(include-book "nonstd/nsa/inverse-trig" :dir :system)
(include-book "nonstd/integrals/u-substitution" :dir :system)

(encapsulate
 ((rad() t)
  (consta1 () t)
  )
 (local (defun rad() 1))
 (local (defun consta1() 1))

 (defthm rad-def
   (and (realp (rad))
	(> (rad) 0)
	(standardp (rad))
	)
   )

 (defthmd consta1-def
   (and (inside-interval-p (consta1) (interval 0 (rad)))
	(standardp (consta1))
	)
   :hints (("goal"
	    :in-theory (enable interval-definition-theory)
	    ))
   )
 )

(defun circle-x-domain() (interval 0 (rad)))

(defun sub-domain() (interval 0 (* 1/2 (acl2-pi))))

(defun circle (x)
  (acl2-sqrt (- (* (rad) (rad)) (* x x)))
  )

(defun sub-func (x)
  (if (inside-interval-p x (sub-domain))
      (* (rad) (acl2-sine x))
    0)
  )

(defun sub-func-prime (x)
  (if (inside-interval-p x (sub-domain))
      (* (rad) (acl2-cosine x))
    0)
  )


(defthm-std c-domain-standard
  (standardp (circle-x-domain))
  )

(defthm-std sub-domain-standard
  (standardp (sub-domain))
  )

(defthm-std circle-standard
  (implies (standardp x)
	   (standardp (circle x))))

(defthm-std sub-func-standard
  (implies (standardp x)
	   (standardp (sub-func x))))

(defthm-std sub-func-prime-standard
  (implies (standardp x)
	   (standardp (sub-func-prime x))))


(local
 (defthm c-domain-interval-lemma
   (implies (and (realp x)
		 (> x 0)
		 )
	    (< (- x) 0)
	    )
   )
 )

(defthm intervalp-c-domain
  (interval-p (circle-x-domain))
  :hints(("goal"
	  :use (:instance c-domain-interval-lemma
			  (x (rad)))
	  :in-theory (enable interval-definition-theory)
	  ))
  )

(defthm c-domain-real
  (implies (inside-interval-p x (circle-x-domain))
	   (realp x)))

(defthm c-domain-non-trivial
  (or (null (interval-left-endpoint (circle-x-domain)))
      (null (interval-right-endpoint (circle-x-domain)))
      (< (interval-left-endpoint (circle-x-domain))
	 (interval-right-endpoint (circle-x-domain))))
  )

(defthm intervalp-sub-domain
  (interval-p (sub-domain))
  :hints(("goal"
	  :use (:instance pi-between-2-4)
	  )))

(defthm sub-domain-real
  (implies (inside-interval-p x (sub-domain))
	   (realp x))
  )

(defthm sub-domain-non-trivial
  (or (null (interval-left-endpoint (sub-domain)))
      (null (interval-right-endpoint (sub-domain)))
      (< (interval-left-endpoint (sub-domain))
	 (interval-right-endpoint (sub-domain))))
  )

(local
 (defthm sine-bound
   (implies (realp x)
	    (and (<= -1 (acl2-sine x))
		 (<= (acl2-sine x) 1)))
   :hints (("goal"
	    :use ((:instance cosine-bound
			     (x (+ (* 1/2 (acl2-pi)) (- x))))
		  (:instance cos-pi/2-x (x x)))
	    :in-theory (disable cosine-bound cos-pi/2-x)))))

(local
 (defthm lemma-1
   (implies (and (realp y)
		 (realp x)
		 (realp z)
		 (>= x (rad))
		 (>= y z)
		 )
	    (>= (* x y) (* x z))
	    )
   )
 )

(local
 (defthm sub-func-range
   (implies (realp x)
	    (and (<= 0 (sub-func x))
		 (<= (sub-func x) (rad))))
   :hints (("goal"
	    :use ((:instance sine-bound)
		  (:instance  rad-def)
		  (:instance sine-positive-in-0-pi/2)
		  (:instance lemma-1
			     (x (rad))
			     (z (acl2-sine x))
			     (y 1))
		  (:instance sine-0)
		  )
	    )
	   ("subgoal 9"
	    :in-theory (enable interval-definition-theory)
	    )
	   ("subgoal 3"
	    :in-theory (enable interval-definition-theory)
	    )
	   )
   ))

(defthm circle-domain-in-domain-of-fi
  (implies (inside-interval-p x (sub-domain))
	   (inside-interval-p (sub-func x) (circle-x-domain)))
  :hints (("goal"
	   :use (
		 (:instance sub-func-range)
		 (:instance intervalp-c-domain)
		 (:instance c-domain-real)
		 )
	   :in-theory (enable interval-definition-theory)
	   ))
  )

(defthm circle-real
  (realp (circle x))
  )

(defthm sub-func-real
  (realp (sub-func x))
  )

(defthm sub-func-prime-real
  (realp (sub-func-prime x))
  )



(local
 (defthm lemma-7
   (implies (acl2-numberp x)
	    (equal (+ (standard-part x) (non-standard-part x)) x)
	    )
   :hints (("goal"
	    :in-theory (enable non-standard-part)
	    ))
   )
 )

(local
 (defthm lemma-8
   (implies (and
	     (i-limited x)
	     (i-limited y)
	     (realp x)
	     (realp y)
	     (= (standard-part x) (standard-part y)))
	    (i-small (- x y)))
   :hints (("goal"
	    :use ((:instance lemma-7 (x x))
		  (:instance lemma-7 (x y))
		  (:instance i-small-non-standard-part (x x))
		  (:instance i-small-non-standard-part (x y))
		  (:instance i-small-plus
			     (x (non-standard-part x))
			     (y (- (non-standard-part y))))
		  (:instance i-small-uminus (x (non-standard-part y)))
		  (:instance fix (x (non-standard-part y)))
		  (:instance i-small (x 0))
		  )
	    ))
   )
 )

(defthmd root-close-lemma
  (implies (and (realp y1)
		(realp y2)
		(not (= (standard-part y1) (standard-part y2)))
		)
	   (not (i-close y1 y2))
	   )
  :hints (("goal"
	   :in-theory (enable i-close i-small)
	   ))
  )

(defthmd root-close-lemma-1
  (implies (and (realp y1)
		(realp y2)
		(not (i-close y1 y2))
		)
	   (not (= (standard-part y1) (standard-part y2)))
	   )
  :hints (("goal"
	   :in-theory (enable i-close i-small)
	   ))
  )

(local
 (defthm ineq-lemma1
   (implies (and (realp x1)
		 (realp x2)
		 (>= x1 0)
		 (>= x2 0)
		 (> x1 x2)
		 )
	    (> (* x1 x1) (* x1 x2)))
   ))

; matt k. addition to speed up proofs:
(in-theory (disable sqrt-epsilon-delta))

(local
 (defthm ineq-lemma2
   (implies (and (realp x1)
		 (realp x2)
		 (>= x1 0)
		 (>= x2 0)
		 (< x2 x1)
		 )
	    (>= (* x1 x2) (* x2 x2)))
   ))

(local
 (defthm ineq-lemma3
   (implies (and (realp a)
		 (realp b)
		 (realp c)
		 (> a b)
		 (>= b c))
	    (> a c))
   ))


(local
 (defthm ineq-lemma4
   (implies (and (realp x1)
		 (realp x2)
		 (>= x1 0)
		 (>= x2 0)
		 (> x1 x2))
	    (> (* x1 x1) (* x2 x2)))

   :hints (("goal"

	    :use (
		  (:instance ineq-lemma1 (x1 x1) (x2 x2))
		  (:instance ineq-lemma2 (x1 x1) (x2 x2))
		  (:instance ineq-lemma3 (a (* x1 x1)) (b (* x1 x2)) (c (* x2 x2)))
		  )
	    :in-theory nil
	    ))
   ))

(local
 (defthm root-close-lemma-2
   (implies (and (realp y1)
		 (realp y2)
		 (i-limited y1)
		 (i-limited y2)
		 (>= y1 0)
		 (>= y2 0)
		 (not (i-close y1 y2)))
	    (not (= (* (standard-part y1) (standard-part y1)) (* (standard-part y2) (standard-part y2))))
	    )
   :hints (("goal"
	    :use (
		  (:instance root-close-lemma-1 (y1 y1) (y2 y2))
		  (:instance ineq-lemma4 (x1 (standard-part y1)) (x2 (standard-part y2)))
		  (:instance ineq-lemma4 (x1 (standard-part y2)) (x2 (standard-part y1)))
		  )
	    :in-theory nil
	    ))
   ))

(local
 (defthm square-is-standard
   (implies (and (i-limited y1)
		 (realp y1))
	    (equal (* (standard-part y1) (standard-part y1))
		   (standard-part (square y1))
		   ))

   ))

(local
 (defthm root-close-lemma-3
   (implies (and (realp y1)
		 (realp y2)
		 (i-limited y1)
		 (i-limited y2)
		 (>= y1 0)
		 (>= y2 0)
		 (not (i-close y1 y2))
		 )
	    (not (= (standard-part (square y1)) (standard-part (square y2)))))

   :hints (("goal"
	    :use (
		  (:instance root-close-lemma-2 (y1 y1) (y2 y2))
		  (:instance square-is-standard (y1 y1))
		  (:instance square-is-standard (y1 y2))
		  )
	    :in-theory nil
	    ))
   ))


(local
 (defthm sqr-real-lemma
   (implies (realp x)
	    (realp (square x)))
   ))


(local
 (defthm root-close-lemma-6
   (implies (and (realp y1)
		 (realp y2)
		 (i-limited y1)
		 (i-limited y2)
		 (>= y1 0)
		 (>= y2 0)
		 (not (i-close y1 y2))
		 )
	    (not (i-close (square y1) (square y2))))

   :hints (("goal"
	    :use (
		  (:instance root-close-lemma-3 (y1 y1) (y2 y2))
		  (:instance root-close-lemma (y1 (square y1)) (y2 (square y2)))
		  (:instance sqr-real-lemma (x y1))
		  (:instance sqr-real-lemma (x y2))
		  )
	    :in-theory nil
	    ))
   ))

(local
 (defthm sqrt-real-lemma
   (implies (realp x)
	    (realp (acl2-sqrt x)))
   ))

(local
 (defthm sqrt>=0-lemma
   (implies (and (i-limited x)
		 (realp x))
	    (>= (acl2-sqrt x) 0))
   ))

(local
 (defthm root-close-f
   (implies
    (and (standardp x1)
	 (realp x1)
	 (realp x2)
	 (>= x1 0)
	 (>= x2 0)
	 (i-close x1 x2)
	 )
    (i-close (acl2-sqrt x1) (acl2-sqrt x2))
    )
   :hints (("goal"
	    :use (
		  (:definition square)
		  (:instance standards-are-limited-forward (x x1))
		  (:instance i-close-limited-2 (y x1) (x x2))
		  (:instance sqrt-real-lemma (x x1))
		  (:instance sqrt-real-lemma (x x2))
		  (:instance limited-sqrt (x x1))
		  (:instance limited-sqrt (x x2))
		  (:instance sqrt>=0-lemma (x x1))
		  (:instance sqrt>=0-lemma (x x2))
		  (:instance root-close-lemma-6 (y1 (acl2-sqrt x1) ) (y2 (acl2-sqrt x2)))
		  )
	    ))


   ))

(local
 (defthm lemma-3
   (implies (and (i-limited x)
		 (i-close y1 y2))
	    (i-close (* x y1) (* x y2)))
   :hints (("goal"
	    :in-theory (enable i-close))
	   ("goal''"
	    :use ((:instance limited*small->small
			     (y (+ y1 (- y2)))))
	    :in-theory (disable limited*small->small)))))

(defthm sub-func-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
	   (i-close (sub-func-prime x)
		    (sub-func-prime x1)))

  :hints (("goal"
	   :use (
		 (:instance rad-def)
		 (:instance standards-are-limited-forward
			    (x (rad))
			    )
		 (:instance sine-continuous
			    (x x)
			    (y x1))
		 (:instance lemma-3
			    (x (rad))
			    (y1 (acl2-sine x))
			    (y2 (acl2-sine x1))
			    )
		 )
	   ))
  )

(local
 (defthm lemma-4
   (implies (i-close x y)
	    (i-small (- x y))
	    )
   :hints (("goal"
	    :in-theory (enable i-small i-close)
	    ))
   )
 )

(local
 (defthm lemma-5
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y))
		 )
	    (i-close x y)
	    )
   :hints (("goal"
	    :in-theory (enable i-small i-close)
	    ))
   )
 )

(encapsulate
 ()
 (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-minimal" :dir :system))

 (local
  (defthm-std acl2-exp-standard
    (implies (standardp x)
	     (standardp (acl2-exp x))))
  )

 (defthmd cosine-standard
   (implies (standardp x)
	    (standardp (acl2-cosine x)))
   :hints (("goal"
	    :use (:instance acl2-exp-standard)
	    :in-theory (enable acl2-cosine))))

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
   :hints (("goal" :use (:instance sin-eqn-deriv)
	    :in-theory (enable acl2-sine acl2-cosine))))

 (local
  (defderivative cos-eqn-deriv
    (/ (+ (acl2-exp (* #c(0 1) x))
	  (acl2-exp (* #c(0 -1) x)))
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
   :hints (("goal" :use (:instance cos-eqn-deriv)
	    :in-theory (enable acl2-sine acl2-cosine))))
 )

(defthm sub-func-prime-is-derivative
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(inside-interval-p x1 (sub-domain))
		(i-close x x1) (not (= x x1)))
	   (i-close (/ (- (sub-func x) (sub-func x1)) (- x x1))
		    (sub-func-prime x)))
  :hints (("goal"
	   :use (
		 (:instance rad-def)
		 (:instance standards-are-limited-forward
			    (x (rad)))
		 (:instance acl2-sine-derivative
			    (x x)
			    (y x1))
		 (:instance lemma-4
			    (x (/ (- (acl2-sine x) (acl2-sine x1)) (- x x1)))
			    (y (acl2-cosine x)))
		 (:instance limited*small->small
			    (x (rad))
			    (y (- (/ (- (acl2-sine x) (acl2-sine x1)) (- x x1)) (acl2-cosine x))))
		 (:instance lemma-5
			    (x (* (rad) (/ (- (acl2-sine x) (acl2-sine x1)) (- x x1))))
			    (y (* (rad) (acl2-cosine x))))
		 )
; matt k. addition to speed up proofs:
           :in-theory (disable ineq-lemma3)
	   ))
  )

(defthm sub-func-differentiable
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(inside-interval-p y1 (sub-domain))
		(inside-interval-p y2 (sub-domain))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2)))
	   (and (i-limited (/ (- (sub-func x) (sub-func y1)) (- x y1)))
		(i-close (/ (- (sub-func x) (sub-func y1)) (- x y1))
			 (/ (- (sub-func x) (sub-func y2)) (- x y2)))))
  :hints (("goal"
	   :use(
		(:definition sub-func-prime)
		(:instance sub-domain-real)
		(:instance rad-def)
		(:instance standards-are-limited-forward
			   (x (rad)))
		(:instance cosine-standard)
		(:instance realp-cosine)
		(:instance standards-are-limited-forward
			   (x (acl2-cosine x))
			   )
		(:instance i-limited-times
			   (x (rad))
			   (y (acl2-cosine x))
			   )
		(:instance sub-func-prime-is-derivative
			   (x x)
			   (x1 y1))
		(:instance i-close-limited
			   (x (* (rad) (acl2-cosine x)))
			   (y (/ (- (sub-func x) (sub-func y1)) (- x y1)))
			   )
		(:instance sub-func-prime-is-derivative
			   (x x)
			   (x1 y2))
		(:instance i-close-symmetric
			   (x (/ (- (sub-func x) (sub-func y1)) (- x y1)))
			   (y (sub-func-prime x))
		 	   )
		(:instance i-close-symmetric
			   (x (/ (- (sub-func x) (sub-func y2)) (- x y2)))
			   (y (sub-func-prime x))
		 	   )
		(:instance i-close-transitive
			   (x (/ (- (sub-func x) (sub-func y1)) (- x y1)))
			   (y (sub-func-prime x))
			   (z (/ (- (sub-func x) (sub-func y2)) (- x y2)))
			   )
		)
	   :in-theory nil
	   ))
  )

(local
 (defthm square-lemma-1
   (implies (and (realp x1)
		 (realp x2)
		 (<= 0 x1)
		 (< x1 x2))
	    (< (* x1 x1) (* x2 x2)))
   :hints (("goal"
	    :cases ((< 0 x1))))))

(local
 (defthm ineq-lemma-5
   (implies (and (realp x1)
		 (realp x2)
		 (> 0 x1)
		 (> 0 x2)
		 (> x1 x2))
	    (> (* x1 x2) (* x1 x1)))
   )
 )

(local
 (defthm ineq-lemma-6
   (implies (and (realp x1)
		 (realp x2)
		 (> 0 x1)
		 (> 0 x2)
		 (> x1 x2))
	    (> (* x2 x2) (* x1 x2)))
   )
 )

(local
 (defthm square-lemma-2
   (implies (and (realp x1)
		 (realp x2)
		 (> 0 x1)
		 (> x1 x2))
	    (> (* x2 x2) (* x1 x1)))
   :hints (("goal"
	    :use ((:instance ineq-lemma-5
			     (x1 x1)
			     (x2 x2))
		  (:instance ineq-lemma-6
			     (x1 x1)
			     (x2 x2))
		  (:instance ineq-lemma3 (a (* x2 x2)) (b (* x1 x2)) (c (* x1 x1)))
		  )
	    ))
   ))

(local
 (defthm square-lemma-3
   (implies (and (realp x)
		 (> x (- (rad)))
		 (< x (rad))
		 )
	    (< (* x x) (* (rad) (rad))))
   :hints (("goal"
	    :use ((:instance square-lemma-1
			     (x2 (rad))
			     (x1 x))
		  (:instance square-lemma-2
			     (x2 (-(rad)))
			     (x1 x))
		  )
	    ))
   )
 )

(local
 (defthm square-lemma-4
   (implies (and (realp x)
		 (or (= (- x)  (rad))
		     (= x  (rad)))
		 )
	    (= (* x x) (* (rad) (rad))))
   )
 )

(local
 (defthm square-lemma-6
   (implies (and (realp x)
		 (and  (>= x (- (rad)))
		       (<= x (rad))))
	    (equal (or (and  (> x (- (rad)))
			     (< x (rad)))
		       (= x (rad))
		       (= x (-(rad))))

		   (and  (>= x (- (rad)))
			 (<= x (rad)))))
   :hints (("goal"
	    :use ((:instance rad-def)
		  )))
   )
 )

(local
 (defthm square-lemma-7
   (implies (realp x)
	    (= (* x x) (* (- x) (- x)))
	    )
   )
 )

(local
 (defthm square-lemma-8
   (implies (and (realp x)
		 (>= x (- (rad)))
		 (<= x (rad)))
	    (<= (* x x) (* (rad) (rad)))
	    )
   :hints (("goal"
	    :use ((:instance rad-def)
		  (:instance square-lemma-6)
		  (:instance square-lemma-3)
		  (:instance square-lemma-4)
		  (:instance square-lemma-7 (x (rad)))
		  )
	    :in-theory nil
	    ))
   )
 )

(local
 (defthm c-domain-lemma
   (equal (interval-right-endpoint (circle-x-domain)) (rad))
   :hints (("goal"
	    :in-theory
	    (enable (interval-right-endpoint))
	    ))
   )
 )

(local
 (defthm c-domain-lemma-1
   (equal (interval-left-endpoint (circle-x-domain)) 0)
   :hints (("goal"
	    :in-theory
	    (enable (interval-left-endpoint))
	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-1
   (implies (inside-interval-p x (circle-x-domain))
	    (and (>= x 0)
		 (<= x (rad)))
	    )
   :hints (("goal"
	    :use (
		  (:definition circle-x-domain)
		  (:instance c-domain-lemma)
		  (:instance c-domain-lemma-1)
		  (:instance inside-interval-p
			     (x x)
			     (interval (circle-x-domain))
			     )
		  (:instance c-domain-real)
		  (:instance rad-def)
		  )
	    :in-theory nil
	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-2
   (implies (inside-interval-p x (circle-x-domain))
	    (<=  (* x x) (* (rad) (rad)))
	    )
   :hints (("goal"
	    :use (
		  (:instance square-lemma-8)
		  (:instance circle-continuous-lemma-1)
		  (:instance (:instance c-domain-real)
			     )
		  )
	    :in-theory nil
	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-3
   (implies (and (standard-numberp x)
		 (standard-numberp x1)
		 )
	    (standard-numberp (- (* x x) (* x1 x1))))
   )
 )

(local
 (defthm lemma-6
   (implies (realp x)
	    (equal (fix (- x)) (- x)))
   )
 )

(local
 (defthm circle-continuous-lemma-4
   (implies (and (realp x)
		 (realp y)
		 (i-close x y)
		 (realp z)
		 (standardp z)
		 (i-limited x))
	    (and (equal (- (standard-part z) (standard-part x)) (standard-part (- z x)))
		 (equal (- (standard-part z) (standard-part y)) (standard-part (- z y)))
		 (equal (standard-part (- z x)) (standard-part (- z y)))
		 )
	    )
   :hints (("goal"
	    :use (
		  (:instance lemma-6 (x x))
		  (:instance lemma-6 (x y))
		  (:instance fix(x z))
		  (:instance standard-part-of-plus (x z) (y (- x)))
		  (:instance standard-part-of-standardp (x z))
		  (:instance standard-part-of-uminus(x x))
		  (:instance standard-part-of-plus (x z) (y (- y)))
		  (:instance standard-part-of-standardp(x z))
		  (:instance standard-part-of-uminus(x y))
		  (:instance standard-part-of-standardp (x z))
		  (:instance standard-part-of-uminus (x x))
		  (:instance standard-part-of-uminus (x y))
		  (:instance fix(x x))
		  (:instance fix(x y))
		  (:instance close-x-y->same-standard-part
			     (x x)
			     (y y)
			     )
		  (:instance standard-part-of-uminus
			     (x x))
		  (:instance standard-part-of-uminus
			     (x y))
		  )
	    :in-theory nil
	    )
	   ("subgoal 2"
	    :use ((:instance standard-part-of-standardp (x z))
		  (:instance standard-part-of-uminus (x x))
		  (:instance standard-part-of-uminus (x y))
		  (:instance fix(x x))
		  )
	    )

	   ("subgoal 4"
	    :use (
		  (:instance close-x-y->same-standard-part
			     (x x)
			     (y y)
			     ))
	    )
	   )
   ))

(local
 (defthm i-close-plus-lemma-2
   (implies (and (acl2-numberp x)
		 (acl2-numberp y)
		 (i-small (- x y))
		 )
	    (i-close x y))

   :hints (("goal"
   	    :use (
   		  (:instance i-close (x x) (y y))
   		  )
	    :in-theory nil
   	    ))
   )
 )

(local
 (defthm circle-continuous-lemma-5
   (implies (and (realp x)
		 (realp y)
		 (i-close x y)
		 (realp z)
		 (i-limited z)
		 (i-limited x)
		 (i-limited y)
		 (standardp z))
	    (i-close (- z x) (- z y))
	    )
   :hints (("goal"
	    :use ((:instance circle-continuous-lemma-4)
		  (:instance lemma-8
			     (x (- z x))
			     (y (- z y))
			     )
		  (:instance i-limited-plus
			     (x z)
			     (y (- x)))
		  (:instance i-limited-plus
			     (x z)
			     (y (- y)))
		  (:instance i-large-uminus (x x))
		  (:instance i-large-uminus (x y))
		  (:instance i-close-plus-lemma-2
			     (x (- z x))
			     (y (- z y))
			     )
		  )
	    :in-theory nil
	    ))
   )
 )


(local
 (defthm circle-continuous-lemma-6
   (implies (and (standardp x)
		 (inside-interval-p x (circle-x-domain))
		 (i-close x x1)
		 (inside-interval-p x1 (circle-x-domain)))
	    (i-close (- (* (rad) (rad)) (* x x)) (- (* (rad) (rad)) (* x1 x1)))
	    )
   :hints (("goal"
	    :use (
		  (:instance c-domain-real (x x))
		  (:instance c-domain-real (x x1))
		  (:instance square-is-continuous
			     (x1 x)
			     (x2 x1))
		  (:instance rad-def)
		  (:instance standards-are-limited-forward (x x))
		  (:instance standards-are-limited-forward (x (rad)))
		  (:instance circle-continuous-lemma-5
			     (x (* x x))
			     (y (* x1 x1))
			     (z (* (rad) (rad)))
			     )
		  (:instance i-limited-times (x (rad))
			     (y (rad)))
		  (:instance i-limited-times (x x)
			     (y x))
		  (:instance i-limited-times (x x1)
			     (y x1))
		  (:instance i-close-limited
			     (x x)
			     (y x1)
			     )
		  (:instance standardp-times
			     (x (rad))
			     (y (rad)))
		  )
	    :in-theory nil
	    ))
   )
 )


(local
 (defthm lemma-9
   (implies (and
	     (acl2-numberp x)
	     (acl2-numberp y)
	     (standardp x)
	     (standardp y))
	    (standardp (+ x y))
	    )
   )
 )

(local
 (defthm lemma-10
   (implies (and
	     (acl2-numberp x)
	     (standardp x))
	    (standardp (- x))
	    )
   )
 )

(local
 (defthm lemma-11
   (implies (realp x)
	    (equal (realfix x) x)
	    )
   )
 )

(defthm circle-continuous
  (implies (and (standardp x)
		(inside-interval-p x (circle-x-domain))
		(i-close x x1)
		(inside-interval-p x1 (circle-x-domain)))
	   (i-close (circle x)
		    (circle x1)))
  :hints (("goal"
	   :use (
		 (:instance square (x (rad)))
		 (:instance square (x x))
		 (:instance square (x x1))
		 (:instance circle (x x))
		 (:instance circle (x x1))
		 (:instance circle-continuous-lemma-2 (x x))
		 (:instance circle-continuous-lemma-2 (x x1))
		 (:instance root-close-f (x1 (- (* (rad) (rad)) (* x x)))
			    (x2 (- (* (rad) (rad)) (* x1 x1))))
		 (:instance rad-def)
		 (:instance c-domain-real (x x))
		 (:instance c-domain-real (x x1))
		 (:instance circle-continuous-lemma-6)
		 (:instance standardp-times
			    (x (rad))
			    (y (rad)))
		 (:instance standardp-times
			    (x x)
			    (y x))
		 (:instance standard-part-of-plus
			    (x (* (rad) (rad)))
			    (y (- (* x x)))
			    )
		 (:instance lemma-6 (x (* x x)))
		 (:instance standard-part-of-plus
			    (x (* (rad) (rad)))
			    (y (- (* x1 x1)))
			    )
		 (:instance lemma-6 (x (* x1 x1)))
		 (:instance fix (x (* (rad) (rad))))
		 (:instance standardp-standard-part
			    (x (* (rad) (rad))))
		 (:instance standardp-standard-part
			    (x (* x x)))
		 (:instance standardp-standard-part
			    (x (+ (* (rad) (rad)) (- (* x x)))))
		 (:instance standards-are-limited-forward (x x))
		 (:instance standards-are-limited-forward (x (rad)))
		 (:instance i-limited-times
			    (x (rad))
			    (y (rad)))
		 (:instance i-limited-times
			    (x x)
			    (y x))
		 (:instance i-limited-plus
			    (x (* (rad) (rad)))
			    (y (- (* x x))))
		 (:instance i-large-uminus
			    (x (* x x)))
		 (:instance lemma-9
			    (x (* (rad) (rad)))
			    (y (- (* x x)))
			    )
		 (:instance lemma-10
			    (x (* x x))
			    )
		 (:instance realp-*
			    (x x)
			    (y x)
			    )
		 (:instance realp-*
			    (x (rad))
			    (y (rad))
			    )
		 (:instance realp-*
			    (x x1)
			    (y x1)
			    )
		 (:instance lemma-11 (x (* x x)))
		 (:instance lemma-11 (x (* x1 x1)))
		 (:instance lemma-11 (x (* (rad) (rad))))
		 )
	   :in-theory nil
	   ))
  )

(encapsulate
 (((circle-sub-derivative *) => *))

 (local
  (defun circle-sub-derivative (x)
    (* (circle (sub-func x)) (sub-func-prime x))
    ))

 (defthm derivative-circle-sub-definition
   (implies (inside-interval-p x (sub-domain))
	    (equal (circle-sub-derivative x)
		   (* (circle (sub-func x))
		      (sub-func-prime x))))
   :hints (("goal"
	    :use (:functional-instance derivative-cr-f-o-fi-definition
				       (fi-domain sub-domain)
				       (f-prime circle)
				       (fi sub-func)
				       (fi-prime sub-func-prime)
				       (fi-range circle-x-domain)
				       (derivative-cr-f-o-fi circle-sub-derivative)
				       (consta consta1)
				       )
	    )
	   ("subgoal 10"
	    :use (:instance circle-domain-in-domain-of-fi)
	    )
	   ("subgoal 9"
	    :use (:instance intervalp-sub-domain)
	    )
	   ("subgoal 8"
	    :use (:instance sub-func-differentiable)
	    )
	   ("subgoal 7"
	    :use (:instance intervalp-c-domain)
	    )
	   ("subgoal 6"
	    :use (:instance sub-func-prime-continuous)
	    )
	   ("subgoal 5"
	    :use (:instance sub-func-prime-is-derivative)
	    )
	   ("subgoal 4"
	    :use (:instance circle-continuous)
	    )
	   ("subgoal 3"
	    :use (:instance consta1-def)
	    )
	   ("subgoal 2"
	    :use (:instance consta1-def)
	    )
	   ("subgoal 1"
	    :use (:instance circle-sub-derivative(x x))
	    )
	   )
   )
 )

(defun circle-sub-prime (x)
  (if (inside-interval-p x (sub-domain))
      (circle-sub-derivative x)
    0)
  )

(defun map-circle-sub-prime (p)
  (if (consp p)
      (cons (circle-sub-prime (car p))
	    (map-circle-sub-prime (cdr p)))
    nil))

(defun riemann-circle-sub-prime (p)
  (dotprod (deltas p)
	   (map-circle-sub-prime (cdr p))))

(encapsulate
 nil

 (local
  (defthm limited-riemann-circle-sub-prime-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (sub-domain))
		  (inside-interval-p b (sub-domain))
		  (< a b))
	     (standardp (standard-part (riemann-circle-sub-prime (make-small-partition a b)))))
    :hints (("goal"
 	     :use (:functional-instance limited-riemann-f-o-fi-prime-small-partition
					(fi-domain sub-domain)
					(f-o-fi-prime circle-sub-prime)
					(map-f-o-fi-prime map-circle-sub-prime)
					(riemann-f-o-fi-prime riemann-circle-sub-prime)
					(derivative-cr-f-o-fi circle-sub-derivative)
					(fi-range circle-x-domain)
					(consta  consta1)
					(f-prime circle)
					(fi sub-func)
					(fi-prime sub-func-prime)
					))
	    ("goal"
	     :use (
		   (:instance riemann-circle-sub-prime)
		   (:instance map-circle-sub-prime)
		   (:instance circle-sub-prime)
		   (:instance derivative-circle-sub-definition)
		   (:instance sub-domain)
		   (:instance circle-domain-in-domain-of-fi)
		   (:instance intervalp-sub-domain)
		   (:instance sub-func-differentiable)
		   (:instance intervalp-c-domain)
		   (:instance sub-func-prime-continuous)
		   (:instance sub-func-prime-is-derivative)
		   (:instance circle-continuous)
		   (:instance consta1-def)
		   )
	     )

 	    ("subgoal 13"
 	     :use (:instance riemann-circle-sub-prime)
 	     :in-theory (enable dotprod)
 	     )
 	    ("subgoal 12"
 	     :use (:instance map-circle-sub-prime)
 	     )
 	    ("subgoal 11"
 	     :use (:instance circle-sub-prime)
 	     )
 	    ("subgoal 10"
 	     :use ((:instance derivative-circle-sub-definition)
 	    	   (:instance sub-domain)
 	    	   )
 	     )
 	    ("subgoal 9"
 	     :use (:instance circle-domain-in-domain-of-fi)
 	     )
 	    ("subgoal 8"
 	     :use (:instance intervalp-sub-domain)
 	     )
 	    ("subgoal 7"
 	     :use (:instance sub-func-differentiable)
 	     )
 	    ("subgoal 6"
 	     :use (:instance intervalp-c-domain)
 	     )
 	    ("subgoal 5"
 	     :use (:instance sub-func-prime-continuous)
 	     )
 	    ("subgoal 4"
 	     :use (:instance sub-func-prime-is-derivative)
 	     )
 	    ("subgoal 3"
 	     :use (:instance circle-continuous)
 	     )
 	    ("subgoal 2"
 	     :use (:instance consta1-def)
 	     )
 	    ("subgoal 1"
 	     :use (:instance consta1-def)
 	     )
 	    )))

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-circle-sub-prime-small-partition nsa-theory)))

 (defun-std strict-int-circle-sub-prime (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (sub-domain))
	    (inside-interval-p b (sub-domain))
	    (< a b))
       (standard-part (riemann-circle-sub-prime (make-small-partition a b)))
     0))

 (defthm strict-int-circle-sub-prime-lemma
   (implies
    (and (standardp a) (standardp b))
    (equal
     (strict-int-circle-sub-prime a b)
     (if (and (realp a)
 	      (realp b)
	      (inside-interval-p a (sub-domain))
	      (inside-interval-p b (sub-domain))
 	      (< a b))
 	 (standard-part (riemann-circle-sub-prime (make-small-partition a b)))
 	 0)))
   )
 )

(defun int-circle-sub-prime (a b)
  (if (<= a b)
      (strict-int-circle-sub-prime a b)
    (- (strict-int-circle-sub-prime b a))))

(defun map-circle (p)
  (if (consp p)
      (cons (circle (car p))
	    (map-circle (cdr p)))
    nil))

(defun riemann-circle (p)
  (dotprod (deltas p)
	   (map-circle (cdr p))))


(encapsulate
 nil

 (local
  (defthmd limited-riemann-circle-small-partition
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (circle-x-domain))
		  (inside-interval-p b (circle-x-domain))
		  (< a b))
	     (standardp (standard-part (riemann-circle (make-small-partition a b)))))
    :hints (("goal"
	     :use (:functional-instance limited-riemann-f-prime-small-partition
					(fi-range circle-x-domain)
					(f-prime circle)
					(map-f-prime map-circle)
					(riemann-f-prime riemann-circle)
					(fi-domain sub-domain)
					(fi sub-func)
					(fi-prime sub-func-prime)
					(consta consta1))
	     )
	    ("subgoal 2"
 	     :use (:instance riemann-circle)
 	     )
	    ("subgoal 1"
 	     :use (:instance  map-circle)
 	     )

	    )
    )
  )

 (local (in-theory nil))
 (local (in-theory (enable limited-riemann-circle-small-partition nsa-theory)))

 (defun-std strict-int-circle (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (circle-x-domain))
	    (inside-interval-p b (circle-x-domain))
	    (< a b))
       (standard-part (riemann-circle (make-small-partition a b)))
     0))

 (defthm strict-int-circle-lemma
   (implies
    (and (standardp a) (standardp b))
    (equal (strict-int-circle a b)
	   (if (and (realp a)
		    (realp b)
		    (inside-interval-p a (circle-x-domain))
		    (inside-interval-p b (circle-x-domain))
		    (< a b))
	       (standard-part (riemann-circle (make-small-partition a b)))
	       0)))
   )
 )

(defun int-circle (a b)
  (if (<= a b)
      (strict-int-circle a b)
    (- (strict-int-circle b a))))

(defthm usubstitution-circle
  (implies (and (inside-interval-p a (sub-domain))
		(inside-interval-p b (sub-domain)))
	   (equal (int-circle (sub-func a) (sub-func b))
		  (int-circle-sub-prime a b)))
  :hints (("goal"
	   :use (:functional-instance usubstitution-f-o-fi
				      (int-f-prime int-circle)
				      (int-f-o-fi-prime int-circle-sub-prime)
				      (fi-domain sub-domain)
				      (fi sub-func)
				      (fi-prime sub-func-prime)
				      (f-prime circle)
				      (consta consta1)
				      (fi-range circle-x-domain)
				      (strict-int-f-o-fi-prime strict-int-circle-sub-prime)
				      (strict-int-f-prime strict-int-circle)
				      (riemann-f-o-fi-prime riemann-circle-sub-prime)
				      (map-f-o-fi-prime map-circle-sub-prime)
				      (map-f-prime map-circle)
				      (riemann-f-prime riemann-circle)
				      (f-o-fi-prime circle-sub-prime)
				      (derivative-cr-f-o-fi circle-sub-derivative)
				      )
					;:in-theory nil
	   )
	  ("subgoal 4"
	   :use (:instance int-circle-sub-prime (a a) (b b))
	   )
	  ("subgoal 3"
	   :use (:instance strict-int-circle-sub-prime-lemma)
	   )
	  ("subgoal 2"
	   :use (:instance int-circle (a a) (b b))
	   )
	  ("subgoal 1"
	   :use (:instance strict-int-circle-lemma)
	   )
	  )
  )

(encapsulate
 nil
 (local (in-theory nil))
 (local (include-book "arithmetic-5/top" :dir :system))
 (local
  (defthm lemma-12
    (implies (acl2-numberp x)
	     (equal (- (* x x) (* (* x y) (* x y))) (* x x (+ 1 (-(* y y)))))
	     )
    ))

 (local
  (defthm lemma-13
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  )
	     (equal (* x x y y) (* (* x y) (* x y)))
	     )
    ))

 (local
  (defthm lemma-14
    (implies (and (realp x)
		  (>= x 0))
	     (= (abs x) x))
    :hints (("goal"
	     :use (:instance abs (x x))
	     :in-theory nil
	     ))

    ))

 (defthm circle-sub-prime-equals
   (implies (and (inside-interval-p x (sub-domain))
		 (>= (acl2-cosine x) 0))
	    (equal (circle-sub-prime x) (*  (* (rad) (acl2-cosine x)) (* (rad) (acl2-cosine x)))))
   :hints (("goal"
	    :use ((:instance circle-sub-prime)
		  (:instance derivative-circle-sub-definition)
		  (:instance sub-func-prime (x x))
		  (:instance sub-func (x x))
		  (:instance sub-domain-real)
		  (:instance rad-def)
		  (:instance sub-func-real)
		  (:instance sub-func-prime-real)
		  (:instance sqrt-*-x-x(x (* (rad) (acl2-cosine x))))
		  (:instance cos**2->1-sin**2)
		  (:instance circle (x (sub-func x)))
		  (:instance lemma-12
			     (x (rad))
			     (y (acl2-sine x)))
		  (:instance lemma-13
			     (x (rad))
			     (y (acl2-cosine x))
			     )
		  (:instance lemma-14
			     (x (* (rad) (acl2-cosine x)))
			     )
		  )
	    :in-theory nil

	    ))
   )
 )
