; A Mechanized Proof of the Curve Length of a Rectifiable Curve
;
; Copyright (C) 2021 University of Wyoming
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "nonstd/nsa/inverse-square" :dir :system)
(include-book "nonstd/nsa/intervals" :dir :system)
(include-book "nonstd/integrals/continuous-function" :dir :system)
(include-book "arithmetic/equalities" :dir :system)

(encapsulate
 ((c (x) t)
  (c-derivative (x) t)
  (c-domain() t))
 (local (include-book "arithmetic/top-with-meta" :dir :system))

 (local (defun c(x) x))
 (local (defun c-derivative (x) (declare (ignore x)) 1))
 (local (defun c-domain () (interval 0 1)))

 (defthm c-acl2numberp
   (implies (acl2-numberp x)
	    (acl2-numberp (c x)))
   )

 (defthm c-domain-non-trivial
   (or (null (interval-left-endpoint (c-domain)))
       (null (interval-right-endpoint (c-domain)))
       (< (interval-left-endpoint (c-domain))
	  (interval-right-endpoint (c-domain))))
   :rule-classes nil)

 (defthm intervalp-der-sqrt-domain
   (interval-p (c-domain))
   )
 
 (defthm c-der-lemma
   (implies (and (standardp x)
		 (inside-interval-p x (c-domain))
		 (inside-interval-p y (c-domain))
		 (i-close x y) 
		 (not (= x y))
		 )
	    (i-close (/ (- (c x) (c y)) (- x y)) (c-derivative x)))
   )

 (defthm c-der-continuous
   (implies 
    (and (standardp x)
	 (inside-interval-p x (c-domain))
	 (inside-interval-p y (c-domain))
	 (i-close x y)
	 )
    (i-close (c-derivative x) (c-derivative y)))
   )
 )

(defthm-std c-der-std
  (implies (standardp x)
           (standardp (c-derivative x))
           )
  )

(defthm c-domain-real
  (implies (inside-interval-p x (c-domain))
	   (realp x))
  )

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp a)
		  (i-close a b))
	     (acl2-numberp b))
    :hints (
	    ("Goal"
	     :in-theory (enable nsa-theory)
	     ))
    ))
 
 (local
  (defthm c-differentiable-lemma1
    (implies (and (standardp x)
		  (inside-interval-p x (c-domain))
		  (inside-interval-p y1 (c-domain))
		  (i-close x y1) (not (= x y1)))
	     (and (i-limited (/ (- (c x) (c y1)) (- x y1)))))
    :hints (("Goal"
	     :use ((:instance c-der-std)
		   (:instance standards-are-limited-forward (x (c-derivative x)))
		   (:instance c-der-lemma (x x) (y y1))
		   (:instance i-close-symmetric (x (/ (- (c x) (c y1)) (- x y1))) (y (c-derivative x)))
		   (:instance i-close-limited (x (c-derivative x)) (y (/ (- (c x) (c y1)) (- x y1))))
		   (:instance c-acl2numberp)
		   (:instance c-acl2numberp (x y1))
		   (:instance c-domain-real)
		   (:instance c-domain-real (x y1))
		   (:instance lemma-1 (a (/ (- (c x) (c y1)) (- x y1))) (b (c-derivative x))))
	     ))
    ))

 (local
  (defthm c-differentiable-lemma2
    (implies (and (standardp x)
		  (inside-interval-p x (c-domain))
		  (inside-interval-p y1 (c-domain))
		  (inside-interval-p y2 (c-domain))
		  (i-close x y1) (not (= x y1))
		  (i-close x y2) (not (= x y2)))
	     (i-close (/ (- (c x) (c y1)) (- x y1))
		      (/ (- (c x) (c y2)) (- x y2))))
    :hints (("Goal"
	     :use ((:instance c-der-lemma (x x) (y y1))
		   (:instance c-der-lemma (x x) (y y2))
		   (:instance i-close-reflexive (x (c-derivative x))))
	     ))
    ))
 
 (defthm c-differentiable
   (implies (and (standardp x)
		 (inside-interval-p x (c-domain))
		 (inside-interval-p y1 (c-domain))
		 (inside-interval-p y2 (c-domain))
		 (i-close x y1) (not (= x y1))
		 (i-close x y2) (not (= x y2)))
	    (and (i-limited (/ (- (c x) (c y1)) (- x y1)))
		 (i-close (/ (- (c x) (c y1)) (- x y1))
			  (/ (- (c x) (c y2)) (- x y2)))))
   :hints(("Goal"
	   :use ((:instance c-differentiable-lemma1)
		 (:instance c-differentiable-lemma2))
	   ))
   )
 )

(defun rc-derivative (x)
  (realpart (c-derivative x))
  )

(defun ic-derivative (x)
  (imagpart (c-derivative x))
  )

(defthmd re-im-close
  (implies (and
	    (acl2-numberp x)
	    (acl2-numberp y)
	    (i-close x y))
	   (and (i-close (realpart x) (realpart y))
		(i-close (imagpart x) (imagpart y))))
  :hints (("Goal"
	   :use ((:instance i-small (x (- x y)))
		 (:instance standard-part-of-plus (x x) (y (- y)))
		 (:instance fix (x x))
		 (:instance fix (x (- y)))
		 (:instance standard-part-of-uminus (x y))
		 (:instance inverse-of-+-as=0 (a (standard-part x)) (b (standard-part y)))
		 
		 (:instance realpart-imagpart-elim (x x))
		 (:instance realpart-imagpart-elim (x y))
		 (:instance standard-part-of-complex (x (realpart x)) (y (imagpart x)))
		 (:instance standard-part-of-complex (x (realpart y)) (y (imagpart y)))
		 (:instance complex-equal
			    (x1 (standard-part (realpart x)))
			    (y1 (standard-part (imagpart x)))
			    (x2 (standard-part (realpart y)))
			    (y2 (standard-part (imagpart y))))
		 )
	   :in-theory (enable nsa-theory)
	   ))	  
  )

(defthmd rc-ic-der-cont
  (implies (and (standardp x)
		(inside-interval-p x (c-domain))
		(inside-interval-p y (c-domain))
		(i-close x y))
	   (and (i-close (rc-derivative x) (rc-derivative y))
		(i-close (ic-derivative x) (ic-derivative y))))
  :hints (("Goal"
	   :use (
		 (:instance c-der-continuous (x x) (y y) )
		 (:instance re-im-close (x (c-derivative x)) (y (c-derivative y)))
		 )
	   :in-theory (enable nsa-theory)))
  )

(defun rc-der-sqr(x)
  (square (rc-derivative x))
  )

(defthmd real-std
  (implies (standardp x)
	   (standardp (realpart x))))

(defthmd rc-der-std
  (implies (standardp x)
	   (standardp (rc-derivative x)))
  
  :hints (("Goal"
	   :use (
		 (:instance c-der-std (x x))
		 (:instance real-std (x (c-derivative x)))
		 )
	   ))
  )

(defthmd rc-der-sqr-cont
  (implies (and (standardp x)
		(inside-interval-p x (c-domain))
		(inside-interval-p y (c-domain))
		(i-close x y))
	   (i-close (rc-der-sqr x) (rc-der-sqr y)))
  :hints (("Goal"
	   :use (
		 (:instance rc-der-std(x x))
		 (:instance rc-ic-der-cont(x x) (y y))
		 (:instance square-is-continuous (x1 (rc-derivative x)) (x2 (rc-derivative y)))
		 )
	   ))
  )

(defun ic-der-sqr(x)
  (square (ic-derivative x) )
  )

(defthmd im-std
  (implies (standardp x)
	   (standardp (imagpart x)))
  )

(defthmd ic-der-std
  (implies (standardp x)
	   (standardp (ic-derivative x)))
  
  :hints (("Goal"
	   :use (
		 (:instance c-der-std (x x))
		 (:instance im-std (x (c-derivative x)))
		 )
	   ))
  )

(defthmd ic-der-sqr-cont
  (implies (and (standardp x)
		(inside-interval-p x (c-domain))
		(inside-interval-p y (c-domain))
		(i-close x y))
	   (i-close (ic-der-sqr x) (ic-der-sqr y)))
  
  :hints (("Goal"
	   :use (
		 (:instance ic-der-std(x x))
		 (:instance rc-ic-der-cont(x x) (y y))
		 (:instance square-is-continuous (x1 (ic-derivative x)) (x2 (ic-derivative y)))
		 )
	   ))
  )

(defun der-sqr-sum(x)
  (+ (rc-der-sqr x) (ic-der-sqr x))
  )

(defthmd i-small-plus-lemma
  (implies (i-close x y)
	   (i-small (- x y)))
  :hints (("Goal"
	   :in-theory (enable i-close i-small)
	   ))
  )

(defthmd i-close-plus-lemma
  (implies (i-small (- x y))
	   (i-close (- x y) 0))
  :hints (("Goal"
	   :in-theory (enable i-close i-small)
	   ))
  )

(defthmd i-close-plus-lemma-1
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(i-close (- x y) 0))
	   (i-close x y)
	   )
  :hints (("Goal"
	   :in-theory (enable i-close i-small)
	   ))
  )


(defthmd i-close-plus-lemma-2
  (implies (and (acl2-numberp x)
		(acl2-numberp y)
		(i-small (- x y))
		)
	   (i-close x y))
  
  :hints (("Goal"
	   :use (
		 (:instance i-close-plus-lemma(x x) )
		 (:instance i-close-plus-lemma-1(x x))
		 )
	   ))
  )

(defthmd close-sum-lemma
  (implies (and (i-close x1 x2)
		(i-close y1 y2))
	   (i-close (+ x1 y1) (+ x2 y2)))
  
  :hints (("Goal"
	   :use (
		 (:instance i-small-plus-lemma (x x1) (y x2))
		 (:instance i-small-plus-lemma (x y1) (y y2))
		 (:instance i-small-plus (x (- x1 x2)) (y (- y1 y2)))
		 (:instance i-close-plus-lemma-2 (x (+ x1 y1)) (y (+ x2 y2)))
		 )
	   ))
  )

(defthm der-sqr-sum-cont
  (implies (and (standardp x)
		(inside-interval-p x (c-domain))
		(inside-interval-p y (c-domain))
                (i-close x y))
           (i-close (der-sqr-sum x) (der-sqr-sum y)))
  
  
  :hints (("Goal"
           :use (
                 (:instance ic-der-sqr-cont (x x) (y y))
                 (:instance rc-der-sqr-cont (x x) (y y))
                 (:instance close-sum-lemma (x1 (rc-der-sqr x)) (x2 (rc-der-sqr y))
			    (y1 (ic-der-sqr x)) (y2 (ic-der-sqr y)))
                 )
           ))
  )

(defun der-sum-sqrt(x)
  (acl2-sqrt (der-sqr-sum x))
  )


(encapsulate
 ()
 
 (local (include-book  "arithmetic/inequalities" :dir :system))
 
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
    
    :hints (("Goal"
	     
	     :use (
		   (:instance ineq-lemma1 (x1 x1) (x2 x2))
		   (:instance ineq-lemma2 (x1 x1) (x2 x2))
		   (:instance ineq-lemma3 (a (* x1 x1)) (b (* x1 x2)) (c (* x2 x2)))
		   )
	     ))
    ))

 (local 
  (defthm root-close-lemma-1
    (implies (and (realp y1)
		  (realp y2)
		  (>= y1 0)
		  (>= y2 0)
		  (not (i-close y1 y2))
		  )
	     (not (= (standard-part y1) (standard-part y2)))
	     )
    :hints (("Goal"
	     :in-theory (enable i-close i-small)
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
    :hints (("Goal"
	     :use (
		   (:instance root-close-lemma-1 (y1 y1) (y2 y2))
		   (:instance ineq-lemma4 (x1 (standard-part y1)) (x2 (standard-part y2)))
		   (:instance ineq-lemma4 (x1 (standard-part y2)) (x2 (standard-part y1)))
		   )
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
    
    :hints (("Goal"
	     :use (
		   (:instance root-close-lemma-2 (y1 y1) (y2 y2))
		   (:instance square-is-standard (y1 y1))
		   (:instance square-is-standard (y1 y2))
		   )
	     :in-theory (disable root-close-lemma-2 square-is-standard )
	     ))
    ))

 (local
  (defthm root-close-lemma
    (implies (and (realp y1)
		  (realp y2)
		  (not (= (standard-part y1) (standard-part y2)))
		  )
	     (not (i-close y1 y2))
	     )
    :hints (("Goal"
	     :in-theory (enable i-close i-small)
	     ))
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
    
    :hints (("Goal"         
	     :use (
		   (:instance root-close-lemma-3 (y1 y1) (y2 y2))
		   (:instance root-close-lemma (y1 (square y1)) (y2 (square y2)))
		   )
	     :in-theory (disable root-close-lemma root-close-lemma-3 square )
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
		  (realp x)
		  (>= x 0))
	     (>= (acl2-sqrt x) 0))
    ))
 
 (local 
  (defthm standard-limited-lemma
    (implies (and (standardp x)
		  (realp x)
		  )
	     (i-limited x))
    ))
 
 (local  
  (defthm close-limited-lemma
    (implies (and (standardp x1)
		  (realp x1)
		  (i-close x1 x2))
	     (i-limited x2))
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
    :hints (("Goal"
	     :use (
		   (:instance standard-limited-lemma (x x1))
		   (:instance close-limited-lemma (x1 x1) (x2 x2))
		   (:instance sqrt-real-lemma (x x1))
		   (:instance sqrt-real-lemma (x x2))
		   (:instance limited-sqrt (x x1))
		   (:instance limited-sqrt (x x2))
		   (:instance sqrt>=0-lemma (x x1))
		   (:instance sqrt>=0-lemma (x x2))
		   (:instance root-close-lemma-6 (y1 (acl2-sqrt x1) ) (y2 (acl2-sqrt x2)))
		   )
	     :in-theory (disable limited-sqrt acl2-sqrt)
	     ))
    ))
 
 
 (local
  (defthm rc-der-real
    (implies (realp x)
	     (realp (rc-derivative x))
	     )
    ))
 
 (local 
  (defthm ic-der-real
    (implies (realp x)
	     (realp (ic-derivative x))
	     )
    ))
 
 (local 
  (defthm der-sqr-sum-real
    (implies (realp x)
	     (realp (der-sqr-sum x)))
    
    :hints (("Goal"
	     :use(
		  (:instance rc-der-real (x x))
		  (:instance ic-der-real (x x))
		  )
	     :in-theory (disable rc-derivative ic-derivative)
	     ))
    ))
 
 (local
  (defthm der-sqr-sum>=0
    (implies (realp x)
	     (>= (der-sqr-sum x) 0))
    :hints (("Goal"
	     :in-theory (disable rc-derivative ic-derivative)
	     ))
    ))
 
 
 (defthm der-sqr-sum-standard
   (implies (standardp x)
	    (standardp (der-sqr-sum x))
	    )
   
   :hints (("Goal"
	    :use(
		 (:instance rc-der-std (x x))
		 (:instance ic-der-std (x x))
		 )
	    :in-theory (disable rc-derivative ic-derivative)
	    ))
   )
 
 (defthm der-sum-sqrt-cont
   (implies (and (standardp x)
		 (inside-interval-p x (c-domain))
		 (inside-interval-p y (c-domain))
		 (i-close x y)
		 )
	    (i-close (der-sum-sqrt x) 
		     (der-sum-sqrt y)
		     ))
   
   :hints (("Goal"
	    :use (
		  (:instance der-sqr-sum-standard(x x))
		  (:instance der-sqr-sum-real (x x)) 
		  (:instance der-sqr-sum-real (x y))
		  (:instance der-sqr-sum>=0 (x x))
		  (:instance der-sqr-sum>=0 (x y))
		  (:instance der-sqr-sum-cont (x x) (y y) )
		  (:instance root-close-f (x1 (der-sqr-sum x)) (x2 (der-sqr-sum y)))
		  )
	    :in-theory (disable der-sqr-sum ) 
	    ))
   )
 )



(defun map-der-sum-sqrt (p)
  (if (consp p)
      (cons (der-sum-sqrt (car p))
	    (map-der-sum-sqrt (cdr p)))
    nil))

(defun riemann-der-sum-sqrt (p)
  (dotprod (deltas p)
           (map-der-sum-sqrt (cdr p))))



(defthmd limited-riemann-der-sum-sqrt-small-partition
  (implies (and (realp a) (standardp a)
                (realp b) (standardp b)
                (inside-interval-p a (c-domain))
                (inside-interval-p b (c-domain))
                (< a b))
           (i-limited (riemann-der-sum-sqrt (make-small-partition a b))))
  
  :hints (("Goal"
           :use (
                 (:functional-instance limited-riemann-rcfn-small-partition
				       (rcfn-domain c-domain)
				       (riemann-rcfn riemann-der-sum-sqrt)
				       (map-rcfn map-der-sum-sqrt)
				       (rcfn der-sum-sqrt)
				       )
                 )
           )
	  ("Subgoal 1"
	   :use (:instance intervalp-der-sqrt-domain)
	   )
	  ("Subgoal 2"
           :use ((:instance c-domain-non-trivial))
           )
          ("Subgoal 3"
           :use ((:instance der-sum-sqrt-cont(x x) (y y)))
           ))
  )

(encapsulate
 ()
 
 (local (in-theory (disable riemann-der-sum-sqrt)))
 
 (local 
  (defthm limited-riemann-der-sum-sqrt-small-partition-1
    (implies (and (realp a) (standardp a)
		  (realp b) (standardp b)
		  (inside-interval-p a (c-domain))
		  (inside-interval-p b (c-domain))
		  (< a b))
	     (standardp( standard-part(riemann-der-sum-sqrt (make-small-partition a b)))))
    
    :hints (("Goal"
	     :use (
		   (:instance limited-riemann-der-sum-sqrt-small-partition(a a) (b b) )
		   )
	     :in-theory (disable riemann-der-sum-sqrt)
	     ))
    ))
 
 (defun-std strict-int-der-sum-sqrt (a b)
   (if (and (realp a)
	    (realp b)
	    (inside-interval-p a (c-domain))
	    (inside-interval-p b (c-domain))
	    (< a b))
       (standard-part (riemann-der-sum-sqrt (make-small-partition a b)))
     0))
 )

(defthm strict-int-der-sum-sqrt-is-integral-of-der-sum-sqrt
  (implies (and (standardp a)
                (standardp b)
                (<= a b)
                (inside-interval-p a (c-domain))
                (inside-interval-p b (c-domain))
                (partitionp p)
                (equal (car p) a)
                (equal (car (last p)) b)
                (i-small (mesh p)))
           (i-close (riemann-der-sum-sqrt p)
                    (strict-int-der-sum-sqrt a b)))
  
  :hints (("Goal"
           :use (
                 (:functional-instance strict-int-rcfn-is-integral-of-rcfn
				       (rcfn-domain c-domain)
				       (riemann-rcfn riemann-der-sum-sqrt)
				       (strict-int-rcfn strict-int-der-sum-sqrt)
				       (map-rcfn map-der-sum-sqrt)
				       (rcfn der-sum-sqrt)
				       )
                 )
           ))
  )